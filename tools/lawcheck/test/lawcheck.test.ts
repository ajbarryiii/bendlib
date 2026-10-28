// Every CLI test runs the real bend compiler on the fixtures; nothing is mocked.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { rewrite, splitEquation } from "../src/terms.ts";
import { parseTy, showTy } from "../src/types.ts";
import { importablePath, predictTooLarge } from "../src/lawcheck.ts";
import { evaluate, TIMEOUT_BUDGET, type Engine } from "../src/checker.ts";
import { mulberry32, render, Universe, Unsupported } from "../src/values.ts";

const CLI = path.join(import.meta.dir, "..", "cli.ts");
const FX = path.join(import.meta.dir, "fixtures");
const T = 180_000;

async function run(...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

async function runEnv(env: Record<string, string>, ...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe", env: { ...process.env, ...env } });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

async function json(...args: string[]) {
  const r = await run(...args, "--json");
  if (r.stderr !== "") throw new Error(r.stderr);
  return { code: r.code, report: JSON.parse(r.stdout) as any };
}

const law = (report: any, name: string) => {
  const l = report.laws.find((x: any) => x.name === name);
  if (!l) throw new Error(`no law ${name} in report`);
  return l;
};
/** Evaluated, premise-false, too-large and timed-out instances partition the generated ones. */
const addsUp = (l: any) => expect([l.name, l.instances + (l.tooLarge ?? 0) + (l.timedOut ?? 0) + (l.premiseFalse ?? 0)]).toEqual([l.name, l.generated]);
const binds = (l: any) => Object.fromEntries(l.counterexample.bindings.map((b: any) => [b.name, b.value]));

// One `correct.bend` run, shared by the two tests that assert on a clean module.
let correctRun: Promise<{ code: number; report: any }> | null = null;
const correct = () => (correctRun ??= json(path.join(FX, "correct.bend")));

describe("correct implementation", () => {
  test("all four laws pass, exit 0", async () => {
    const { code, report } = await correct();
    expect(code).toBe(0);
    expect(report.laws.map((l: any) => [l.name, l.status, l.claim])).toEqual([
      ["ins_sorted", "pass", "equation"],
      ["dbl_add", "pass", "equation"],
      ["app_size", "pass", "equation"],
      ["le_dbl", "pass", "predicate"],
    ]);
    for (const l of report.laws) expect(l.instances).toBeGreaterThan(0);
    for (const l of report.laws) addsUp(l);
    expect(law(report, "ins_sorted").premise.satisfied).toBeLessThan(law(report, "ins_sorted").premise.total);
  }, T);
});

describe("planted bugs", () => {
  test("each bug yields a minimal counterexample, exit 1", async () => {
    const { code, report } = await json(path.join(FX, "buggy.bend"));
    expect(code).toBe(1);
    expect(law(report, "ins_length").status).toBe("pass");
    const sorted = law(report, "ins_sorted");
    expect(sorted.status).toBe("fail");
    expect(binds(sorted)).toEqual({ x: "0n", xs: "[1n]" });
    expect(sorted.counterexample.lhs).toEqual({ term: "is_sorted(ins(0n, [1n]))", value: "False{}" });
    expect(sorted.counterexample.rhs).toEqual({ term: "True{}", value: "True{}" });
    const dbl = law(report, "dbl_add");
    expect(binds(dbl)).toEqual({ n: "2n" });
    expect(dbl.counterexample.lhs.value).toBe("3n");
    expect(dbl.counterexample.rhs.value).toBe("4n");
    expect([dbl.counterexample.expected, dbl.counterexample.observed]).toEqual(["3n", "4n"]);
    const app = law(report, "app_size");
    expect(binds(app)).toEqual({ xs: "Push{Blue{}, Bot{}}", ys: "Bot{}" });
    expect(app.counterexample.lhs.value).toBe("0n");
    expect(app.counterexample.rhs.value).toBe("1n");
  }, T);

  test("human output shows binders and both sides", async () => {
    const r = await run(path.join(FX, "buggy.bend"), "--law", "ins_sorted");
    expect(r.code).toBe(1);
    expect(r.stderr).toBe("");
    expect(r.stdout).toMatch(/✗ ins_sorted {2}counterexample \(shrunk/);
    expect(r.stdout).toMatch(/\n +x = 0n\n +xs = \[1n\]\n/);
    expect(r.stdout).toContain("lhs  is_sorted(ins(0n, [1n])) = False{}");
    expect(r.stdout).toContain("proves nothing about all inputs");
  }, T);

  test("shrinking reduces random Nat, list and datatype counterexamples", async () => {
    const dbl = law((await json(path.join(FX, "buggy.bend"), "--law", "dbl_add", "--size", "0", "--max-instances", "3", "--seed", "2")).report, "dbl_add");
    expect(dbl.counterexample.original).toEqual([{ name: "n", value: "3n" }]);
    expect(dbl.counterexample.shrinkSteps).toBeGreaterThan(0);
    expect(binds(dbl)).toEqual({ n: "2n" });
    const sorted = law((await json(path.join(FX, "buggy.bend"), "--law", "ins_sorted", "--size", "0", "--max-instances", "3", "--seed", "7")).report, "ins_sorted");
    expect(sorted.counterexample.original).toEqual([{ name: "x", value: "2n" }, { name: "xs", value: "[4n, 14n]" }]);
    expect(sorted.counterexample.shrinkSteps).toBeGreaterThan(0);
    expect(binds(sorted)).toEqual({ x: "0n", xs: "[1n]" });
    const app = law((await json(path.join(FX, "buggy.bend"), "--law", "app_size", "--size", "0", "--max-instances", "3", "--seed", "6")).report, "app_size");
    expect(app.counterexample.original).toEqual([{ name: "xs", value: "Push{Red{}, Push{Blue{}, Bot{}}}" }, { name: "ys", value: "Push{Green{}, Bot{}}" }]);
    expect(binds(app)).toEqual({ xs: "Push{Blue{}, Bot{}}", ys: "Bot{}" });
  }, T);
});

describe("claim kinds and skips", () => {
  test("template function binder is instantiated from the catalog", async () => {
    const { code, report } = await json(path.join(FX, "template.bend"));
    expect(code).toBe(0);
    expect(law(report, "twice_id").status).toBe("pass");
    expect(law(report, "add_zero").status).toBe("pass");
  }, T);

  test("template map laws: a true one passes, a false one fails on a non-identity f", async () => {
    const { code, report } = await json(path.join(FX, "templates_map.bend"), "--max-instances", "40");
    expect(code).toBe(1);
    expect(law(report, "length_map").status).toBe("pass");
    const bad = law(report, "map_id_bad");
    expect(bad.status).toBe("fail");
    const f = bad.counterexample.bindings.find((b: any) => b.name === "f");
    expect(f).toBeDefined();
    expect(f.value).not.toBe("(lc_x => lc_x)");
  }, T);

  test("two template function binders search the full catalog product (no false pass)", async () => {
    const { code, report } = await json(path.join(FX, "cat2.bend"), "--jobs", "4");
    expect(code).toBe(1);
    const two = law(report, "two_funs_bad");
    expect(two.status).toBe("fail");
    const f = two.counterexample.bindings.find((b: any) => b.name === "f");
    expect(f).toBeDefined();
    // The old lexicographic 8-combination cap only ever tried the first two `Nat -> Nat` entries
    // (identity and constant zero), so a counterexample needing a growing `f` was never found.
    expect(f.value).not.toBe("(lc_x => lc_x)");
    expect(f.value).not.toBe("(lc_x => 0n)");
    expect(two.counterexample.bindings.find((b: any) => b.name === "g")).toBeDefined();
    expect(law(report, "one_fun_bad").status).toBe("fail");
  }, T);

  test("predicates, refutations, premises, type parameters, unsupported binders", async () => {
    const { code, report } = await json(path.join(FX, "kinds.bend"));
    expect(code).toBe(1);
    const st = Object.fromEntries(report.laws.map((l: any) => [l.name, l.status]));
    expect(st).toEqual({
      le_half: "pass", half_le_bad: "fail", p_holds: "pass", lt_irrefl: "pass", add_ne_bad: "fail", le_trans: "pass",
      append_nil_r: "pass", reverse_id_bad: "fail", pair_swap: "pass", where_law: "pass", fn_binder: "skip", float_law: "skip",
    });
    expect(binds(law(report, "half_le_bad"))).toEqual({ n: "1n" });
    expect(law(report, "half_le_bad").counterexample.goal).toBe("{False{} == True{} : Bool}");
    expect(law(report, "p_holds").instances).toBeGreaterThan(0);
    expect(binds(law(report, "add_ne_bad"))).toEqual({ a: "0n", b: "0n" });
    expect(law(report, "lt_irrefl").premise.satisfied).toBe(0);
    const rev = law(report, "reverse_id_bad");
    expect(rev.counterexample.types).toEqual([{ name: "A", value: "U32" }]);
    expect(binds(rev)).toEqual({ xs: "[0, 1]" });
    expect(law(report, "where_law").premise.satisfied).toBeGreaterThan(0);
    expect(law(report, "fn_binder").reason).toMatch(/function-typed binder f/);
    expect(law(report, "float_law").reason).toMatch(/F32/);
  }, T);
});

describe("random Nat bound, list length, Type predicates, function equations", () => {
  test("random Nats reach --max-nat and random lists are long enough to break a length bound", async () => {
    const { code, report } = await json(path.join(FX, "adv.bend"), "--jobs", "4");
    expect(code).toBe(1);
    const lt = law(report, "lt_twelve");
    expect(lt.status).toBe("fail");
    // The planted bound is 12, so the random phase must have reached a Nat ≥ 12.
    expect(Number(binds(lt).n.replace("n", ""))).toBeGreaterThanOrEqual(12);
    const ls = law(report, "list_short");
    expect(ls.status).toBe("fail");
    // The planted bound is length 6, so the random list phase must have reached at least that.
    expect(ls.counterexample.bindings[0].value.split(", ").length).toBeGreaterThanOrEqual(6);
  }, T);

  test("--max-nat bounds random Nats (planted bound just above the limit does not break)", async () => {
    const { code, report } = await json(path.join(FX, "adv.bend"), "--law", "lt_twelve", "--max-nat", "11", "--jobs", "4");
    expect(code).toBe(0);
    const l = law(report, "lt_twelve");
    expect(l.status).toBe("pass");
    expect(l.tooLarge ?? 0).toBe(0);
  }, T);

  test("an equation between functions is skipped, never failed", async () => {
    const { code, report } = await json(path.join(FX, "adv.bend"), "--law", "fn_eq", "--jobs", "4");
    expect(code).toBe(0);
    const l = law(report, "fn_eq");
    expect(l.status).toBe("skip");
    expect(l.reason).toMatch(/equation between functions/);
  }, T);

  test("a Type-valued predicate is decided: Unit holds, Empty is a counterexample", async () => {
    const { code, report } = await json(path.join(FX, "pred_type.bend"), "--jobs", "4");
    expect(code).toBe(1);
    const l = law(report, "all_zero_bad");
    expect(l.status).toBe("fail");
    expect(binds(l)).toEqual({ n: "1n" });
    expect(l.counterexample.expected).toBe("Empty");
    expect(l.counterexample.observed).toBe("Unit");
    expect(l.counterexample.goal).toBe("Empty");
  }, T);

  test("a Type-valued predicate premise is satisfied in Unit and dropped in Empty", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-predpremise-"));
    const file = path.join(dir, "root.bend");
    fs.writeFileSync(file, [
      "import Base",
      "",
      "def IsZero(n: Nat) -> Type:",
      "  match n:",
      "    case 0n:",
      "      Unit",
      "    case 1n+p:",
      "      Empty",
      "",
      "law unit_premise:",
      "  for n: Nat",
      "  for h: IsZero(n)",
      "  {Nat.add(n, 0n) == n : Nat}",
      "",
    ].join("\n"));
    const { code, report } = await json(file, "--jobs", "4", "--max-instances", "20");
    expect(code).toBe(0);
    const l = law(report, "unit_premise");
    expect(l.status).toBe("pass");
    expect(l.premise.satisfied).toBeGreaterThan(0);
    expect(l.premise.satisfied).toBeLessThan(l.premise.total);
  }, T);

  test("a refutation whose every instance is too large is skipped, not passed", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-toolarge-"));
    const file = path.join(dir, "root.bend");
    fs.writeFileSync(file, [
      "import Base",
      "",
      "law all_too_large:",
      "  for n: Nat",
      "  for _: {Nat.pow(20n, 25n) == 0n : Nat}",
      "  Empty",
      "",
    ].join("\n"));
    const { code, report } = await json(file, "--jobs", "4", "--max-instances", "4");
    expect(code).toBe(0);
    const l = law(report, "all_too_large");
    expect(l.status).toBe("skip");
    expect(l.reason).toBe("every instance was too large to evaluate (the claim or its premises build unary Nats too large for the checker; lower --max-nat)");
    expect(l.tooLarge).toBeGreaterThan(0);
  }, T);
});

describe("a file inside BEND_LIB", () => {
  test("keeps its hub namespace, so its local import's types match (it saw root/list.Step)", async () => {
    const lib = fs.mkdtempSync(path.join("/tmp", "lawcheck-hublib-"));
    const pkg = path.join(lib, "0x0123456789abcdef0123456789abcdef");
    fs.cpSync(path.join(FX, "hub_pkg"), pkg, { recursive: true });
    const r = await runEnv({ BEND_LIB: lib }, path.join(pkg, "src", "main.bend"), "--json");
    expect(r.stderr).toBe("");
    expect(law(JSON.parse(r.stdout), "first_uncons").status).toBe("pass");
  }, T);
});

describe("Word(n) values", () => {
  const zeros32 = "WCon{False{}, ".repeat(32) + "WNil{}" + "}".repeat(32);
  let wordRun: Promise<{ code: number; report: any }> | null = null;
  const word = () => (wordRun ??= json(path.join(FX, "word.bend")));

  test("literal widths: small ones exhaustively, Word(32n) through U32{w}", async () => {
    const { code, report } = await word();
    expect(code).toBe(1);
    expect(law(report, "zero_to_nat").status).toBe("pass");
    const comm = law(report, "add_comm3");
    expect(comm.status).toBe("pass");
    expect(comm.instances).toBe(64);
    expect(law(report, "u32_not_not").status).toBe("pass");
    expect(law(report, "u32_not_not").instances).toBeGreaterThan(0);
    const inc = law(report, "u32_inc_bad");
    expect(inc.status).toBe("fail");
    expect(binds(inc)).toEqual({ w: zeros32 });
    expect([inc.counterexample.expected, inc.counterexample.observed]).toEqual(["1", "0"]);
  }, T);

  test("a width bound by an earlier Nat binder (plain, -n, +n) is generated, not skipped", async () => {
    const { report } = await word();
    for (const name of ["not_complement", "not_not", "add_exact"]) {
      const l = law(report, name);
      expect([name, l.status]).toEqual([name, "pass"]);
      expect(l.instances).toBeGreaterThan(0);
    }
    for (const l of report.laws) if (l.status === "pass") addsUp(l);
    expect(law(report, "add_exact").premise.satisfied).toBeGreaterThan(0);
    expect(law(report, "add_exact").premise.satisfied).toBeLessThan(law(report, "add_exact").premise.total);
  }, T);

  test("planted bugs over Word(n) shrink to a one-bit counterexample", async () => {
    const { report } = await word();
    const not = law(report, "not_to_nat_bad");
    expect(not.status).toBe("fail");
    expect(binds(not)).toEqual({ n: "1n", w: "WCon{False{}, WNil{}}" });
    expect([not.counterexample.expected, not.counterexample.observed]).toEqual(["1n", "0n"]);
    const add = law(report, "add_exact_bad");
    expect(add.status).toBe("fail");
    expect(binds(add)).toEqual({ n: "1n", a: "WCon{True{}, WNil{}}", b: "WCon{True{}, WNil{}}" });
    expect(add.counterexample.lhs.value).toBe("0n");
    expect(add.counterexample.rhs.value).toBe("2n");
  }, T);

  test("human output prints the Word counterexample", async () => {
    const r = await run(path.join(FX, "word.bend"), "--law", "not_to_nat_bad");
    expect(r.code).toBe(1);
    expect(r.stderr).toBe("");
    expect(r.stdout).toMatch(/\n +n = 1n\n +w = WCon\{False\{\}, WNil\{\}\}\n/);
    expect(r.stdout).toContain("lhs  Word.to_nat(1n, Word.not(1n, WCon{False{}, WNil{}})) = 1n");
  }, T);

  test("enumeration covers every word of a small width and the edges of a wide one; fit resizes", () => {
    const U = new Universe(new Map());
    const all3 = U.enumerate(parseTy("Word(3n)")!, 1).map((v) => render(v));
    expect(new Set(all3).size).toBe(8);
    expect(U.enumerate(parseTy("Word(32n)")!, 0).map((v) => render(v))).toEqual([zeros32, "WCon{True{}, ".repeat(32) + "WNil{}" + "}".repeat(32)]);
    expect(U.enumerate(parseTy("Word(32n)")!, 1).length).toBe(66);
    expect(() => U.check(parseTy("Word(n)")!)).toThrow(Unsupported);
    const w = { v: "word" as const, bits: [true, false, true] };
    expect(render(U.fit(parseTy("Word(2n)")!, w))).toBe("WCon{True{}, WCon{False{}, WNil{}}}");
    expect(U.shrink(w).map((v) => render(v))).toContain("WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}");
  });
});

describe("recursion through a list", () => {
  test("a rose tree is generated, with and without children, and shrinks (it overflowed the stack)", async () => {
    const { code, report } = await json(path.join(FX, "rose.bend"));
    expect(code).toBe(1);
    expect(law(report, "val_refl").status).toBe("pass");
    expect(binds(law(report, "val_zero"))).toEqual({ t: "Node{1n, []}" });
    expect(binds(law(report, "leaf"))).toEqual({ t: "Node{0n, [Node{0n, []}]}" });
  }, T);
});

describe("unsafe verdict", () => {
  test("a checker verdict that relies on unsafe code is not a clean pass", async () => {
    const { code, report } = await json(path.join(FX, "unsafe_pass.bend"), "--max-instances", "3");
    expect(code).toBe(0);
    const l = law(report, "zero_is_zero");
    expect(l.status).toBe("skip");
    expect(l.status).not.toBe("pass");
    expect(l.reason).toMatch(/unsafe or foreign code/);
  }, T);

  test("a clean module still reports pass", async () => {
    const { code, report } = await correct();
    expect(code).toBe(0);
    expect(report.laws.every((l: any) => l.status === "pass")).toBe(true);
  }, T);

  test("an open law alongside @unsafe is not a clean pass", async () => {
    const { code, report } = await json(path.join(FX, "unsafe_open.bend"), "--max-instances", "3", "--jobs", "4");
    expect(code).toBe(0);
    const l = law(report, "zero_is_zero");
    expect(l.status).toBe("skip");
    expect(l.status).not.toBe("pass");
    expect(l.reason).toMatch(/unsafe or foreign code/);
  }, T);
});

describe("where premises and exs witnesses", () => {
  test("where drops failing instances; a false where law fails; exs searches for a witness", async () => {
    const { code, report } = await json(path.join(FX, "where_exs.bend"), "--max-instances", "40", "--jobs", "4");
    expect(code).toBe(1);
    expect(report.laws.map((l: any) => [l.name, l.status])).toEqual([
      ["where_true", "pass"], ["where_false", "fail"], ["exs_found", "pass"], ["exs_missing", "skip"],
    ]);
    const wt = law(report, "where_true");
    expect(wt.premise.satisfied).toBeGreaterThan(0);
    expect(wt.premise.satisfied).toBeLessThan(wt.premise.total);
    expect(binds(law(report, "where_false"))).toEqual({ n: "0n", m: "0n" });
    expect(law(report, "exs_found").claim).toBe("witness");
    expect(law(report, "exs_missing").reason).toMatch(/^no witness found in \d+ candidates$/);
  }, T);
});

describe("too-large instances and --max-nat", () => {
  test("random U32s are mostly small, a few set the top bit; 4294967295 enters the enumeration at depth 3; shrinking reaches 0", () => {
    const U = new Universe(new Map());
    const ty = parseTy("U32")!;
    const r = mulberry32(7);
    const ns = Array.from({ length: 2000 }, () => (U.random(ty, 3, r) as { n: number }).n);
    expect(ns.every((n) => Number.isInteger(n) && n >= 0 && n <= 4294967295)).toBe(true);
    expect(ns.filter((n) => n <= 30).length).toBeGreaterThan(1500);
    expect(ns.filter((n) => n > 65536).length).toBeLessThan(200);
    expect(ns.filter((n) => n >= 2147483648).length).toBeGreaterThan(40);
    expect(ns).toContain(4294967295);
    expect(U.enumerate(ty, 2).map((v) => render(v))).toEqual(["0", "1", "2", "3"]);
    expect(U.enumerate(ty, 3).map((v) => render(v))).toEqual(["0", "1", "2", "3", "4294967295"]);
    expect(U.shrink({ v: "u32", n: 4294967295 }).map((v) => render(v))).toEqual(["0", "1", "2", "2147483647", "4294967294"]);
    let x = { v: "u32" as const, n: 4294967295 };
    for (let k = 0; k < 40 && x.n > 0; k++) {
      const c = U.shrink(x) as (typeof x)[];
      expect(c.map((y) => y.n)).toContain(0);
      x = c.find((y) => y.n === Math.floor(x.n / 2)) ?? c[0];
    }
    expect(x.n).toBe(0);
  });

  const u32Law = (lines: string[]) => {
    const file = path.join(fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-u32-")), "u32.bend");
    fs.writeFileSync(file, ["import Base", "", ...lines].join("\n") + "\n");
    return file;
  };

  test("a law's line adds up: evaluated, premises false and too large make up the generated instances", async () => {
    const file = u32Law(["law small_add_comm:", "  for a: U32", "  for b: U32", "  for h: {Nat.is_lt(U32.to_nat(a), 3n) == True{} : Bool}",
      "  {Nat.add(U32.to_nat(a), U32.to_nat(b)) == Nat.add(U32.to_nat(b), U32.to_nat(a)) : Nat}"]);
    const r = await run(file, "--max-instances", "40", "--mem-mb", "300", "--jobs", "4");
    expect(r.stderr).toBe("");
    expect(r.code).toBe(0);
    const m = /✓ small_add_comm +(\d+) instances, 0 failures \(sizes ≤ 3\), (\d+) with premises false, (\d+) too large to evaluate \((\d+) generated\)/.exec(r.stdout);
    expect(m).not.toBeNull();
    const [evaluated, premiseFalse, tooLarge, generated] = m!.slice(1).map(Number);
    expect(generated).toBe(40);
    expect(evaluated + premiseFalse + tooLarge).toBe(generated);
    expect(Math.min(evaluated, premiseFalse, tooLarge)).toBeGreaterThan(0);
  }, T);

  // par(n) is True in 2^n steps and little memory: from about n = 22 it outlasts a 3 s timeout.
  const PAR = ["def par(n: Nat) -> Bool:", "  match n:", "    case 0n:", "      True{}", "    case 1n++p:", "      Bool.and(par(p), par(p))", ""];

  // Only x = 3 hangs, so with --max-nat 3 the batch 0..3 times out and only its slow half stays undecided.
  test("timed-out instances get their own count on the law's line, are never passed, and fail only --strict", async () => {
    const file = u32Law([...PAR, "law par_true:", "  for x: Nat", "  {par(Bool.pick(Nat, Nat.is_eq(x, 3n), 40n, 0n)) == True{} : Bool}"]);
    const args = [file, "--max-instances", "10", "--max-nat", "3", "--timeout", "3000", "--jobs", "4", "--allow-skip", "u32.par_true"];
    const r = await run(...args);
    expect(r.stderr).toBe("");
    expect(r.code).toBe(0);
    const m = /✓ par_true +(\d+) instances, 0 failures \(sizes ≤ 3\), (\d+) timed out \((\d+) generated\)/.exec(r.stdout);
    expect(m).not.toBeNull();
    const [evaluated, timedOut, generated] = m!.slice(1).map(Number);
    expect([evaluated, timedOut, generated]).toEqual([3, 1, 4]);
    const s = await run(...args, "--strict");
    expect(s.stderr).toBe("");
    expect(s.code).toBe(1);
    expect(s.stdout).toContain("strict: par_true (1 timed out): timed-out instances fail --strict; raise --timeout");
  }, T);

  test("when every instance is too large and no binder is a plain Nat, the reason does not suggest --max-nat", async () => {
    const file = u32Law(["law all_too_large_u32:", "  for a: U32", "  for _: {Nat.pow(20n, 25n) == 0n : Nat}", "  Empty"]);
    const { code, report } = await json(file, "--jobs", "4", "--max-instances", "4");
    expect(code).toBe(0);
    const l = law(report, "all_too_large_u32");
    expect(l.status).toBe("skip");
    expect(l.reason).toBe("every instance was too large to evaluate (the claim or its premises build unary Nats too large for the checker)");
  }, T);

  test("overflowing instances are dropped, not errors; a small counterexample still fails", async () => {
    const { code, report } = await json(path.join(FX, "pow.bend"), "--max-instances", "40");
    expect(code).toBe(1);
    expect(law(report, "pow_add").status).toBe("pass");
    const wrong = law(report, "pow_add_wrong");
    expect(wrong.status).toBe("fail");
    expect(wrong.counterexample).toBeDefined();
  }, T);

  test("--max-nat bounds random Nats so nothing overflows", async () => {
    const { code, report } = await json(path.join(FX, "pow.bend"), "--law", "pow_add", "--max-nat", "3");
    expect(code).toBe(0);
    const l = law(report, "pow_add");
    expect(l.status).toBe("pass");
    expect(l.tooLarge ?? 0).toBe(0);
  }, T);

  test("predictTooLarge drops only Nat equations that the checker cannot normalize", () => {
    expect(predictTooLarge("{Nat.pow(30n, 5n) == Nat.mul(30n, Nat.pow(30n, 4n)) : Nat}")).toBe(true);
    expect(predictTooLarge("{Nat.pow(2n, 3n) == 8n : Nat}")).toBe(false);
    // A huge Nat subterm under a non-Nat claim is left to the checker (soundness guard).
    expect(predictTooLarge("{Nat.is_le(Nat.pow(30n, 5n), 0n) == True{} : Bool}")).toBe(false);
    expect(predictTooLarge("{Nat.add(two(), 0n) == 0n : Nat}")).toBe(false);
  });

  test("predictTooLarge sees a large subterm under a small result (the mul_pow instance that timed out)", () => {
    expect(predictTooLarge("{Nat.pow(Nat.mul(7n, 0n), 9n) == Nat.mul(Nat.pow(7n, 9n), Nat.pow(0n, 9n)) : Nat}")).toBe(true);
    expect(predictTooLarge("{Nat.pow(Nat.mul(2n, 0n), 3n) == Nat.mul(Nat.pow(2n, 3n), Nat.pow(0n, 3n)) : Nat}")).toBe(false);
  });

  test("predictTooLarge drops a comparison only when both sides are too large (the pow_le_pow_right instance that timed out)", () => {
    expect(predictTooLarge("{Nat.is_le(Nat.pow(1n+7n, 6n), Nat.pow(1n+7n, 14n)) == True{} : Bool}")).toBe(true);
    expect(predictTooLarge("{Nat.is_lt(Nat.pow(1n+7n, 6n), 5n) == True{} : Bool}")).toBe(false);
    expect(predictTooLarge("{Nat.is_le(Nat.pow(2n, 3n), Nat.pow(2n, 5n)) == True{} : Bool}")).toBe(false);
    expect(predictTooLarge("{Bool.not(Nat.is_le(Nat.pow(30n, 5n), Nat.pow(30n, 5n))) == False{} : Bool}")).toBe(false);
  });
});

describe("imports and --impl", () => {
  test("laws over an imported module print the user's alias", async () => {
    const { code, report } = await json(path.join(FX, "laws_lib.bend"));
    expect(code).toBe(1);
    expect(binds(law(report, "app_size"))).toEqual({ xs: "M.Push{0n, M.Bot{}}", ys: "M.Bot{}" });
    expect(law(report, "app_bot").counterexample.observed).toBe("M.Push{0n, M.Bot{}}");
  }, T);

  test("--impl swaps the implementation", async () => {
    const { code, report } = await json(path.join(FX, "laws_lib.bend"), "--impl", path.join(FX, "lib_ok.bend"));
    expect(code).toBe(0);
    expect(report.laws.map((l: any) => l.status)).toEqual(["pass", "pass"]);
  }, T);

  test("hash imports (a name@version spec and a direct 0x hash) resolve to a local 0x<hash> copy", async () => {
    const hash = "deadbeefdeadbeefdeadbeefdeadbeef";
    const lib = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-bendlib-"));
    fs.mkdirSync(path.join(lib, "names"), { recursive: true });
    fs.mkdirSync(path.join(lib, `0x${hash}`), { recursive: true });
    fs.writeFileSync(path.join(lib, "names", "lawcheck-testpkg@1.2.3.4"), `0x${hash}\n`);
    fs.writeFileSync(path.join(lib, `0x${hash}`, "lib.bend"), [
      "import Base",
      "",
      "type Color is Data:",
      "  Red{}",
      "  Green{}",
      "",
      "def pick(c: Color) -> Nat:",
      "  match c:",
      "    case Red{}:",
      "      0n",
      "    case Green{}:",
      "      1n",
      "",
    ].join("\n"));
    const writeRoot = (kind: string, importLine: string) => {
      const dir = fs.mkdtempSync(path.join(os.tmpdir(), `lawcheck-hashroot-${kind}-`));
      const file = path.join(dir, "root.bend");
      fs.writeFileSync(file, [
        "import Base",
        importLine,
        "",
        "law pick_le_one:",
        "  for c: H.Color",
        "  {Nat.is_le(H.pick(c), 1n) == True{} : Bool}",
        "",
        "law pick_bad:",
        "  for c: H.Color",
        "  {H.pick(c) == 0n : Nat}",
        "",
      ].join("\n"));
      return file;
    };
    const roots = [
      writeRoot("named", "import lawcheck-testpkg@1.2.3.4/lib.bend as H"),
      writeRoot("hash", `import 0x${hash}/lib.bend as H`),
    ];
    for (const root of roots) {
      const r = await runEnv({ BEND_LIB: lib }, root, "--native", "--jobs", "4", "--max-instances", "6", "--json");
      expect(r.stderr).toBe("");
      expect(r.code).toBe(1);
      const rep = JSON.parse(r.stdout);
      const ok = rep.laws.find((l: any) => l.name === "pick_le_one");
      expect(ok.status).toBe("pass");
      expect(ok.native.checked).toBeGreaterThan(0);
      expect(ok.native.disagreements).toEqual([]);
      const bad = rep.laws.find((l: any) => l.name === "pick_bad");
      expect(bad.status).toBe("fail");
      expect(bad.native.checked).toBeGreaterThan(0);
      expect(bad.native.disagreements).toEqual([]);
      expect(r.stdout).not.toContain(hash);
      expect(bad.counterexample.bindings).toEqual([{ name: "c", value: "H.Green{}" }]);
      expect(bad.counterexample.lhs.term).toBe("H.pick(H.Green{})");
    }
  }, T);

  test("nested hash imports (a name@version module importing another) resolve hermetically", async () => {
    const depHash = "feedfacefeedfacefeedfacefeedface";
    const kernelHash = "deadbeefdeadbeefdeadbeefdeadbeef";
    const lib = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-bendlib-"));
    fs.mkdirSync(path.join(lib, "names"), { recursive: true });
    fs.mkdirSync(path.join(lib, `0x${depHash}`), { recursive: true });
    fs.mkdirSync(path.join(lib, `0x${kernelHash}`), { recursive: true });
    fs.writeFileSync(path.join(lib, "names", "lawcheck-dep@2.0.0.0"), `0x${depHash}\n`);
    fs.writeFileSync(path.join(lib, "names", "lawcheck-kernel@1.2.3.4"), `0x${kernelHash}\n`);
    fs.writeFileSync(path.join(lib, `0x${depHash}`, "base.bend"), [
      "import Base",
      "",
      "type Color is Data:",
      "  Red{}",
      "  Green{}",
      "",
      "def pick(c: Color) -> Nat:",
      "  match c:",
      "    case Red{}:",
      "      0n",
      "    case Green{}:",
      "      1n",
      "",
    ].join("\n"));
    fs.writeFileSync(path.join(lib, `0x${kernelHash}`, "kernel.bend"), [
      "import Base",
      "import lawcheck-dep@2.0.0.0/base.bend as D",
      "",
      "def pick_red() -> Nat:",
      "  D.pick(D.Red{})",
      "",
    ].join("\n"));
    const writeRoot = (kind: string, importLine: string) => {
      const dir = fs.mkdtempSync(path.join(os.tmpdir(), `lawcheck-nested-${kind}-`));
      const file = path.join(dir, "root.bend");
      fs.writeFileSync(file, [
        "import Base",
        importLine,
        "",
        "law pick_red_zero:",
        "  {H.pick_red() == 0n : Nat}",
        "",
        "law pick_red_one:",
        "  {H.pick_red() == 1n : Nat}",
        "",
      ].join("\n"));
      return file;
    };
    const roots = [
      writeRoot("named", "import lawcheck-kernel@1.2.3.4/kernel.bend as H"),
      writeRoot("hash", `import 0x${kernelHash}/kernel.bend as H`),
    ];
    for (const root of roots) {
      const r = await runEnv({ BEND_LIB: lib }, root, "--native", "--jobs", "4", "--max-instances", "6", "--json");
      expect(r.stderr).toBe("");
      expect(r.code).toBe(1);
      const rep = JSON.parse(r.stdout);
      const ok = rep.laws.find((l: any) => l.name === "pick_red_zero");
      expect(ok.status).toBe("pass");
      expect(ok.native.checked).toBeGreaterThan(0);
      expect(ok.native.disagreements).toEqual([]);
      const bad = rep.laws.find((l: any) => l.name === "pick_red_one");
      expect(bad.status).toBe("fail");
      expect(bad.native.checked).toBeGreaterThan(0);
      expect(bad.native.disagreements).toEqual([]);
      expect(bad.counterexample.expected).toBe("0n");
      expect(bad.counterexample.observed).toBe("1n");
      expect(bad.counterexample.lhs).toEqual({ term: "H.pick_red()", value: "0n" });
      // Neither the root's module nor the nested dependency may leak its hash into the readback.
      expect(r.stdout).not.toContain(kernelHash);
      expect(r.stdout).not.toContain(depHash);
    }
  }, T);
});

describe("errors", () => {
  test("syntax error: clean located message, exit 2", async () => {
    const r = await run(path.join(FX, "syntax_error.bend"));
    expect(r.code).toBe(2);
    expect(r.stdout).toBe("");
    expect(r.stderr).toContain("lawcheck: cannot load");
    // bend 2.0.32 locates the orphaned `case` (column 5); 2.0.27 located the missing `:` (column 9).
    expect(r.stderr).toContain("syntax_error.bend:5:5");
    expect(r.stderr).not.toMatch(/\n\s+at /);
  }, T);

  test("module that does not type-check: exit 2", async () => {
    const r = await run(path.join(FX, "type_error.bend"));
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("does not type-check");
    expect(r.stderr).toContain("Location: f");
  }, T);

  test("usage errors: exit 2", async () => {
    expect((await run()).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--bogus")).code).toBe(2);
    expect((await run(path.join(FX, "nope.bend"))).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--law", "nope")).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--size", "x")).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--allow-skip")).code).toBe(2);
    expect((await run("mutate", path.join(FX, "mut_weak.bend"), "--strict")).code).toBe(2);
  }, T);

  test("--json errors emit {\"error\":…} on stdout with the same exit code", async () => {
    const load = await run(path.join(FX, "syntax_error.bend"), "--json");
    expect(load.code).toBe(2);
    expect(load.stderr).toBe("");
    const e = JSON.parse(load.stdout).error;
    expect(e.kind).toBe("load");
    expect(e.message).toContain("cannot load");
    const usage = await run("--json", "--bogus");
    expect(usage.code).toBe(2);
    expect(usage.stderr).toBe("");
    expect(JSON.parse(usage.stdout).error.kind).toBe("usage");
  }, T);
});

describe("strict mode", () => {
  test("a skipped law fails the gate under --strict unless allowed", async () => {
    const file = path.join(FX, "strict_skip.bend");
    const plain = await run(file, "--jobs", "4");
    expect(plain.code).toBe(0);
    expect(plain.stdout).toContain("~ vacuous");
    const strict = await run(file, "--strict", "--jobs", "4");
    expect(strict.code).toBe(1);
    expect(strict.stdout).toContain("~ vacuous");
    const allowed = await run(file, "--strict", "--allow-skip", "strict_skip.vacuous", "--jobs", "4");
    expect(allowed.code).toBe(0);
    const wrong = await run(file, "--strict", "--allow-skip", "strict_skip.other,strict_skip.vacuous", "--jobs", "4");
    expect(wrong.code).toBe(0);
    const absent = await run(file, "--strict", "--allow-skip", "strict_skip.other", "--jobs", "4");
    expect(absent.code).toBe(1);
  }, T);

  test("an --allow-skip entry allows the skip only in its own module", async () => {
    const file = path.join(FX, "strict_skip.bend");
    const elsewhere = await run(file, "--strict", "--allow-skip", "other_module.vacuous", "--jobs", "4");
    expect(elsewhere.code).toBe(1);
    expect(elsewhere.stdout).toContain("~ vacuous");
  }, T);

  test("an unqualified --allow-skip entry is a usage error", async () => {
    const file = path.join(FX, "strict_skip.bend");
    for (const entry of ["vacuous", ".vacuous", "strict_skip.", "strict_skip.vacuous,vacuous"]) {
      const r = await run(file, "--strict", "--allow-skip", entry);
      expect(r.code).toBe(2);
      expect(r.stderr).toContain("--allow-skip entries are <module>.<law>");
    }
  }, T);

  test("--allow-skip without --strict is accepted and changes nothing", async () => {
    const r = await run(path.join(FX, "strict_skip.bend"), "--allow-skip", "strict_skip.vacuous", "--jobs", "4");
    expect(r.code).toBe(0);
  });
});

describe("json schema, maxNat, and term printing", () => {
  test("the report carries schema and the --max-nat actually used", async () => {
    const { report } = await json(path.join(FX, "correct.bend"), "--max-nat", "7", "--max-instances", "3");
    expect(report.schema).toBe(1);
    expect(report.tool).toBe("lawcheck");
    expect(report.maxNat).toBe(7);
  }, T);

  test("zero-arg calls print with () and template arguments print with ~", async () => {
    const two = law((await json(path.join(FX, "print_term.bend"), "--law", "two_bad", "--jobs", "4")).report, "two_bad");
    expect(two.status).toBe("fail");
    expect(two.counterexample.lhs.term).toBe("Nat.add(two(), 0n)");
    const tm = law((await json(path.join(FX, "templates_map.bend"), "--law", "map_id_bad", "--max-instances", "40")).report, "map_id_bad");
    expect(tm.counterexample.lhs.term).toContain("~U32");
    expect(tm.counterexample.claim).toContain("~U32");
  }, T);
});

describe("term rewriting", () => {
  test("substitutes whole identifiers only, never inside literals", () => {
    const env = new Map([["x", "1n"], ["xs", "[2n, 3n]"], ["A", "U32"], ["a", "&2"]]);
    const q = (id: string) => (id === "ins" ? "U.ins" : id);
    expect(rewrite(`{List.length(a, A, ins(x, xs)) == 1n+x : Nat}`, env, q)).toBe(`{List.length(&2, U32, U.ins(1n, ([2n, 3n]))) == 1n+1n : Nat}`);
    expect(rewrite(`f("x", 'x', xs0, Nat.x)`, env, q)).toBe(`f("x", 'x', xs0, Nat.x)`);
  });

  test("a name under a ../ namespace (bend >= 2.0.28) is one identifier", () => {
    const env = new Map([["xs", "[2n]"]]);
    const q = (id: string) => (id.startsWith("../../fx/lib_ok.") ? "L." + id.slice("../../fx/lib_ok.".length) : id);
    expect(rewrite(`{../../fx/lib_ok.size(xs) == 1n : Nat}`, env, q)).toBe(`{L.size(([2n])) == 1n : Nat}`);
  });

  test("splits a printed goal and parses printed types", () => {
    expect(splitEquation("{[3n, 5n] == [6n, 1n] : List<&2, Nat>}")).toEqual({ lhs: "[3n, 5n]", rhs: "[6n, 1n]", type: "List<&2, Nat>" });
    expect(splitEquation("{Some{(1n, 2n)} == None{} : Maybe<&2, Pair(Nat, Nat)>}")?.rhs).toBe("None{}");
    expect(showTy(parseTy("Either<a, b, List<&2, U32>, m.T>")!)).toBe("Either<a, b, List<&2, U32>, m.T>");
    expect(showTy(parseTy("List<&2, ../../fx/lib_ok.Stack>")!)).toBe("List<&2, ../../fx/lib_ok.Stack>");
    expect(parseTy("@_:A -> B")).toBeNull();
  });
});

describe("non-plain target paths (bend >= 2.0.28 imports only plain names)", () => {
  test("a target under a digit-leading directory is checked via a scratch copy; output keeps the original path", async () => {
    const base = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-nonplain-"));
    const dir = path.join(base, "4d2_vn8j");
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(path.join(dir, "lib.bend"), [
      "import Base",
      "",
      "def double(x: Nat) -> Nat:",
      "  Nat.double(x)",
      "",
    ].join("\n"));
    const ok = path.join(dir, "ok.bend");
    fs.writeFileSync(ok, [
      "import Base",
      "",
      "law add_zero:",
      "  for a: Nat",
      "  {Nat.add(a, 0n) == a : Nat}",
      "",
    ].join("\n"));
    const sibling = path.join(dir, "sibling.bend");
    fs.writeFileSync(sibling, [
      "import Base",
      "import ./lib.bend as L",
      "",
      "law double_add:",
      "  for x: Nat",
      "  {L.double(x) == Nat.add(x, x) : Nat}",
      "",
    ].join("\n"));
    const bad = path.join(dir, "bad.bend");
    fs.writeFileSync(bad, [
      "import Base",
      "import ./lib.bend as L",
      "",
      "law bad_double:",
      "  for x: Nat",
      "  {L.double(x) == x : Nat}",
      "",
    ].join("\n"));

    // the path really is one bend cannot import, so the scratch-copy branch runs
    expect(importablePath(ok)).toBe(false);

    const a = await json(ok, "--jobs", "4");
    expect(a.code).toBe(0);
    expect(a.report.laws.map((l: any) => l.status)).toEqual(["pass"]);
    expect(a.report.file).toBe(ok);

    const b = await json(sibling, "--jobs", "4");
    expect(b.code).toBe(0);
    expect(b.report.laws.map((l: any) => l.status)).toEqual(["pass"]);
    expect(b.report.file).toBe(sibling);

    const c = await run(bad, "--jobs", "4", "--json");
    expect(c.code).toBe(1);
    const rep = JSON.parse(c.stdout);
    const l = rep.laws.find((x: any) => x.name === "bad_double");
    expect(l.status).toBe("fail");
    expect(rep.file).toBe(bad);
    expect(c.stdout).toContain(bad);
    expect(c.stdout).not.toContain(path.join(rep.tmpDir, "root"));
  }, T);

  // This layout used to end in the located `plain names` error; staging the root with its imports
  // made absolute now checks it.
  test("an import that climbs above a non-plain component is checked via a staged copy", async () => {
    const base = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-nonplain-climb-"));
    const dir = path.join(base, "4d2_vn8j", "x");
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(path.join(base, "z.bend"), ["import Base", "", "def z(x: Nat) -> Nat:", "  x", ""].join("\n"));
    const root = path.join(dir, "climb.bend");
    fs.writeFileSync(root, [
      "import Base",
      "import ../../z.bend as Z",
      "",
      "law zid:",
      "  for x: Nat",
      "  {Z.z(x) == x : Nat}",
      "",
    ].join("\n"));
    const r = await run(root, "--jobs", "4");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("1 laws: 1 ✓ · 0 ✗ · 0 ~ · 0 !");
    expect(r.stdout).not.toContain("plain names");
  }, T);

  test("a target whose basename is not plain (1st.bend, x.y.bend) is checked under a plain copy", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-names-"));
    const src = ["import Base", "", "law add_zero:", "  for x: Nat", "  {Nat.add(x, 0n) == x : Nat}", "",
      "law bad:", "  for x: Nat", "  {Nat.add(x, 1n) == x : Nat}", ""].join("\n");
    for (const name of ["1st.bend", "x.y.bend"]) {
      const file = path.join(dir, name);
      fs.writeFileSync(file, src);
      expect(importablePath(file)).toBe(false);
      const r = await run(file, "--jobs", "4", "--max-instances", "10", "--json");
      expect(r.code).toBe(1);
      const rep = JSON.parse(r.stdout);
      expect(rep.file).toBe(file);
      expect(rep.laws.map((l: any) => [l.name, l.status])).toEqual([["add_zero", "pass"], ["bad", "fail"]]);
    }
  }, T);

  test("--impl swaps an import that sits under a non-plain directory", async () => {
    const dir = path.join(fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-implnp-")), "-home-x", "4d2");
    fs.mkdirSync(dir, { recursive: true });
    for (const f of ["laws_lib.bend", "lib_ok.bend", "lib_buggy.bend"]) fs.copyFileSync(path.join(FX, f), path.join(dir, f));
    const ok = await run(path.join(dir, "laws_lib.bend"), "--impl", path.join(dir, "lib_ok.bend"), "--jobs", "4", "--json");
    expect(ok.stderr).toBe("");
    expect(ok.code).toBe(0);
    expect(JSON.parse(ok.stdout).laws.every((l: any) => l.status === "pass")).toBe(true);
    const bad = await run(path.join(dir, "laws_lib.bend"), "--impl", path.join(dir, "lib_buggy.bend"), "--jobs", "4", "--json");
    expect(bad.code).toBe(1);
    const app = JSON.parse(bad.stdout).laws.find((l: any) => l.name === "app_size");
    expect(app.status).toBe("fail");
    expect(binds(app)).toEqual({ xs: "M.Push{0n, M.Bot{}}", ys: "M.Bot{}" });
  }, T);
});

describe("catalog budget, exs witnesses, tool errors, bisection", () => {
  const tmpFile = (name: string, lines: string[]) => {
    const file = path.join(fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-rv-")), name);
    fs.writeFileSync(file, lines.join("\n") + "\n");
    return file;
  };

  // 4^3 catalog contexts and a budget of 50: a prefix of the product never reached f = double
  // with a growing g, the only contexts that break the law.
  test("a budget below the catalog product still meets every pair of catalog entries", async () => {
    const file = tmpFile("cat3.bend", ["import Base", "", "law two_used:", "  for ~f: Nat -> Nat", "  for ~g: Nat -> Nat",
      "  for ~h: Nat -> Nat", "  for x: Nat", "  {Nat.is_le(f(g(1n)), 3n) == True{} : Bool}"]);
    const { code, report } = await json(file, "--max-instances", "50", "--jobs", "4");
    expect(code).toBe(1);
    const l = law(report, "two_used");
    expect(l.status).toBe("fail");
    expect(l.instances).toBe(50);
    expect(l.counterexample.bindings.find((b: any) => b.name === "f").value).toBe("(lc_x => Nat.double(lc_x))");
  }, T);

  test("a proposition-typed template binder is skipped with that reason", async () => {
    const file = tmpFile("prop.bend", ["import Base", "", "law op_assoc4:", "  for ~op: Nat -> Nat -> Nat",
      "  for ~assoc: @x: Nat -> @y: Nat -> @z: Nat -> {op(op(x, y), z) == op(x, op(y, z)) : Nat}",
      "  for a: Nat", "  {op(op(a, a), a) == op(a, op(a, a)) : Nat}"]);
    const { code, report } = await json(file, "--jobs", "4");
    expect(code).toBe(0);
    const l = law(report, "op_assoc4");
    expect(l.status).toBe("skip");
    expect(l.reason).toMatch(/^proposition-typed template binder ~assoc: /);
  }, T);

  test("an exs witness search tries each distinct value once", async () => {
    const file = tmpFile("exs.bend", ["import Base", "", "law exs_bool:", "  exs b: Bool", "  {Bool.and(b, False{}) == True{} : Bool}"]);
    const { code, report } = await json(file, "--jobs", "4");
    expect(code).toBe(0);
    expect(law(report, "exs_bool").reason).toBe("no witness found in 2 candidates");
    expect(report.checkerRuns).toBeLessThanOrEqual(2);
  }, T);

  test("an exs witness of a type with no finite value is a skip, not a crash", async () => {
    const file = tmpFile("inf.bend", ["import Base", "", "type Inf is Data:", "  Mk{x: Inf}", "", "def k(i: Inf) -> Nat:", "  0n", "",
      "law exs_inf:", "  exs i: Inf", "  {k(i) == 0n : Nat}"]);
    const r = await run(file, "--jobs", "4");
    expect(r.stderr).toBe("");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("~ exs_inf  skipped: `exs` witness i: no generator for type Inf");
  }, T);

  test("a tool error exits 2 with a typed error, under --json on stdout", async () => {
    const file = path.join(FX, "correct.bend");
    for (const args of [[file], ["mutate", file]]) {
      const j = await runEnv({ BEND_BIN: "/nonexistent/bend" }, ...args, "--json");
      expect(j.code).toBe(2);
      expect(j.stderr).toBe("");
      const e = JSON.parse(j.stdout).error;
      expect(e.kind).toBe("error");
      expect(e.message).toContain("/nonexistent/bend");
      const t = await runEnv({ BEND_BIN: "/nonexistent/bend" }, ...args);
      expect(t.code).toBe(2);
      expect(t.stdout).toBe("");
      expect(t.stderr).toMatch(/^lawcheck: .*\/nonexistent\/bend/);
      expect(t.stderr).not.toMatch(/\n\s+at /);
    }
  }, T);

  test("an empty numeric flag value is a usage error, not 0", async () => {
    for (const flag of ["--size", "--seed"]) {
      const r = await run(path.join(FX, "correct.bend"), flag, "");
      expect(r.code).toBe(2);
      expect(r.stderr).toContain(`${flag} needs an integer`);
    }
  }, T);

  // A stand-in checker that sleeps past the timeout on any batch holding a SLOW claim and
  // otherwise reports, like bend, the first BAD claim in file order.
  const slowEngine = (): Engine => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-slow-"));
    const bend = path.join(dir, "bend");
    fs.writeFileSync(bend, [
      "#!/bin/bash",
      `grep -q SLOW "$1" && exec sleep 30`,
      `awk '/^law /{id=substr($2,1,length($2)-1); getline; if ($0 ~ /BAD/) {print "Error:"; print "- expected : 1n"; print "- observed : 2n"; print "Location: " id; print "9>|   {==}"; f=1; exit}} END{if (!f) {print "ALL PROOFS CHECK"; print "Use --verdict for mathematical validity."}}' "$1"`,
    ].join("\n") + "\n");
    fs.chmodSync(bend, 0o755);
    return { header: "import Base\n", dir, bend, timeoutMs: 1500, memMb: 1024, jobs: 4, runs: 0, display: (s) => s, unsafe: [] };
  };

  test("a slow instance is isolated down to itself; a failure in the other half is still found", async () => {
    const E = slowEngine();
    const items = Array.from({ length: 8 }, (_, i) => ({ id: `t${i}`, claim: i === 2 ? "{SLOW}" : i === 5 ? "{BAD}" : "{ok}" }));
    const res = await evaluate(E, items);
    expect(items.map((it) => [it.id, res.get(it.id)!.r])).toEqual([
      ["t0", "pass"], ["t1", "pass"], ["t2", "timeout"], ["t3", "pass"], ["t4", "pass"], ["t5", "fail"], ["t6", "pass"], ["t7", "pass"],
    ]);
    expect(res.get("t5")).toEqual({ r: "fail", expected: "1n", observed: "2n" });
  }, 60_000);

  test("one slow instance in a batch of 32 is the only one timed out; the other 31 are decided", async () => {
    const E = slowEngine();
    const items = Array.from({ length: 32 }, (_, i) => ({ id: `s${i}`, claim: i === 7 ? "{SLOW}" : i === 20 ? "{BAD}" : "{ok}" }));
    const res = await evaluate(E, items);
    const want = items.map((it, i) => [it.id, i === 7 ? "timeout" : i === 20 ? "fail" : "pass"]);
    expect(items.map((it) => [it.id, res.get(it.id)!.r])).toEqual(want);
    // 1 + log2(32) timed-out runs along the slow instance's chain
    expect(E.runs).toBeLessThanOrEqual(2 * 6 + 2);
  }, 90_000);

  for (const n of [8, 32]) {
    test(`a batch of ${n} where every instance hangs stays bounded: at most 11 runs and 6 timeouts of wall time`, async () => {
      const E = slowEngine();
      const items = Array.from({ length: n }, (_, i) => ({ id: `h${i}`, claim: "{SLOW}" }));
      const t0 = performance.now();
      const res = await evaluate(E, items);
      expect(items.map((it) => res.get(it.id)!.r)).toEqual(Array(n).fill("timeout"));
      expect(E.runs).toBeLessThanOrEqual(1 + 2 * (TIMEOUT_BUDGET - 1));
      expect(performance.now() - t0).toBeLessThan(TIMEOUT_BUDGET * E.timeoutMs + 3000);
    }, 90_000);
  }

  // n = 0 overflows the checker (9^9 in unary), so the first batch is bisected; every other
  // instance is undecidable, and the halves must still stop at the first one.
  test("bisecting an overflowing batch still stops at the first undecidable instance", async () => {
    const file = tmpFile("und.bend", ["import Base", "", "def big_or_open(n: Nat) -> Type:", "  match n:", "    case 0n:",
      "      {Nat.pow(9n, 9n) == 0n : Nat}", "    case 1n+p:", "      Either<&1, &1, {p == p : Nat}, {p == p : Nat}>", "",
      "law und:", "  for n: Nat", "  big_or_open(n)"]);
    const { report } = await json(file, "--max-instances", "32", "--jobs", "4");
    const l = law(report, "und");
    expect(l.status).toBe("skip");
    expect(l.reason).toMatch(/^not decidable by evaluation/);
    expect(l.instances).toBeGreaterThan(16);
    expect(report.checkerRuns).toBeLessThanOrEqual(16);
  }, T);
});
