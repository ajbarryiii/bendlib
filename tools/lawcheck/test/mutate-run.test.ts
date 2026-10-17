// Real-bend mutation-runner tests: the laws are checked against every mutant of
// the target file's defs; nothing is mocked.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { mutate } from "../src/lawcheck.ts";

const FX = path.join(import.meta.dir, "fixtures");
const T = 240_000;
const def = (rep: any, name: string) => rep.defs.find((d: any) => d.name === name);

/** A fresh temp directory holding the given files (name to lines). */
function files(tree: Record<string, string[]>): string {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-mutrun-"));
  for (const [name, lines] of Object.entries(tree)) fs.writeFileSync(path.join(dir, name), lines.join("\n") + "\n");
  return dir;
}

describe("mutate runner", () => {
  test("weak laws leave survivors; some mutants are invalid", async () => {
    const rep = await mutate(path.join(FX, "mut_weak.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const all = rep.defs.flatMap((d: any) => d.mutants);
    expect(all.some((m: any) => m.status === "survived")).toBe(true);
    expect(all.some((m: any) => m.status === "invalid")).toBe(true);
    // The bead's app arg-swap is rejected by Bend's termination checker (not a
    // decreasing self-call), so it is invalid, not survived; `size` still survives.
    const swap = def(rep, "app").mutants.find((m: any) => m.op === "arg-swap");
    expect(swap.status).toBe("invalid");
    expect(def(rep, "size").mutants.some((m: any) => m.status === "survived")).toBe(true);
  }, T);

  test("strong laws kill every mutant of both defs", async () => {
    const rep = await mutate(path.join(FX, "mut_strong.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    for (const name of ["app", "size"]) {
      expect(def(rep, name).mutants.filter((m: any) => m.status === "survived")).toEqual([]);
    }
  }, T);

  test("in-file mode mutates one def and kills at least one mutant", async () => {
    const rep = await mutate(path.join(FX, "correct.bend"), { def: "dbl", jobs: 4, maxInstances: 5 });
    expect(rep.defs.map((d: any) => d.name)).toEqual(["dbl"]);
    expect(rep.defs[0].mutants.some((m: any) => m.status === "killed")).toBe(true);
  }, T);

  // first_of calls the non-self helper pick; swapping pick's arguments still
  // type-checks, and the diagonal law first_of(a, a) = a does not catch it.
  test("a non-self arg-swap can genuinely survive", async () => {
    const rep = await mutate(path.join(FX, "mut_argswap.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const swaps = def(rep, "first_of").mutants.filter((m: any) => m.op === "arg-swap");
    expect(swaps).toHaveLength(1);
    expect(swaps[0].def).toBe("first_of");
    expect(swaps[0].status).toBe("survived");
  }, T);

  test("proofs in the laws file are stripped in impl mode, so mutants are classified by the laws", async () => {
    const rep = await mutate(path.join(FX, "mut_proved", "laws.bend"), {
      impl: path.join(FX, "mut_proved", "lib.bend"), jobs: 4, maxInstances: 20, seed: 1, size: 3,
    });
    const ms = rep.defs.flatMap((d: any) => d.mutants);
    expect(ms.filter((m: any) => m.status === "killed").length).toBeGreaterThanOrEqual(4);
    expect(ms.some((m: any) => m.status === "survived")).toBe(false);
    expect(ms.some((m: any) => m.status === "invalid")).toBe(true);
  }, T);

  test("no law evaluated on the base is a usage error, never all-survivors", async () => {
    await expect(mutate(path.join(FX, "mut_allskip.bend"), { jobs: 4, maxInstances: 5 })).rejects.toThrow(/no law was evaluated on the unmutated code/);
    await expect(mutate(path.join(FX, "mut_nolaws.bend"), { jobs: 4, maxInstances: 5 })).rejects.toThrow(/no law was evaluated on the unmutated code/);
  }, T);

  test("in-file mode keeps the target's local imports resolvable in every copy", async () => {
    const dir = files({
      "helper.bend": ["import Base", "", "def two() -> Nat:", "  2n"],
      "target.bend": ["import Base", "import ./helper.bend as H", "", "def dbl(n: Nat) -> Nat:", "  match n:", "    case 0n:", "      0n",
        "    case 1n+p:", "      Nat.add(H.two(), dbl(p))", "", "law dbl_one:", "  {dbl(1n) == 2n : Nat}"],
    });
    const rep = await mutate(path.join(dir, "target.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const ms = def(rep, "dbl").mutants;
    expect(ms.filter((m: any) => m.status === "killed").length).toBeGreaterThanOrEqual(2);
    expect(ms.some((m: any) => /no such file/.test(m.detail ?? ""))).toBe(false);
  }, T);

  test("impl mode keeps the impl file's own local imports resolvable in every mutant", async () => {
    const dir = files({
      "types.bend": ["import Base", "", "def two() -> Nat:", "  2n"],
      "lib.bend": ["import Base", "import ./types.bend as T", "", "def dbl(n: Nat) -> Nat:", "  match n:", "    case 0n:", "      0n",
        "    case 1n+p:", "      Nat.add(T.two(), dbl(p))"],
      "laws.bend": ["import Base", "import ./lib.bend as L", "", "law dbl_one:", "  {L.dbl(1n) == 2n : Nat}"],
    });
    const rep = await mutate(path.join(dir, "laws.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    expect(rep.impl).toBe(path.join(dir, "lib.bend"));
    const ms = def(rep, "dbl").mutants;
    expect(ms.filter((m: any) => m.status === "killed").length).toBeGreaterThanOrEqual(2);
    expect(ms.some((m: any) => /no such file/.test(m.detail ?? ""))).toBe(false);
  }, T);

  // `internal_dbl_zero` proves dbl(0n) == 0n, so the `0n → 1n` mutant broke that proof and was
  // reported invalid; with proofs stripped the law dbl_zero kills it.
  test("proof helpers are stripped, so a behaviour change is killed by a law, in-file and in impl mode", async () => {
    const dbl = ["def dbl(n: Nat) -> Nat:", "  match n:", "    case 0n:", "      0n", "    case 1n+p:", "      2n+dbl(p)"];
    const inFile = files({
      "m.bend": ["import Base", "", ...dbl, "", "def internal_dbl_zero() -> {dbl(0n) == 0n : Nat}:", "  {==}", "",
        "law dbl_zero:", "  {dbl(0n) == 0n : Nat}", "", "def dbl_zero():", "  internal_dbl_zero()", "",
        "law dbl_one:", "  {dbl(1n) == 2n : Nat}"],
    });
    const impl = files({
      "lib.bend": ["import Base", "", ...dbl, "", "def internal_lib_zero() -> {dbl(0n) == 0n : Nat}:", "  {==}"],
      "laws.bend": ["import Base", "import ./lib.bend as L", "", "def internal_dbl_zero() -> {L.dbl(0n) == 0n : Nat}:", "  {==}", "",
        "law dbl_zero:", "  {L.dbl(0n) == 0n : Nat}", "", "def dbl_zero():", "  internal_dbl_zero()", "",
        "law dbl_one:", "  {L.dbl(1n) == 2n : Nat}"],
    });
    for (const [file, opts] of [[path.join(inFile, "m.bend"), {}], [path.join(impl, "laws.bend"), { impl: path.join(impl, "lib.bend") }]] as const) {
      const rep = await mutate(file, { ...opts, jobs: 4, maxInstances: 5, seed: 1, size: 3 });
      expect(rep.defs.map((d: any) => d.name)).toEqual(["dbl"]);
      const lit = def(rep, "dbl").mutants.find((m: any) => m.op === "literal" && m.before === "0n" && m.after === "1n");
      expect(lit.status).toBe("killed");
      expect(lit.law).toBe("dbl_zero");
    }
  }, T);

  test("impl mode works when the files sit under a non-plain directory", async () => {
    const dir = path.join(files({}), "-home-x");
    fs.mkdirSync(dir);
    for (const f of ["mut_weak.bend", "lib_ok.bend"]) fs.copyFileSync(path.join(FX, f), path.join(dir, f));
    const rep = await mutate(path.join(dir, "mut_weak.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const all = rep.defs.flatMap((d: any) => d.mutants);
    expect(all.some((m: any) => /plain names/.test(m.detail ?? ""))).toBe(false);
    expect(def(rep, "app").mutants.filter((m: any) => m.status === "killed").length).toBeGreaterThanOrEqual(3);
    expect(def(rep, "size").mutants.some((m: any) => m.status === "survived")).toBe(true);
  }, T);

  test("an invalid mutant's detail keeps the checker's expected/observed lines", async () => {
    const rep = await mutate(path.join(FX, "mut_weak.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const inv = rep.defs.flatMap((d: any) => d.mutants).filter((m: any) => m.status === "invalid");
    expect(inv.length).toBeGreaterThan(0);
    expect(inv.some((m: any) => (m.detail ?? "").includes("- expected"))).toBe(true);
    expect(inv.every((m: any) => m.detail !== "Error:")).toBe(true);
  }, T);
});
