// Tests for the bend-mathlib tools against committed fixtures (real compiler runs).
import { expect, test } from "bun:test";
import { createHash } from "node:crypto";
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { hubHash, packageFiles } from "./hash.ts";
import { baseNames, BEND, LOCK_FORMAT, parseLock, parseModule, packageModules, ROOT, rssSource, treeRssKb, type LockEntry } from "./lib.ts";
import { lockAgainstErrors } from "./lock.ts";
import { devlibError, headerVersionError, loginError, publish, regenerateIndex, verdictError } from "./release.ts";

const dir = import.meta.dir;
const run = (script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args]);
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};
const runWith = (env: Record<string, string>, script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args], { env: { ...process.env, ...env } });
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};
// a `bend` that always fails; macOS has no /bin/false (GH #16)
const FALSE = Bun.which("false") ?? (() => { throw new Error("no `false` on PATH"); })();
const STACK = /\n\s+at /;

test("check: the good fixture is green on the pinned compiler", () => {
  const r = run("check.ts", join(dir, "fixtures/good"));
  expect(r.out).toContain("1/1 modules green");
  expect(r.code).toBe(0);
});

test("twins gives a handwritten Nat call of a twinned law its twin's call, so --verdict finds a model (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-twins-call-"));
  const src = join(tmp, "m.bend");
  writeFileSync(src, [
    "import Base", "",
    "# Applying f to zero gives its value at zero.", "law at_zero:", "  for ~f: Nat -> Nat", "  {f(0n) == f(0n) : Nat}", "",
    "def at_zero(f):", "  {==}", "",
    "def internal_nat_at_zero() -> {Nat.add(0n, 0n) == Nat.add(0n, 0n) : Nat}:", "  at_zero(~(x => Nat.add(x, 0n)))", "",
    "def internal_not_a_call(n: Nat) -> {n == n : Nat}:", "  {==}", "",
  ].join("\n"));
  expect(run("twins.ts", tmp).code).toBe(0);
  const text = readFileSync(src, "utf8");
  expect(text).toContain("def internal_nat_at_zero_sym() -> {Nat.add(0n, 0n) == Nat.add(0n, 0n) : Nat}:\n  at_zero_sym(~(x => Nat.add(x, 0n)))");
  expect(text).not.toContain("internal_not_a_call_sym");
  const p = Bun.spawnSync([BEND, src, "--check-only"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  expect(new TextDecoder().decode(p.stdout)).toContain("ALL PROOFS CHECK");
  expect(run("twins.ts", tmp, "--check").code).toBe(0);
});

test("check: a missing compiler is a toolchain error, exit 2, no stack (planted negative)", () => {
  const r = runWith({ BEND_CLI: "/nonexistent/bend" }, "check.ts", join(dir, "fixtures/good"));
  expect(r.code).toBe(2);
  expect(r.out).toContain("toolchain mismatch");
  expect(r.out).not.toMatch(STACK);
});

test("twins: the good fixture's generated section is up to date", () => {
  expect(run("twins.ts", join(dir, "fixtures/good"), "--check").code).toBe(0);
});

test("lint: the good fixture is clean, including the erasure check", () => {
  const r = run("lint.ts", join(dir, "fixtures/good"), "--erasure");
  expect(r.out).toContain("0 finding(s)");
  expect(r.code).toBe(0);
});

test("lint: every planted violation in the bad fixture is reported", () => {
  const r = run("lint.ts", join(dir, "fixtures/bad"), "--erasure");
  expect(r.code).toBe(1);
  for (const needle of [
    "must be lowercase snake_case without dots",
    "has no '#' doc line",
    "exactly one claim line (found 2)",
    "predicate 'iszero' must not match",
    "type 'tree'",
    "binder 'y' of 'Nat.add_zero_x' can be erased",
  ]) expect(r.out).toContain(needle);
});

test("index: the since column marks published and unpublished fixture lemmas", () => {
  const r = run("index.ts", join(dir, "fixtures/index"), "fixture-package", "0.1.0.0", "--stdout");
  expect(r.code).toBe(0);
  const rows = r.out.split("\n");
  expect(rows.find((l) => l.startsWith("| `not_not(b)` |"))?.endsWith("| 0.1.0.0 |")).toBe(true);
  expect(rows.find((l) => l.startsWith("| `and_comm(a, b)` |"))?.endsWith("| next |")).toBe(true);
  expect(r.out).toContain("Rows marked `next` are proved in this repository but not yet published: the import lines above do not contain them yet.");
});

test("index: no 'next' rows or note when every lock entry is published", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-index-"));
  cpSync(join(dir, "fixtures/index"), tmp, { recursive: true });
  const lockPath = join(tmp, "PUBLIC_API.lock");
  const lock: Record<string, { since: string | null }> = JSON.parse(readFileSync(lockPath, "utf8"));
  for (const e of Object.values(lock)) e.since = "0.1.0.0";
  writeFileSync(lockPath, JSON.stringify(lock, null, 2) + "\n");
  const r = run("index.ts", tmp, "fixture-package", "0.1.0.0", "--stdout");
  expect(r.code).toBe(0);
  expect(r.out).not.toContain("Rows marked");
  expect(r.out).not.toContain("| next |");
});

test("index: the last line counts lemmas and generated _sym twins separately (planted pair)", () => {
  const split = run("index.ts", join(dir, "fixtures/split"), "fixture-package", "0.1.0.0", "--stdout");
  expect(split.code).toBe(0);
  expect(split.out.trimEnd().endsWith("1 lemmas + 1 generated _sym twins, 1 predicates. Generated by `tools/mathlib/index.ts`.")).toBe(true);
  expect(split.out).toContain("| `add_zero_sym(x)` |");
  expect(split.out).toContain("| `le(a: Nat, b: Nat) -> Data` |");
  const plain = run("index.ts", join(dir, "fixtures/index"), "fixture-package", "0.1.0.0", "--stdout");
  expect(plain.code).toBe(0);
  expect(plain.out.trimEnd().endsWith("2 lemmas + 0 generated _sym twins, 0 predicates. Generated by `tools/mathlib/index.ts`.")).toBe(true);
});

const subdir = join(dir, "fixtures/subdir");

test("packageModules recurses into subdirectories", () => {
  const rel = packageModules(subdir).map((p) => p.slice(subdir.length + 1));
  expect(rel).toEqual(["all.bend", "src/helper.bend", "src/inner.bend", "src/mod.bend"]);
});

test("lint reads a module in a subdirectory", () => {
  const r = run("lint.ts", subdir);
  expect(r.code).toBe(1);
  expect(r.out).toContain("src/mod.bend");
  expect(r.out).toContain("in 4 module(s)");
});

test("lock reads a module in a subdirectory", () => {
  const r = run("lock.ts", subdir, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("mod.add_ident");
});

test("index reads a module in a subdirectory", () => {
  const r = run("index.ts", subdir, "fixture-package", "0.1.0.0", "--stdout");
  expect(r.code).toBe(0);
  expect(r.out).toContain("## mod");
  expect(r.out).toContain("add_ident");
});

test("parseModule keeps a one-line def header as the physical line", () => {
  const m = parseModule("m.bend", "import Base\n\ndef f(a: Nat) -> Data:\n  {g(a) == True{} : Bool}\n");
  expect(m.defs[0].header).toBe("def f(a: Nat) -> Data:");
  expect(m.defs[0].body).toEqual(["  {g(a) == True{} : Bool}"]);
});

test("parseModule accumulates a multi-line def header and starts the body after it", () => {
  const m = parseModule("m.bend", "import Base\n\ndef f(\n  a: Nat\n) -> Data:\n  {g(a) == True{} : Bool}\n");
  expect(m.defs[0].header).toBe("def f(\n  a: Nat\n) -> Data:");
  expect(m.defs[0].body).toEqual(["  {g(a) == True{} : Bool}"]);
});

const multiline = join(dir, "fixtures/multiline");

test("lint flags a predicate whose -> Data is on a continuation line, and the one-line control", () => {
  const r = run("lint.ts", multiline);
  expect(r.code).toBe(1);
  expect(r.out).toContain("predicate 'multiline_pred' calls 'Frobnicate', which is not a Base function");
  expect(r.out).toContain("predicate 'single_pred' calls 'Frobnicate', which is not a Base function");
});

const preds = join(dir, "fixtures/preds");

test("lint allows a predicate's own ~template params, lambda binders, and flags non-Base calls/uncalled refs (planted negatives)", () => {
  const r = run("lint.ts", preds);
  expect(r.code).toBe(1);
  expect(r.out).toContain("3 finding(s) in 5 module(s)");
  // the two candidate predicates (own `~le`/`~eq`) are clean
  expect(r.out).not.toContain("sorted_by.bend");
  expect(r.out).not.toContain("mem.bend");
  // a directory named `evidence/` is skipped as deliberately-failing negatives
  expect(r.out).not.toContain("ev_bad.bend");
  expect(r.out).not.toContain("evidence/");
  // planted negatives: a non-Base call, a ~MNat.le passed uncalled, and an own def passed uncalled
  expect(r.out).toContain("bad_call.bend:7: predicate 'bad_call' calls 'helper', which is not a Base function");
  expect(r.out).toContain("bad_ref.bend:5: predicate 'bad_ref' refers to 'MNat.le', which is not a Base function");
  expect(r.out).toContain("bad_own.bend:7: predicate 'bad_own' refers to 'own_helper', which is not a Base function");
});

test("lint still flags a bad file when the evidence directory is passed directly (negative fixtures)", () => {
  const r = run("lint.ts", join(preds, "evidence"));
  expect(r.code).toBe(1);
  expect(r.out).toContain("evidence/ev_bad.bend:6: predicate 'ev_bad' calls 'ev_helper', which is not a Base function");
});

const kern = join(dir, "fixtures/kernel");

test("lint: normal mode flags a kernel predicate's match, own call, body length and type", () => {
  const r = run("lint.ts", kern);
  expect(r.code).toBe(1);
  expect(r.out).toContain("predicate 'kernel_pred' must have a one-line body");
  expect(r.out).toContain("predicate 'kernel_pred' must not match (it would be nominal across versions)");
  expect(r.out).toContain("predicate 'kernel_pred' calls 'own_le', which is not a Base function");
  expect(r.out).toContain("predicate 'kernel_pred' calls 'Sub.sub_le', which is not a Base function");
  expect(r.out).toContain("type 'Box': bend-mathlib holds no datatypes (use a kernel package)");
});

test("lint --kernel allows match, same-package defs and types but requires a LICENSE (planted negative)", () => {
  const r = run("lint.ts", kern, "--kernel");
  expect(r.code).toBe(1);
  expect(r.out).toContain("a --kernel package requires a LICENSE file");
  expect(r.out).not.toContain("must not match");
  expect(r.out).not.toContain("calls 'own_le'");
  expect(r.out).not.toContain("calls 'Sub.sub_le'");
  expect(r.out).not.toContain("type 'Box'");
});

test("lint --kernel is clean once the package dir carries a LICENSE (acceptance form)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-kernel-"));
  const dst = join(tmp, "kernel");
  cpSync(kern, dst, { recursive: true });
  cpSync(join(ROOT, "packages", "bend-mathlib", "LICENSE"), join(dst, "LICENSE"));
  const r = run("lint.ts", dst, "--kernel");
  expect(r.code).toBe(0);
  expect(r.out).toContain("0 finding(s)");
});

test("lint --kernel is clean on the candidate kernel once a LICENSE is added (xv/k acceptance)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-kernel-xvk-"));
  const dst = join(tmp, "k");
  cpSync(join(ROOT, "research", "candidates", "perm", "generic", "xv", "k"), dst, { recursive: true });
  cpSync(join(ROOT, "packages", "bend-mathlib", "LICENSE"), join(dst, "LICENSE"));
  const r = run("lint.ts", dst, "--kernel");
  expect(r.code).toBe(0);
  expect(r.out).toContain("0 finding(s)");
});

test("lock locks a predicate whose -> Data is on a continuation line, and the one-line control", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-multiline-"));
  cpSync(multiline, tmp, { recursive: true });
  const r = run("lock.ts", tmp, "--update");
  expect(r.code).toBe(0);
  const lock = parseLock(readFileSync(join(tmp, "PUBLIC_API.lock"), "utf8"));
  expect(lock["pred.multiline_pred"]?.kind).toBe("predicate");
  expect(lock["pred.single_pred"]?.kind).toBe("predicate");
});

test("lock: an exs clause is locked, and changing a frozen exs fails (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lock-exs-"));
  const src = join(tmp, "m.bend");
  const lemmas = (exs: string) => [
    "import Base", "",
    "# A lemma with a witness.", "law witness:",
    "  for -x: Nat", `  exs ${exs}`,
    "  {Nat.is_le(x, w) == True{} : Bool}", "",
    "def witness(x):", "  x", "",
  ].join("\n");
  writeFileSync(src, lemmas("w: Nat"));
  expect(run("lock.ts", tmp, "--update").code).toBe(0);
  const lock = parseLock(readFileSync(join(tmp, "PUBLIC_API.lock"), "utf8"));
  expect(lock["m.witness"].text).toContain("exs w: Nat");
  expect(run("lock.ts", tmp, "--freeze", "0.1.0.0").code).toBe(0);
  writeFileSync(src, lemmas("w: Bool"));
  const r = run("lock.ts", tmp, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("m.witness (published in 0.1.0.0) changed");
});

test("lock: a public value def is locked, and changing a frozen body fails (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lock-def-"));
  const src = join(tmp, "m.bend");
  const def = (body: string) => [
    "import Base", "",
    "# Insert x at the front.", "def ins(x: Nat, xs: List<Nat>) -> List<Nat>:",
    `  ${body}`, "",
  ].join("\n");
  writeFileSync(src, def("x <> xs"));
  expect(run("lock.ts", tmp, "--update").code).toBe(0);
  const lock = parseLock(readFileSync(join(tmp, "PUBLIC_API.lock"), "utf8"));
  expect(lock["m.ins"].kind).toBe("def");
  expect(run("lock.ts", tmp, "--freeze", "0.1.0.0").code).toBe(0);
  writeFileSync(src, def("xs <> x"));
  const r = run("lock.ts", tmp, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("m.ins (published in 0.1.0.0) changed");
});

test("lock: a law header with a trailing comment is still locked, so changing it fails (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lock-comment-"));
  const src = join(tmp, "m.bend");
  const law = (claim: string) => ["import Base", "", "# A law.", "law noted: # a note", "  for n: Nat", `  ${claim}`, "", "def noted(n):", "  {==}", ""].join("\n");
  writeFileSync(src, law("{Nat.add(n, 0n) == n : Nat}"));
  expect(run("lock.ts", tmp, "--update").code).toBe(0);
  expect(parseLock(readFileSync(join(tmp, "PUBLIC_API.lock"), "utf8"))["m.noted"].kind).toBe("law");
  expect(run("lock.ts", tmp, "--freeze", "0.1.0.0").code).toBe(0);
  writeFileSync(src, law("{n == n : Nat}"));
  const r = run("lock.ts", tmp, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("m.noted (published in 0.1.0.0) changed");
});

test("lint and lock reject a one-line or indented law the tools cannot read (planted negatives)", () => {
  for (const header of ["law one_line: for m: Nat {m == m : Nat}", " law indented:\n  for m: Nat\n  {m == m : Nat}"]) {
    const tmp = mkdtempSync(join(tmpdir(), "bend-stray-law-"));
    writeFileSync(join(tmp, "m.bend"), ["import Base", "", "# A law.", header, "", "def x(m):", "  {==}", ""].join("\n"));
    const lint = run("lint.ts", tmp);
    expect(lint.code).toBe(1);
    expect(lint.out).toContain("a law must be a column-0 'law name:' block");
    const lock = run("lock.ts", tmp, "--update");
    expect(lock.code).toBe(1);
    expect(lock.out).toContain("is not locked");
  }
});

test("lock refuses two modules that share a basename, and flags entries gone from the source", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lock-dup-"));
  const mod = ["import Base", "", "# A law.", "law same:", "  for -m: Nat", "  {m == m : Nat}", "", "def same(m):", "  {==}", ""].join("\n");
  for (const d of ["a", "b"]) { mkdirSync(join(tmp, d)); writeFileSync(join(tmp, d, "x.bend"), mod); }
  const dup = run("lock.ts", tmp, "--update");
  expect(dup.code).toBe(1);
  expect(dup.out).toContain("'x.same' is defined twice");

  const gone = mkdtempSync(join(tmpdir(), "bend-lock-gone-"));
  writeFileSync(join(gone, "x.bend"), mod);
  writeFileSync(join(gone, "PUBLIC_API.lock"), JSON.stringify({ format: LOCK_FORMAT, entries: { "x.old": anchored({ since: null }) } }));
  const r = run("lock.ts", gone, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("no longer in the source (run --update): x.old");
});

test("lint: a public predicate needs a doc line (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lint-preddoc-"));
  writeFileSync(join(tmp, "m.bend"), ["import Base", "", "def undocumented(n: Nat) -> Data:", "  {Nat.is_le(n, 3n) == True{} : Bool}", ""].join("\n"));
  const r = run("lint.ts", tmp);
  expect(r.code).toBe(1);
  expect(r.out).toContain("predicate 'undocumented' has no '#' doc line above it");
});

test("lint --erasure reports a module that does not check instead of passing it (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lint-baseline-"));
  writeFileSync(join(tmp, "m.bend"), ["import Base", "", "# A false proof.", "law broken:", "  for n: Nat", "  {Nat.add(n, 1n) == n : Nat}", "", "def broken(n):", "  {==}", ""].join("\n"));
  const r = run("lint.ts", tmp, "--erasure");
  expect(r.code).toBe(1);
  expect(r.out).toContain("erasure not checked: the unmodified module fails");
});

test("lint: a public law statement may not name an internal_ helper (planted pair)", () => {
  const bad = mkdtempSync(join(tmpdir(), "bend-lint-internal-bad-"));
  writeFileSync(join(bad, "m.bend"), [
    "import Base", "",
    "# Names an internal helper in the public claim.", "law uses_internal:",
    "  for -x: Nat", "  {internal_z(x) == x : Nat}", "",
    "def uses_internal(x):", "  x", "",
  ].join("\n"));
  const r = run("lint.ts", bad);
  expect(r.code).toBe(1);
  expect(r.out).toContain("law 'uses_internal' names internal helper 'internal_z' in its public statement");

  const ok = mkdtempSync(join(tmpdir(), "bend-lint-internal-ok-"));
  writeFileSync(join(ok, "m.bend"), [
    "import Base", "",
    "# An internal helper law may use internal_ names.", "law internal_z_law:",
    "  for -x: Nat", "  {internal_z(x) == x : Nat}", "",
    "def internal_z_law(x):", "  x", "",
  ].join("\n"));
  const r2 = run("lint.ts", ok);
  expect(r2.code).toBe(0);
  expect(r2.out).not.toContain("names internal helper");
});

const anchored = (over: Partial<LockEntry> = {}): LockEntry => ({ kind: "law", text: "t", sha256: "s", since: "0.1.0.0", ...over });

test("lock --against: only published entries are anchored; any change is reported (planted negatives)", () => {
  const old = { "m.a": anchored() };
  expect(lockAgainstErrors(old, { "m.a": anchored() })).toEqual([]);
  for (const changed of [anchored({ text: "u" }), anchored({ sha256: "u" }), anchored({ kind: "def" }), anchored({ since: "0.2.0.0" })]) {
    expect(lockAgainstErrors(old, { "m.a": changed })).toHaveLength(1);
  }
  expect(lockAgainstErrors(old, {})).toHaveLength(1);
  expect(lockAgainstErrors({ "m.b": anchored({ since: null }) }, {})).toEqual([]);
  expect(lockAgainstErrors(old, { "m.a": anchored(), "m.c": anchored({ since: null }) })).toEqual([]);
});

test("lock --against: the real 0.1.0.1 tag matches; a missing tag is a typed failure", () => {
  const pkg = join(ROOT, "packages", "bend-mathlib");
  const ok = run("lock.ts", pkg, "--check", "--against", "bend-mathlib-v0.1.0.1");
  expect(ok.code).toBe(0);
  expect(ok.out).toContain("against bend-mathlib-v0.1.0.1: 0 check(s) failed");
  const bad = run("lock.ts", pkg, "--check", "--against", "no-such-tag-xyz");
  expect(bad.code).toBe(1);
  expect(bad.out).toContain("against: cannot read");
  expect(bad.out).not.toMatch(STACK);
});

test("lock: writes format 2 and parses both the v2 document and a bare v1 map", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-lock-format-"));
  writeFileSync(join(tmp, "m.bend"), [
    "import Base", "",
    "# A tiny law.", "law tiny:",
    "  for -x: Nat", "  {x == x : Nat}", "",
    "def tiny(x):", "  {==}", "",
  ].join("\n"));
  expect(run("lock.ts", tmp, "--update").code).toBe(0);
  const doc = JSON.parse(readFileSync(join(tmp, "PUBLIC_API.lock"), "utf8"));
  expect(doc.format).toBe(LOCK_FORMAT);
  expect(parseLock(JSON.stringify(doc))["m.tiny"]).toBeDefined();
  const bare = parseLock(JSON.stringify({ "m.x": anchored({ since: null }) }));
  expect(bare["m.x"].text).toBe("t");
});

test("index keeps a subdir module's relative path in the generated import", () => {
  const r = run("index.ts", subdir, "fixture-package", "0.1.0.0", "--stdout");
  expect(r.out).toContain("import fixture-package@0.1.0.0/src/mod.bend as MMod");
  expect(r.out).toContain("import fixture-package@0.1.0.0/src/inner.bend as MInner");
});

test("lint --erasure checks a subdir module that imports a sibling", () => {
  const r = run("lint.ts", subdir, "--erasure");
  expect(r.out).toContain("binder 'y' of 'inner_id' can be erased");
});

test("baseNames lists the compiler's Base names", async () => {
  const b = await baseNames();
  expect(b.size).toBeGreaterThan(100);
  expect(b.has("Nat.is_le")).toBe(true);
});

test("lint fails cleanly when `bend base` is broken instead of trusting an empty Base set", () => {
  const r = runWith({ BEND_CLI: FALSE }, "lint.ts", join(dir, "fixtures/good"));
  expect(r.code).toBe(2);
  expect(r.out).toMatch(/base' failed/);
  expect(r.out).not.toContain("0 finding(s)");
  expect(r.out).not.toMatch(STACK);
});

test("release fails cleanly for a missing absolute pkgdir (no mangled join, no EINVAL)", () => {
  const missing = join(tmpdir(), "bend-release-missing");
  const r = run("release.ts", missing, "some-package-name", "0.1.0.0");
  expect(r.code).toBe(1);
  expect(r.out).toContain(`package directory ${missing} does not exist`);
  expect(r.out).not.toContain("EINVAL");
});

test("release resolves an absolute existing pkgdir instead of mangling it", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-abs-"));
  writeFileSync(join(tmp, "m.bend"), "import Base\n");
  const r = runWith({ BEND_CLI: FALSE }, "release.ts", tmp, "some-package-name", "0.1.0.0");
  expect(r.code).toBe(1);
  expect(r.out).not.toContain("does not exist");
  expect(r.out).toContain("FAIL check");
});

test("release: a climbing package is a typed usage error, exit 2, no stack", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-climb-"));
  mkdirSync(join(tmp, "pkg"));
  writeFileSync(join(tmp, "other.bend"), "import Base\n\ndef other() -> U32:\n  7\n");
  writeFileSync(join(tmp, "pkg", "all.bend"), "import Base\nimport ../other.bend as Other\n\ndef f() -> U32:\n  Other.other()\n");
  expect(run("lock.ts", join(tmp, "pkg"), "--update").code).toBe(0);
  const r = run("release.ts", join(tmp, "pkg"), "some-package-name", "0.1.0.0");
  expect(r.code).toBe(2);
  expect(r.out).toContain("is outside the entry directory");
  expect(r.out).toContain("usage: release.ts <pkgdir>");
  expect(r.out).not.toMatch(STACK);
});

test("release: headerVersionError flags a stale all.bend header, accepts the target (planted pair)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-header-"));
  const entry = join(tmp, "all.bend");
  writeFileSync(entry, "# fixture-package: import fixture-package@0.1.0.0/bools.bend.\nimport Base\n");
  const err = headerVersionError(tmp, "fixture-package", "0.2.0.0");
  expect(err).toContain("names fixture-package@0.1.0.0");
  expect(err).toContain("release target is fixture-package@0.2.0.0");
  writeFileSync(entry, "# fixture-package: import fixture-package@0.2.0.0/bools.bend.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
});

test("release: headerVersionError reads only the first line and only this package's version (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-header-neg-"));
  writeFileSync(join(tmp, "all.bend"), "# fixture-package: a stub.\n# import fixture-package@0.1.0.0/bools.bend in the second line.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
  writeFileSync(join(tmp, "all.bend"), "# fixture-package: depends on other-package@0.1.0.0.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
  writeFileSync(join(tmp, "all.bend"), "# my-fixture-package: import my-fixture-package@0.1.0.0/bools.bend.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
});

test("release: the dry run fails on a stale header before any gate or hash (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-gate-"));
  mkdirSync(join(tmp, "pkg"));
  writeFileSync(join(tmp, "pkg", "all.bend"), "# fixture-package: import fixture-package@0.1.0.0/bools.bend.\nimport Base\n");
  const r = run("release.ts", join(tmp, "pkg"), "fixture-package", "0.2.0.0");
  expect(r.code).toBe(1);
  expect(r.out).toContain("names fixture-package@0.1.0.0");
  expect(r.out).not.toContain("FAIL check");
  expect(r.out).not.toContain("expected hash");
});

test("release: a correct header passes the gate and the run reaches the check gate", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-gate-ok-"));
  mkdirSync(join(tmp, "pkg"));
  writeFileSync(join(tmp, "pkg", "all.bend"), "# fixture-package: import fixture-package@0.2.0.0/bools.bend.\nimport Base\n");
  const r = runWith({ BEND_CLI: FALSE }, "release.ts", join(tmp, "pkg"), "fixture-package", "0.2.0.0");
  expect(r.code).toBe(1);
  expect(r.out).not.toContain("release target is");
  expect(r.out).toContain("FAIL check");
});

test("release: devlibError refuses the devlib dir and a BEND_LIB holding a symlink, allows a plain cache (planted pair)", () => {
  expect(devlibError(undefined)).toBeNull();
  const plain = mkdtempSync(join(tmpdir(), "bend-release-lib-plain-"));
  mkdirSync(join(plain, "0x00000000000000000000000000000000"));
  expect(devlibError(plain)).toBeNull();
  const linked = mkdtempSync(join(tmpdir(), "bend-release-lib-link-"));
  symlinkSync(join(dir, "fixtures/good"), join(linked, "0x00000000000000000000000000000000"), "dir");
  expect(devlibError(linked)).toContain(`BEND_LIB=${linked} holds the symlink`);
  expect(devlibError(join(ROOT, ".devlib"))).toContain("is the devlib directory");
});

test("release: a symlinked BEND_LIB is a usage error before any gate (planted negative)", () => {
  const linked = mkdtempSync(join(tmpdir(), "bend-release-lib-run-"));
  symlinkSync(join(dir, "fixtures/good"), join(linked, "0x00000000000000000000000000000000"), "dir");
  const r = runWith({ BEND_LIB: linked, BEND_CLI: FALSE }, "release.ts", join(dir, "fixtures/good"), "some-package-name", "0.1.0.0");
  expect(r.code).toBe(2);
  expect(r.out).toContain("not through devlib");
  expect(r.out).not.toMatch(/(ok  |FAIL) check/);
});

test("release under devlib run is refused before the header check and any gate", () => {
  const p = Bun.spawnSync([process.execPath, join(dir, "devlib.ts"), "run", "--", process.execPath, join(dir, "release.ts"), join(ROOT, "packages/bend-mathlib"), "bend-mathlib", "9.9.9.9"]);
  const out = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
  expect(p.exitCode).toBe(2);
  expect(out).toContain("is the devlib directory");
  expect(out).not.toContain("release target is");
  expect(out).not.toMatch(/(ok  |FAIL) check/);
});

test("release: lock --freeze leaves README stale until regenerateIndex runs (the post-freeze path)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-index-regen-"));
  cpSync(join(dir, "fixtures/index"), tmp, { recursive: true });
  expect(run("index.ts", tmp, "fixture-package", "0.1.0.0").code).toBe(0);
  expect(run("index.ts", tmp, "fixture-package", "0.2.0.0", "--check").code).toBe(1);
  expect(run("lock.ts", tmp, "--freeze", "0.2.0.0").code).toBe(0);
  expect(run("index.ts", tmp, "fixture-package", "0.2.0.0", "--check").code).toBe(1);
  expect(regenerateIndex(tmp, "fixture-package", "0.2.0.0").code).toBe(0);
  expect(readFileSync(join(tmp, "README.md"), "utf8")).toContain("fixture-package@0.2.0.0");
  expect(run("index.ts", tmp, "fixture-package", "0.2.0.0", "--check").code).toBe(0);
});

// A local BendHub in its own process (Bun.spawnSync in release.ts would deadlock a server in the
// test's event loop). GET /__state reports what the hub received.
const MOCK_HUB_SRC = `
import { createHash } from "node:crypto";
const packages = new Map();
const names = new Map();
const publishes = [];
const server = Bun.serve({
  port: 0,
  async fetch(req) {
    const p = new URL(req.url).pathname;
    if (req.method === "POST" && p === "/") {
      const body = await req.json().catch(() => null);
      const files = body && body.files;
      if (!files) return new Response("bad request", { status: 400 });
      const manifest = Object.keys(files).sort().map((x) => createHash("sha256").update(files[x]).digest("hex") + " " + x + "\\n").join("");
      const hash = "0x" + createHash("sha256").update(manifest).digest("hex").slice(0, 32);
      packages.set(hash, { manifest, files });
      publishes.push(hash);
      return new Response(process.env.MOCK_TAMPER === "1" ? "0x" + "1".repeat(32) + "\\n" : hash + "\\n");
    }
    if (req.method === "GET" && p === "/__state") return Response.json({ publishes, names: Object.fromEntries(names) });
    if (req.method === "GET" && p === "/publish-check") return Response.json({ name: "free", version_ok: true, reason: "" });
    if (req.method === "POST" && p === "/register") return Response.json({ ok: true });
    if (req.method === "POST" && p === "/link") {
      const body = await req.json();
      names.set(body.name + "@" + body.version, body.hash);
      return Response.json({ ok: true });
    }
    if (req.method === "GET" && p.startsWith("/name/")) {
      const hash = names.get(p.slice(6));
      return hash === undefined ? new Response("", { status: 404 }) : new Response(hash + "\\n");
    }
    const seg = p.split("/");
    if (req.method === "GET" && seg.length >= 3 && /^0x[0-9a-f]{32}$/.test(seg[1])) {
      const pkg = packages.get(seg[1]);
      if (!pkg) return new Response("", { status: 404 });
      if (seg[2] === "manifest") return new Response(pkg.manifest);
      const file = pkg.files[seg.slice(2).join("/")];
      return file === undefined ? new Response("", { status: 404 }) : new Response(file);
    }
    return new Response("not found", { status: 404 });
  },
});
console.log(String(server.port));
`;

async function startMockHub(extraEnv: Record<string, string> = {}) {
  const file = join(mkdtempSync(join(tmpdir(), "bend-mock-hub-")), "hub.ts");
  writeFileSync(file, MOCK_HUB_SRC);
  const proc = Bun.spawn([process.execPath, file], { stdout: "pipe", stderr: "inherit", env: { ...process.env, ...extraEnv } });
  const first = await proc.stdout.getReader().read();
  const port = new TextDecoder().decode(first.value ?? new Uint8Array()).trim();
  expect(port).toMatch(/^\d+$/);
  const url = `http://127.0.0.1:${port}`;
  const state = async () => (await (await fetch(`${url}/__state`)).json()) as { publishes: string[]; names: Record<string, string> };
  return { url, state, stop: () => proc.kill() };
}

function makeReleasePkg(name: string, version: string): string {
  const pkg = join(mkdtempSync(join(tmpdir(), "bend-release-pkg-")), "pkg");
  mkdirSync(pkg);
  cpSync(join(dir, "fixtures/good/list.bend"), join(pkg, "list.bend"));
  writeFileSync(join(pkg, "all.bend"),
    `# ${name}: fixture lemmas; import one module, e.g. ${name}@${version}/list.bend.\nimport Base\nimport ./list.bend as L\n`);
  expect(run("lock.ts", pkg, "--update").code).toBe(0);
  return pkg;
}

// A bend stand-in for the untestable part: --publish mines a proof of work (minutes here). It
// speaks the same CLI and hub protocol as main.ts; other calls delegate to the real bend.
function makePublishStub(): string {
  const stub = join(mkdtempSync(join(tmpdir(), "bend-publish-stub-")), "bend");
  writeFileSync(stub, `#!${process.execPath}
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { packageFiles } from "${join(dir, "hash.ts")}";

const REAL = process.env.BEND_REAL ?? "";
const HUB = process.env.BEND_HUB ?? "";
const args = process.argv.slice(2);
const key = () => {
  try { return String((JSON.parse(readFileSync(join(process.env.HOME ?? "", ".bend", "bendai.json"), "utf8"))).key ?? ""); } catch { return ""; }
};
const post = (route, body) => fetch(HUB + route, { method: "POST",
  headers: { authorization: "Bearer " + key(), "content-type": "application/json" }, body: JSON.stringify(body) });

if (args.includes("--publish")) {
  const res = await fetch(HUB, { method: "POST", body: JSON.stringify({ files: packageFiles(args[0]), nonce: 0 }) });
  console.log((await res.text()).trim());
  process.exit(res.ok ? 0 : 1);
}
if (args[0] === "link") {
  const [name, version] = args[1].split("@");
  const check = await (await fetch(HUB + "/publish-check?name=" + name + "&version=" + version,
    { headers: { authorization: "Bearer " + key() } })).json();
  if (check.name === "free") await post("/register", { name });
  await post("/link", { name, version, hash: args[2] });
  console.log("linked " + args[1] + " to " + args[2]);
  process.exit(0);
}
const p = Bun.spawnSync([REAL, ...args], { env: process.env });
process.stdout.write(p.stdout);
process.stderr.write(p.stderr);
process.exit(p.exitCode);
`, { mode: 0o755 });
  return stub;
}

test("release: loginError is null with a key and typed without one (planted pair)", () => {
  const saved = process.env.HOME;
  try {
    const bad = mkdtempSync(join(tmpdir(), "bend-login-bad-"));
    process.env.HOME = bad;
    expect(loginError()).toContain("run `bend login`");
    for (const file of ["bendai.json", "bender.json"]) {
      const good = mkdtempSync(join(tmpdir(), "bend-login-good-"));
      mkdirSync(join(good, ".bend"));
      writeFileSync(join(good, ".bend", file), JSON.stringify({ key: "test-key", login: "tester" }) + "\n");
      process.env.HOME = good;
      expect(loginError()).toBeNull();
    }
  } finally {
    if (saved === undefined) delete process.env.HOME; else process.env.HOME = saved;
  }
});

test("release: verdictError accepts only exit 0 with exactly ALL PROOFS CHECK (planted negatives)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-verdict-"));
  const bin = join(tmp, "bend");
  writeFileSync(bin, [
    "#!/bin/sh",
    '[ "$2" = --verdict ] || exit 9',
    'case "$1" in',
    '  *clean.bend) echo "ALL PROOFS CHECK" ;;',
    '  *hole.bend) echo "SOME PROOFS FAIL"; echo "?goal"; exit 1 ;;',
    '  *mismatch.bend) echo "Sorry - this is a mismatch between the TypeScript implementation, and the formalized BendTT kernel."; exit 1 ;;',
    '  *extra.bend) echo "ALL PROOFS CHECK"; echo "Error: 1 defs rely on unsafe or foreign code:" ;;',
    "esac",
  ].join("\n") + "\n", { mode: 0o755 });
  const saved = process.env.BEND_CLI;
  try {
    process.env.BEND_CLI = bin;
    expect(verdictError(join(tmp, "clean.bend"))).toBeNull();
    expect(verdictError(join(tmp, "hole.bend"))).toContain("SOME PROOFS FAIL");
    expect(verdictError(join(tmp, "mismatch.bend"))).toContain("(exit 1):\nSorry - this is a mismatch");
    expect(verdictError(join(tmp, "extra.bend"))).toContain("rely on unsafe");
  } finally {
    if (saved === undefined) delete process.env.BEND_CLI; else process.env.BEND_CLI = saved;
  }
});

test("release publish: a local mock hub exercises publish, verify, link, freeze and README", async () => {
  const hub = await startMockHub();
  const home = mkdtempSync(join(tmpdir(), "bend-release-home-"));
  mkdirSync(join(home, ".bend"));
  writeFileSync(join(home, ".bend", "bendai.json"), JSON.stringify({ key: "test-key", login: "tester" }) + "\n");
  const releases = join(mkdtempSync(join(tmpdir(), "bend-ledger-")), "RELEASES.md");
  const pkg = makeReleasePkg("fixture-package", "0.2.0.0");
  const stub = makePublishStub();
  const saved = { HOME: process.env.HOME, BEND_HUB: process.env.BEND_HUB, BENDLIB_RELEASES: process.env.BENDLIB_RELEASES, BEND_CLI: process.env.BEND_CLI, BEND_REAL: process.env.BEND_REAL };
  process.env.HOME = home;
  process.env.BEND_HUB = hub.url;
  process.env.BENDLIB_RELEASES = releases;
  process.env.BEND_CLI = stub;
  process.env.BEND_REAL = BEND;
  try {
    const expected = hubHash(packageFiles(join(pkg, "all.bend")));
    const got = await publish(pkg, "fixture-package", "0.2.0.0", expected);
    expect(got).toBe(expected);
    expect((await hub.state()).publishes).toEqual([expected]);
    const lock = parseLock(readFileSync(join(pkg, "PUBLIC_API.lock"), "utf8"));
    expect(Object.values(lock).every((e) => e.since === "0.2.0.0")).toBe(true);
    expect(readFileSync(join(pkg, "README.md"), "utf8")).toContain("fixture-package@0.2.0.0");
    expect(readFileSync(releases, "utf8")).toContain(`| fixture-package | 0.2.0.0 | \`${got}\` |`);
  } finally {
    if (saved.HOME === undefined) delete process.env.HOME; else process.env.HOME = saved.HOME;
    if (saved.BEND_HUB === undefined) delete process.env.BEND_HUB; else process.env.BEND_HUB = saved.BEND_HUB;
    if (saved.BENDLIB_RELEASES === undefined) delete process.env.BENDLIB_RELEASES; else process.env.BENDLIB_RELEASES = saved.BENDLIB_RELEASES;
    if (saved.BEND_CLI === undefined) delete process.env.BEND_CLI; else process.env.BEND_CLI = saved.BEND_CLI;
    if (saved.BEND_REAL === undefined) delete process.env.BEND_REAL; else process.env.BEND_REAL = saved.BEND_REAL;
    hub.stop();
  }
}, 180000);

test("release publish: a hub that echoes a different hash is refused before link/freeze (planted negative)", async () => {
  const hub = await startMockHub({ MOCK_TAMPER: "1" });
  const home = mkdtempSync(join(tmpdir(), "bend-release-tamper-home-"));
  mkdirSync(join(home, ".bend"));
  writeFileSync(join(home, ".bend", "bendai.json"), JSON.stringify({ key: "test-key", login: "tester" }) + "\n");
  const releases = join(mkdtempSync(join(tmpdir(), "bend-ledger-tamper-")), "RELEASES.md");
  const pkg = makeReleasePkg("fixture-package", "0.2.0.0");
  const stub = makePublishStub();
  const saved = { HOME: process.env.HOME, BEND_HUB: process.env.BEND_HUB, BENDLIB_RELEASES: process.env.BENDLIB_RELEASES, BEND_CLI: process.env.BEND_CLI, BEND_REAL: process.env.BEND_REAL };
  process.env.HOME = home;
  process.env.BEND_HUB = hub.url;
  process.env.BENDLIB_RELEASES = releases;
  process.env.BEND_CLI = stub;
  process.env.BEND_REAL = BEND;
  try {
    const expected = hubHash(packageFiles(join(pkg, "all.bend")));
    await expect(publish(pkg, "fixture-package", "0.2.0.0", expected)).rejects.toThrow(/differs from the locally computed/);
    const state = await hub.state();
    expect(state.publishes).toHaveLength(1);
    expect(state.names["fixture-package@0.2.0.0"]).toBeUndefined();
    expect(readFileSync(join(pkg, "PUBLIC_API.lock"), "utf8")).not.toContain("0.2.0.0");
    expect(existsSync(join(pkg, "README.md"))).toBe(false);
  } finally {
    if (saved.HOME === undefined) delete process.env.HOME; else process.env.HOME = saved.HOME;
    if (saved.BEND_HUB === undefined) delete process.env.BEND_HUB; else process.env.BEND_HUB = saved.BEND_HUB;
    if (saved.BENDLIB_RELEASES === undefined) delete process.env.BENDLIB_RELEASES; else process.env.BENDLIB_RELEASES = saved.BENDLIB_RELEASES;
    if (saved.BEND_CLI === undefined) delete process.env.BEND_CLI; else process.env.BEND_CLI = saved.BEND_CLI;
    if (saved.BEND_REAL === undefined) delete process.env.BEND_REAL; else process.env.BEND_REAL = saved.BEND_REAL;
    hub.stop();
  }
}, 60000);

test("release --publish: no stored key fails typed before publish touches the hub (planted negative)", async () => {
  const hub = await startMockHub();
  const home = mkdtempSync(join(tmpdir(), "bend-release-nologin-"));
  const releases = join(mkdtempSync(join(tmpdir(), "bend-ledger-neg-")), "RELEASES.md");
  const pkg = makeReleasePkg("fixture-package", "0.2.0.0");
  try {
    const r = runWith({ HOME: home, BEND_CLI: BEND, BEND_HUB: hub.url, BENDLIB_RELEASES: releases }, "release.ts", pkg, "fixture-package", "0.2.0.0", "--publish");
    expect(r.code).toBe(1);
    expect(r.out).toContain("run `bend login`");
    expect((await hub.state()).publishes).toHaveLength(0);
    expect(existsSync(join(pkg, "README.md"))).toBe(false);
    expect(readFileSync(join(pkg, "PUBLIC_API.lock"), "utf8")).not.toContain("0.2.0.0");
  } finally {
    hub.stop();
  }
});

test("a missing or non-directory package path is a typed usage error, exit 2, no stack", () => {
  const parent = mkdtempSync(join(tmpdir(), "bend-missing-"));
  const missing = join(parent, "nope");
  const file = join(dir, "fixtures/good/list.bend");
  const cases: [string, string[]][] = [
    ["check.ts", [missing]],
    ["check.ts", [file]],
    ["lint.ts", [missing]],
    ["twins.ts", [missing, "--check"]],
    ["lock.ts", [missing, "--check"]],
    ["index.ts", [missing, "fixture-package", "0.1.0.0", "--stdout"]],
  ];
  for (const [script, args] of cases) {
    const r = run(script, ...args);
    expect(r.code).toBe(2);
    expect(r.out).toMatch(/no such package directory|not a directory/);
    expect(r.out).not.toMatch(STACK);
  }
});

test("check: --max-seconds must be a positive integer", () => {
  const r = run("check.ts", join(dir, "fixtures/good"), "--max-seconds", "x");
  expect(r.code).toBe(2);
  expect(r.out).toContain("--max-seconds needs a positive integer");
  expect(r.out).not.toMatch(STACK);
});

test("index: the version must be a.b.c.d", () => {
  const r = run("index.ts", join(dir, "fixtures/index"), "fixture-package", "notaversion", "--stdout");
  expect(r.code).toBe(2);
  expect(r.out).toContain("version must be a.b.c.d");
  expect(r.out).not.toMatch(STACK);
});

test("twins: a byte-empty module is up to date, not perpetually stale", () => {
  const empty = join(dir, "fixtures/empty");
  const r = run("twins.ts", empty, "--check");
  expect(r.code).toBe(0);
  expect(r.out).toContain("twins up to date");
  expect(readFileSync(join(empty, "empty.bend"), "utf8")).toBe("");
});

const foreign = join(dir, "fixtures/foreign");
const refHash = (rec: Record<string, string>) =>
  "0x" + createHash("sha256").update(Object.keys(rec).sort()
    .map((p) => createHash("sha256").update(rec[p]).digest("hex") + " " + p + "\n").join(""))
    .digest("hex").slice(0, 32);
const foreignRecord = () => ({
  "main.bend": readFileSync(join(foreign, "main.bend"), "utf8"),
  "shout.c": readFileSync(join(foreign, "shout.c"), "utf8"),
  "sub/helper.js": readFileSync(join(foreign, "sub/helper.js"), "utf8"),
  "sub/mod.bend": readFileSync(join(foreign, "sub/mod.bend"), "utf8"),
  "LICENSE": readFileSync(join(foreign, "LICENSE"), "utf8"),
});

test("the foreign fixture is genuinely foreign to the pinned compiler", () => {
  const p = Bun.spawnSync([BEND, join(foreign, "main.bend"), "--check-only"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  expect(new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).toMatch(/defs? rely on unsafe or foreign code/);
});

test("packageFiles collects a def's foreign .c and .js imports at their paths", () => {
  expect(Object.keys(packageFiles(join(foreign, "main.bend"))).sort())
    .toEqual(["LICENSE", "main.bend", "shout.c", "sub/helper.js", "sub/mod.bend"]);
});

test("hash: the CLI hash covers the foreign files, computed over the exact manifest", () => {
  const r = run("hash.ts", join(foreign, "main.bend"));
  expect(r.code).toBe(0);
  expect(r.out).toContain("shout.c");
  expect(r.out).toContain("sub/helper.js");
  expect(r.out).toContain(refHash(foreignRecord()));
});

test("packageFiles: a package with no foreign files is byte-identical to before (planted negative)", () => {
  expect(hubHash(packageFiles(join(subdir, "all.bend")))).toBe("0xdfe38237eb381cd99fcdc0bc22bf893b");
  expect(hubHash(packageFiles(join(dir, "fixtures/good/list.bend")))).toBe("0x872818a5c5997957f8e2324698c1296e");
});

test("packageFiles: an indented `import` inside a comment is not a foreign file (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-hash-comment-"));
  writeFileSync(join(tmp, "main.bend"), 'import Base\n\ndef f(x: U32) -> IO(U32):\n  # import "./ghost.c" is only a note\n  x\n');
  expect(Object.keys(packageFiles(join(tmp, "main.bend")))).toEqual(["main.bend"]);
});

test("packageFiles follows every local import form bend loads, and drops a BOM (planted negatives)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-hash-forms-"));
  writeFileSync(join(tmp, "all.bend"), "﻿import Base\nimport plain.bend as P\n  import ./indented.bend as I  # a note\n\ndef f() -> Nat:\n  Nat.add(P.p(), I.i())\n");
  writeFileSync(join(tmp, "plain.bend"), "import Base\n\ndef p() -> Nat:\n  1n\n");
  writeFileSync(join(tmp, "indented.bend"), "import Base\n\ndef i() -> Nat:\n  2n\n");
  writeFileSync(join(tmp, "unused.bend"), "import Base\n");
  const p = Bun.spawnSync([BEND, join(tmp, "all.bend"), "--check-only"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  expect(new TextDecoder().decode(p.stdout)).toContain("ALL PROOFS CHECK");
  const files = packageFiles(join(tmp, "all.bend"));
  expect(Object.keys(files).sort()).toEqual(["all.bend", "indented.bend", "plain.bend"]);
  expect(files["all.bend"].startsWith("import Base")).toBe(true);

  // bend keys an absolute import by its path below the entry, and refuses one outside it
  writeFileSync(join(tmp, "abs.bend"), `import Base\nimport ${join(tmp, "plain.bend")} as P\n`);
  expect(Object.keys(packageFiles(join(tmp, "abs.bend"))).sort()).toEqual(["abs.bend", "plain.bend"]);
  const away = mkdtempSync(join(tmpdir(), "bend-hash-away-"));
  writeFileSync(join(away, "far.bend"), "import Base\n");
  writeFileSync(join(tmp, "far.bend"), `import Base\nimport ${join(away, "far.bend")} as F\n`);
  expect(() => packageFiles(join(tmp, "far.bend"))).toThrow(/outside the entry directory/);
});

test("hash: a missing, non-file or climbing entry is a typed usage error, exit 2, no stack", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-hash-bad-"));
  const climb = join(tmp, "pkg", "sub", "main.bend");
  mkdirSync(join(tmp, "pkg", "sub"), { recursive: true });
  writeFileSync(join(tmp, "pkg", "other.bend"), "import Base\n\ndef other() -> Nat:\n  7\n");
  writeFileSync(climb, "import Base\nimport ../other.bend as Other\n\ndef f() -> Nat:\n  Other.other()\n");
  const cases: [string, string][] = [
    ["not a .bend file", join(tmp, "nope.bend")],
    ["not a .bend file", tmp],
    ["is outside the entry directory", climb],
  ];
  for (const [needle, arg] of cases) {
    const r = run("hash.ts", arg);
    expect(r.code).toBe(2);
    expect(r.out).toContain(needle);
    expect(r.out).toContain("usage: bun tools/mathlib/hash.ts");
    expect(r.out).not.toMatch(STACK);
  }
});

test.skipIf(process.platform !== "linux")("treeRssKb: the ps measure of a process tree agrees with /proc, children included", async () => {
  expect(rssSource()).toBe("proc");
  // bash waits on a child that holds 64 MB it has written, so the tree's size is mostly the child's
  const hold = "const b = Buffer.alloc(64 << 20, 1); setTimeout(() => b.length, 30000)";
  const p = Bun.spawn(["bash", "-c", `"$0" -e '${hold}' & wait`, process.execPath], { stdout: "ignore", stderr: "ignore" });
  try {
    for (let i = 0; i < 100 && treeRssKb(p.pid, "proc") < 64 * 1024; i++) await Bun.sleep(100);
    const before = treeRssKb(p.pid, "proc"), ps = treeRssKb(p.pid, "ps"), after = treeRssKb(p.pid, "proc");
    expect(before).toBeGreaterThan(64 * 1024);
    expect(ps).toBeGreaterThan(Math.min(before, after) * 0.8);
    expect(ps).toBeLessThan(Math.max(before, after) * 1.2);
    expect(treeRssKb(999999999, "ps")).toBe(0);
  } finally {
    Bun.spawnSync(["pkill", "-9", "-P", String(p.pid)]);
    p.kill(9);
  }
  await p.exited;
  expect(treeRssKb(p.pid, "ps")).toBe(0);
});

