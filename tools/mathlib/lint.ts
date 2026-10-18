// lint: enforce bend-mathlib's permanent-API conventions (PLAN.md §3.1).
//
//   names      law/def names are lowercase snake_case, no dots (the compiler enforces F5 Base collisions)
//   docs/claims every public law has a `#` doc line, one claim line and a proof right below it
//   types      no `type` declarations (mathlib holds no nominal definitions)
//   predicates a type-level def (-> Data / -> Type) has a one-line body with no `match` that calls
//              only Base functions, its own `~` templates and lambda-bound names; a directory named
//              `evidence/` is skipped as deliberately-failing negatives unless it is the package itself
//   internal   a public law's binders / exs / claim may not name an internal_* helper
//   erasure    (--erasure) every binder that CAN be erased is: tried in a scratch copy
//   kernel     (--kernel) predicates may match and call own defs; `type`s allowed; a LICENSE is required
// usage: bun tools/mathlib/lint.ts [pkgdir] [--erasure] [--allow-types] [--kernel] · exit: 0/1/2

import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, relative, resolve, sep } from "node:path";
import { BEND, CLEAN, PkgError, ROOT, baseNames, isHubImport, isPredicate, packageModules, parseModule, type Module } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/lint.ts [pkgdir] [--erasure] [--allow-types] [--kernel]";
const usage = (msg: string): never => { console.error(`lint: ${msg}\n${USAGE}`); process.exit(2); };

const args = process.argv.slice(2);
const pkg = resolve(args.find((a) => !a.startsWith("--")) ?? join(ROOT, "packages", "bend-mathlib"));
const doErasure = args.includes("--erasure");
const kernel = args.includes("--kernel");
const allowTypes = args.includes("--allow-types") || kernel;

const findings: string[] = [];
const at = (m: Module, line: number, msg: string) => findings.push(`${relative(ROOT, m.file)}:${line}: ${msg}`);
const NAME = /^[a-z][a-z0-9_]*$/;
let files: string[];
try { files = packageModules(pkg); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
// `evidence/` holds deliberately-failing negatives; skip it below the package root, but still
// lint it when it is the package itself (a directly-passed path keeps failing).
files = files.filter((f) => !relative(pkg, f).split(sep).slice(0, -1).includes("evidence"));
const base = await baseNames().catch((e: unknown) => usage(e instanceof Error ? e.message : String(e)));
const mods = files.map((f) => parseModule(f));

if (kernel && !existsSync(join(pkg, "LICENSE"))) findings.push(`${relative(ROOT, join(pkg, "LICENSE"))}: a --kernel package requires a LICENSE file`);

for (const m of mods) {
  for (const law of m.laws) {
    if (!NAME.test(law.name)) at(m, law.line, `law name '${law.name}' must be lowercase snake_case without dots`);
    if (!law.name.startsWith("internal_")) {
      for (const s of [...law.binders.map((b) => b.raw), ...law.exs, ...law.claimLines]) {
        const hit = /\binternal_[A-Za-z0-9_]*/.exec(s);
        if (hit) at(m, law.line, `law '${law.name}' names internal helper '${hit[0]}' in its public statement`);
      }
    }
    if (!law.name.startsWith("internal_") && law.doc.length === 0) at(m, law.line, `law '${law.name}' has no '#' doc line above it`);
    if (law.claimLines.length !== 1) at(m, law.line, `law '${law.name}' must have exactly one claim line (found ${law.claimLines.length})`);
    if (!law.proof) at(m, law.line, `law '${law.name}' has no 'def ${law.name}(...)' proof directly after it`);
  }
  for (const line of m.stray) at(m, line, "a law must be a column-0 'law name:' block (bend accepts other forms the tools cannot read)");
  for (const d of m.defs) {
    if (!NAME.test(d.name)) at(m, d.line, `def name '${d.name}' must be lowercase snake_case without dots`);
    if (!d.name.startsWith("internal_") && isPredicate(d)) {
      if (d.doc.length === 0) at(m, d.line, `predicate '${d.name}' has no '#' doc line above it`);
      const body = d.body.filter((l) => l.trim() !== "");
      if (body.length !== 1 && !kernel) at(m, d.line, `predicate '${d.name}' must have a one-line body`);
      const text = body.join(" ");
      if (/\bmatch\b/.test(text) && !kernel) at(m, d.line, `predicate '${d.name}' must not match (it would be nominal across versions)`);
      // A predicate may call its own template parameters (`~le`, `~eq`): they are substituted
      // by the caller with a closed term, so the body stays a plain application of Base.
      const templates = new Set([...d.header.matchAll(/~([A-Za-z_][A-Za-z0-9_]*)\s*:/g)].map((t) => t[1]));
      // A lambda's parameters (`+x => k => m => ...`) are locally bound, so a call to one
      // (`k(Some{x})`) is not a non-Base function reference.
      const lambdas = new Set([...text.matchAll(/([A-Za-z_][A-Za-z0-9_]*)\s*=>/g)].map((b) => b[1]));
      const own = new Set([...m.defs.map((x) => x.name), ...m.laws.map((x) => x.name)]);
      const localAliases = new Set(m.imports.filter((i) => !isHubImport(i.path)).map((i) => i.alias));
      const samePackage = (id: string) => kernel && (own.has(id) || localAliases.has(id.split(".")[0]));
      for (const call of text.matchAll(/([A-Za-z_][A-Za-z0-9_.]*)\s*\(/g)) {
        const fn = call[1];
        if (!base.has(fn) && !templates.has(fn) && !lambdas.has(fn) && !samePackage(fn)) at(m, d.line, `predicate '${d.name}' calls '${fn}', which is not a Base function`);
      }
      // A non-Base def passed without a call (`~MNat.le`, `~helper`) is just as nominal.
      for (const ref of text.matchAll(/(?<![A-Za-z0-9_.])([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+|[a-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_.]*\s*\()/g)) {
        const id = ref[1];
        const foreign = id.includes(".") ? !base.has(id) && !/^[A-Z]/.test(id.split(".").pop()!) : own.has(id);
        if (foreign && !samePackage(id) && !lambdas.has(id)) at(m, d.line, `predicate '${d.name}' refers to '${id}', which is not a Base function`);
      }
    }
  }
  if (!allowTypes) for (const t of m.types) at(m, t.line, `type '${t.name}': bend-mathlib holds no datatypes (use a kernel package)`);
}

if (doErasure) {
  // One scratch copy of the package; for each candidate, overwrite the module with
  // one binder erased, re-check, then restore the original text (nothing is deleted).
  const dir = mkdtempSync(join(tmpdir(), "bendlib-erasure-"));
  cpSync(pkg, dir, { recursive: true });
  const check = (target: string) => {
    const p = Bun.spawnSync([BEND, target, "--check-only"], { cwd: dir, env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
    return (new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).trim();
  };
  for (const m of mods) {
    const lines = m.text.split("\n");
    const target = join(dir, relative(pkg, m.file));
    // A failed mutant reads as "not erasable", so a module that fails unmodified would pass silently.
    let baseline: string | undefined;
    for (const law of m.laws) {
      for (const b of law.binders) {
        if (b.mark === "-" || b.mark === "~" || /^(Type|Data|Kind\b)/.test(b.type)) continue;
        const idx = lines.findIndex((l, i) => i >= law.line && l.trim() === b.raw);
        if (idx < 0) continue;
        baseline ??= check(target);
        if (baseline !== CLEAN) continue;
        const mutated = lines.slice();
        mutated[idx] = mutated[idx].replace(/for\s+[+]?/, "for -");
        mkdirSync(dirname(target), { recursive: true });
        writeFileSync(target, mutated.join("\n"));
        const out = check(target);
        writeFileSync(target, m.text);
        if (out === CLEAN) at(m, idx + 1, `binder '${b.name}' of '${law.name}' can be erased (write 'for -${b.name}')`);
      }
    }
    if (baseline !== undefined && baseline !== CLEAN) {
      at(m, 1, `erasure not checked: the unmodified module fails in the scratch copy:\n${baseline.split("\n").slice(0, 4).join("\n")}`);
    }
  }
}

for (const f of findings) console.log(f);
console.log(`${findings.length} finding(s) in ${mods.length} module(s)${doErasure ? " (erasure checked)" : ""}`);
process.exit(findings.length === 0 ? 0 : 1);
