// twins: generate `<name>_sym` twins for every public equational law.
//
// Bend's rewrite `%e : P` replaces the equation's RIGHT side with its LEFT side,
// so a Mathlib-style lemma `{big == simple}` expands, and its reversed twin
// `{simple == big}` simplifies (PLAN.md §3.1.6, fact F28). Twins are appended in
// a generated trailing section of the same module, proved by Equal.sym.
//
// usage: bun tools/mathlib/twins.ts [pkgdir] [--check]
//   default: rewrite each module's generated section in place
//   --check: exit 1 if any module's generated section is out of date (CI)

import { readFileSync, writeFileSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { GENERATED_MARK, PkgError, ROOT, packageModules, parseModule, splitEquation } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/twins.ts [pkgdir] [--check]";
const usage = (msg: string): never => { console.error(`twins: ${msg}\n${USAGE}`); process.exit(2); };

const args = process.argv.slice(2);
const pkg = resolve(args.find((a) => !a.startsWith("--")) ?? join(ROOT, "packages", "bend-mathlib"));
const check = args.includes("--check");
let stale = 0;

let files: string[];
try { files = packageModules(pkg); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
for (const file of files) {
  const text = readFileSync(file, "utf8");
  const cut = text.indexOf(GENERATED_MARK);
  const handwritten = (cut >= 0 ? text.slice(0, cut) : text).replace(/\s+$/, "") + "\n";
  // Parse only the handwritten part so twins are never twinned.
  const mod = parseModule(file, handwritten);
  const out: string[] = [];
  const twinned = new Set<string>();
  for (const law of mod.laws) {
    if (law.name.startsWith("internal_") || law.name.endsWith("_sym") || law.exs.length > 0 || !law.proof) continue;
    if (law.binders.some((b) => b.where) || law.claimLines.length !== 1) continue;
    // A twin of a conclusion drawn from hypotheses (succ_inj, le_antisymm) is permanent noise.
    if (law.binders.some((b) => b.type.startsWith("{") || /^([a-z_][A-Za-z0-9_.]*|[A-Z])\(/.test(b.type))) continue;
    const eq = splitEquation(law.claimLines[0]);
    if (!eq) continue;
    const params = law.binders.map((b) => b.name);
    const callArgs = law.binders.map((b) => (b.mark === "~" ? "~" : "") + b.name);
    out.push(
      `# ${(law.doc[0] ?? law.name).replace(/\.$/, "")}, reversed to rewrite toward the simple side.`,
      `law ${law.name}_sym:`,
      ...law.binders.map((b) => `  ${b.raw}`),
      `  {${eq.rhs} == ${eq.lhs} : ${eq.type}}`,
      ``,
      `def ${law.name}_sym(${params.join(", ")}):`,
      `  Equal.sym(${eq.type}, ${eq.lhs}, ${eq.rhs}, ${law.name}(${callArgs.join(", ")}))`,
      ``,
    );
    twinned.add(law.name);
  }
  // --verdict takes a ~ constant's model from a call of its law (PLAN F38), so each handwritten
  // `internal_` def that is one call of a twinned law with `~` arguments gets the twin's call.
  const calls: string[] = [];
  for (const d of mod.defs) {
    const body = d.body.map((l) => l.trim()).filter(Boolean);
    const head = /^def (internal_\w+)\((.*)\) -> (\{.*\}):$/.exec(d.header.trim());
    const call = body.length === 1 ? /^(\w+)\((~.*)\)$/.exec(body[0]!) : null;
    if (head === null || call === null || !twinned.has(call[1]!)) continue;
    const eq = splitEquation(head[3]!);
    if (!eq) continue;
    calls.push(`def ${head[1]}_sym(${head[2]}) -> {${eq.rhs} == ${eq.lhs} : ${eq.type}}:`, `  ${call[1]}_sym(${call[2]})`, ``);
  }
  if (calls.length) out.push(`# Calls of the twins, as the calls above the generated section make of their laws (PLAN F38).`, ...calls);
  // A module with no twins and no generated section is already up to date, even when byte-empty.
  const next = out.length === 0
    ? (cut < 0 ? text : handwritten)
    : handwritten + "\n" + GENERATED_MARK + "\n\n" + out.join("\n").replace(/\n+$/, "") + "\n";
  if (next !== text) {
    stale++;
    if (check) console.log(`stale: ${relative(ROOT, file)}`);
    else { writeFileSync(file, next); console.log(`updated: ${relative(ROOT, file)}`); }
  }
}
if (check && stale > 0) process.exit(1);
console.log(check ? "twins up to date" : `${stale} module(s) updated`);
