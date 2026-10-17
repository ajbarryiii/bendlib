// check: every module of a package must check with EXACTLY the clean verdict (CLEAN)
// on the pinned compiler, contain no unsafe code and no holes, and stay under a
// wall-time ceiling.
//
// usage: bun tools/mathlib/check.ts [packages/bend-mathlib] [--json] [--max-seconds N]
// exit: 0 all green · 1 findings · 2 usage/toolchain error

import { readFileSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { BEND, CLEAN, PkgError, ROOT, packageModules, stripCommentsAndStrings } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/check.ts [packages/bend-mathlib] [--json] [--max-seconds N]";
const usage = (msg: string): never => { console.error(`check: ${msg}\n${USAGE}`); process.exit(2); };

const args = process.argv.slice(2);
const json = args.includes("--json");
const maxIdx = args.indexOf("--max-seconds");
const maxSeconds = maxIdx >= 0 ? Number(args[maxIdx + 1]) : 10;
if (!Number.isInteger(maxSeconds) || maxSeconds <= 0) usage(`--max-seconds needs a positive integer, got ${JSON.stringify(args[maxIdx + 1] ?? null)}`);
const pkg = resolve(args.find((a, i) => !a.startsWith("--") && args[i - 1] !== "--max-seconds") ?? join(ROOT, "packages", "bend-mathlib"));

const pinned = JSON.parse(readFileSync(join(ROOT, "toolchain.json"), "utf8")).bend.version as string;
let ver = "";
try { ver = new TextDecoder().decode(Bun.spawnSync([BEND, "version"]).stdout).trim(); } catch { /* no compiler: reported below */ }
if (ver !== `bend ${pinned}`) {
  console.error(`toolchain mismatch: toolchain.json pins ${pinned}, ${BEND} reports "${ver}"`);
  process.exit(2);
}

type Row = { module: string; ok: boolean; seconds: number; output: string; problems: string[] };
const rows: Row[] = [];
let files: string[];
try { files = packageModules(pkg); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
for (const file of files) {
  const problems: string[] = [];
  const src = stripCommentsAndStrings(readFileSync(file, "utf8"));
  if (/@unsafe/.test(src)) problems.push("contains @unsafe");
  if (/^def\s+\w+\?\s*\(/m.test(src)) problems.push("contains an unsafe `def f?(`");
  if (/(^|[\s(,])\?[A-Za-z_]/m.test(src)) problems.push("contains a ?hole");
  const t0 = performance.now();
  const p = Bun.spawnSync([BEND, file, "--check-only"], { cwd: pkg, env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  const seconds = (performance.now() - t0) / 1000;
  const output = (new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).trim();
  if (output !== CLEAN) problems.push(`checker output is not exactly ${JSON.stringify(CLEAN)}`);
  if (p.exitCode !== 0) problems.push(`exit code ${p.exitCode}`);
  if (seconds > maxSeconds) problems.push(`took ${seconds.toFixed(2)}s > ${maxSeconds}s ceiling`);
  rows.push({ module: relative(ROOT, file), ok: problems.length === 0, seconds, output, problems });
}

if (json) console.log(JSON.stringify({ compiler: ver, rows }, null, 2));
else {
  for (const r of rows) {
    console.log(`${r.ok ? "ok  " : "FAIL"} ${r.module.padEnd(40)} ${r.seconds.toFixed(2)}s`);
    if (!r.ok) { for (const pr of r.problems) console.log(`       - ${pr}`); console.log(r.output.split("\n").map((l) => "       | " + l).join("\n")); }
  }
  console.log(`${rows.filter((r) => r.ok).length}/${rows.length} modules green on ${ver}`);
}
process.exit(rows.length > 0 && rows.every((r) => r.ok) ? 0 : 1);
