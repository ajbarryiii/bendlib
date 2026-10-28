// release: run every gate (`bend --verdict` on each module needs Lean v4.34.0 on PATH), compute the
// package's hub hash, publish anonymously, verify the uploaded content from an empty cache, then
// attach the name (PLAN.md §3.5).
//
// usage: bun tools/mathlib/release.ts <pkgdir> <name> <version> [--publish]
//   without --publish: gates + expected hash + the exact commands (dry run)
//   with --publish: also publishes, verifies, links the name, freezes the lock, updates RELEASES.md,
//   regenerates the package README for the released version
// exit: 0 ok · 1 a gate or verification failed · 2 usage

import { appendFileSync, existsSync, mkdtempSync, readdirSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { join, relative, basename, resolve } from "node:path";
import { BEND, CLEAN, PkgError, ROOT, packageModules } from "./lib.ts";
import { hubHash, packageFiles } from "./hash.ts";

const USAGE = "usage: release.ts <pkgdir> <name(1-64 chars)> <a.b.c.d> [--publish]";
const usage = (msg: string): never => { console.error(`release: ${msg}\n${USAGE}`); process.exit(2); };
const sh = (cmd: string[], extra: Record<string, string> = {}) => {
  const p = Bun.spawnSync(cmd, { cwd: ROOT, env: { ...process.env, BEND_NO_TELEMETRY: "1", ...extra } });
  return { code: p.exitCode, out: (new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).trim() };
};
const fail = (msg: string): never => { console.error(`release: ${msg}`); process.exit(1); };

// bend reads BEND_HUB and its key file; read them per call so a test can point both away.
const hubUrl = () => process.env.BEND_HUB ?? "https://hub.bend-lang.com";
const bendBin = () => process.env.BEND_CLI ?? BEND;
// bend >= 2.0.36 keeps the key in bendai.json and moves an older bender.json there on its next hub call.
const keyFiles = () => ["bendai.json", "bender.json"].map((f) => join(process.env.HOME ?? homedir(), ".bend", f));
// The ledger is repo-root state; the override lets the publish-path test run off-tree.
const releasesFile = () => process.env.BENDLIB_RELEASES ?? join(ROOT, "RELEASES.md");

// The first line is the hub description and part of the permanent hash, so it must name the
// version being released; a stale `name@<v>` there would freeze the wrong description forever.
export function headerVersionError(pkg: string, name: string, version: string): string | null {
  const entry = join(pkg, "all.bend");
  if (!existsSync(entry)) return null;
  const first = readFileSync(entry, "utf8").split("\n", 1)[0] ?? "";
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`(?:^|[^A-Za-z0-9-])${escaped}@(\\d+\\.\\d+\\.\\d+\\.\\d+)`, "g");
  const wrong = [...first.matchAll(re)].map((m) => m[1]).find((v) => v !== version);
  return wrong ? `${relative(ROOT, entry)}:1 names ${name}@${wrong}; the release target is ${name}@${version}` : null;
}

/** Why `BEND_LIB` would let a hub import resolve to local files (devlib's symlinks), else null. */
export function devlibError(bendLib: string | undefined): string | null {
  if (bendLib === undefined || bendLib === "") return null;
  const real = (p: string) => { try { return realpathSync(p); } catch { return resolve(p); } };
  // Under such a BEND_LIB a hub import loads as a local file outside the entry's directory, which bend
  // refuses to publish (2.0.39 main.ts:857-862; before 2.0.39 it bundled it), but only after every gate ran.
  const refuse = (why: string) => `BEND_LIB=${bendLib} ${why}; a publish would take its hub imports for local files outside the package. Run release.ts directly, not through devlib (its gates fetch hub imports themselves)`;
  if (real(bendLib) === real(join(ROOT, ".devlib"))) return refuse("is the devlib directory");
  let entries;
  try { entries = readdirSync(bendLib, { withFileTypes: true }); } catch { return null; }
  const link = entries.find((e) => e.isSymbolicLink());
  return link ? refuse(`holds the symlink ${link.name}`) : null;
}

/** Regenerate the package README for `version`; run after `lock --freeze` so its since cells are final. */
export function regenerateIndex(pkg: string, name: string, version: string) {
  return sh([process.execPath, "tools/mathlib/index.ts", pkg, name, version]);
}

/** bend's stored key; without one, `bend link` starts an interactive login and hangs under spawnSync. */
export function loginError(): string | null {
  for (const file of keyFiles()) {
    try {
      const key = (JSON.parse(readFileSync(file, "utf8")) as { key?: unknown }).key;
      if (typeof key === "string" && key !== "") return null;
    } catch {}
  }
  return "not logged in (no key in ~/.bend/bendai.json or ~/.bend/bender.json): run `bend login`";
}

/** Why `bend <module> --verdict` (the proven kernel, PLAN F35) is not exactly ALL PROOFS CHECK, else null. */
export function verdictError(module: string): string | null {
  const r = sh([bendBin(), module, "--verdict"]);
  return r.code === 0 && r.out === "ALL PROOFS CHECK" ? null : `${relative(ROOT, module)} (exit ${r.code}):\n${r.out}`;
}

/** Publish, verify from an empty cache, link the name, freeze the lock, regenerate README, record it. */
export async function publish(pkg: string, name: string, version: string, expected: string): Promise<string> {
  const pub = sh([bendBin(), join(pkg, "all.bend"), "--publish"]);
  const got = pub.out.match(/^(0x[0-9a-f]{32})$/m)?.[1];
  if (!got) throw new Error(`publish did not print a hash:\n${pub.out}`);
  if (got !== expected) throw new Error(`hub hash ${got} differs from the locally computed ${expected}`);
  console.log(`published ${got}`);

  const lib = mkdtempSync(join(tmpdir(), "bendlib-verify-"));
  const probe = join(lib, "probe.bend");
  writeFileSync(probe, `import Base\nimport ${got}/all.bend as P\n`);
  const v = sh([bendBin(), probe, "--check-only"], { BEND_LIB: join(lib, "lib") });
  if (v.out !== CLEAN) throw new Error(`fresh-cache verification of ${got} failed:\n${v.out}`);
  console.log("verified from an empty cache");

  const link = sh([bendBin(), "link", `${name}@${version}`, got]);
  if (link.code !== 0) throw new Error(`bend link failed:\n${link.out}`);
  const named = (await (await fetch(`${hubUrl()}/name/${name}@${version}`)).text()).trim();
  if (named !== got) throw new Error(`hub resolves ${name}@${version} to ${named}, expected ${got}`);
  console.log(`linked ${name}@${version} -> ${got}`);

  const freeze = sh([process.execPath, "tools/mathlib/lock.ts", pkg, "--freeze", version]);
  if (freeze.code !== 0) throw new Error(`lock freeze failed:\n${freeze.out}`);
  // freeze rewrites the lock's since cells, so the README is only correct after this step.
  const idx = regenerateIndex(pkg, name, version);
  if (idx.code !== 0) throw new Error(`index regeneration for ${version} failed:\n${idx.out}`);
  const compiler = sh([bendBin(), "version"]).out;
  const ledger = releasesFile();
  if (!existsSync(ledger)) writeFileSync(ledger, "# Releases\n\n| package | version | hash | compiler | date |\n|---|---|---|---|---|\n");
  appendFileSync(ledger, `| ${name} | ${version} | \`${got}\` | ${compiler} | ${new Date().toISOString().slice(0, 10)} |\n`);
  return got;
}

async function main(): Promise<void> {
  const [pkgArg, name, version] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
  const doPublish = process.argv.includes("--publish");
  if (!pkgArg || !/^[a-z][a-z0-9-]{0,63}$/.test(name ?? "") || !/^\d+\.\d+\.\d+\.\d+$/.test(version ?? "")) {
    usage("need <pkgdir> <name(1-64 chars)> <a.b.c.d>");
  }
  const pkg = resolve(pkgArg);
  if (!existsSync(pkg)) {
    console.error(`release: package directory ${pkg} does not exist`);
    process.exit(1);
  }
  const devlib = devlibError(process.env.BEND_LIB);
  if (devlib) usage(devlib);
  const header = headerVersionError(pkg, name, version);
  if (header) fail(header);
  if (doPublish) {
    const login = loginError();
    if (login) fail(login);
  }

  const gates: [string, string[]][] = [
    ["check", [process.execPath, "tools/mathlib/check.ts", pkg]],
    ["lint", [process.execPath, "tools/mathlib/lint.ts", pkg, "--erasure"]],
    ["twins", [process.execPath, "tools/mathlib/twins.ts", pkg, "--check"]],
    ["comments", [process.execPath, "tools/comments.ts", ...["packages", "tools"].map((d) => join(ROOT, d))]],
    ["lock", [process.execPath, "tools/mathlib/lock.ts", pkg, "--check"]],
  ];
  for (const m of packageModules(pkg)) {
    gates.push(["lawcheck " + basename(m, ".bend"), [process.execPath, "tools/lawcheck/cli.ts", m, "--max-instances", "100", "--strict", "--allow-skip", "algebra.foldl_eq_foldr,algebra.foldl_eq_foldr_sym,algebra.foldl_op_eq_foldr_op,algebra.foldl_op_eq_foldr_op_sym,algebra.op_assoc4,algebra.op_assoc4_sym,algebra.op_comm3,algebra.op_comm3_sym,algebra.op_four,algebra.op_four_sym,algebra.op_left_comm,algebra.op_left_comm_sym,algebra.op_right_comm,algebra.op_right_comm_sym,bool.eq_true_of_ne_false,equal.cong2,equal.subst,list.sorted_append,maybe.maybe_bind_assoc,maybe.maybe_bind_assoc_sym,maybe.maybe_bind_map,maybe.maybe_bind_map_sym,maybe.maybe_map_bind,maybe.maybe_map_bind_sym,maybe.maybe_map_compose,maybe.maybe_map_compose_sym,maybe.maybe_map_pure,maybe.maybe_map_pure_sym,maybe.maybe_pure_bind,maybe.maybe_pure_bind_sym,nat.le_total,nat.le_total_d,order.le_antisymm_eq,order.le_total_of_not_le,order.le_total_true,order.le_total_true_sym,order.le_trans3,order.le_trans4,u32.u32_sub_wrap,u32.u32_sub_wrap_sym"]]);
  }
  for (const [label, cmd] of gates) {
    const r = sh(cmd);
    console.log(`${r.code === 0 ? "ok  " : "FAIL"} ${label}`);
    if (r.code !== 0) fail(`${label} gate failed:\n${r.out}`);
  }
  const entry = join(pkg, "all.bend");
  let files: Record<string, string>;
  try { files = packageFiles(entry); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
  for (const m of packageModules(pkg)) {
    const err = verdictError(m);
    console.log(`${err ? "FAIL" : "ok  "} verdict ${basename(m, ".bend")}`);
    if (err) fail(`verdict gate failed (--verdict needs Lean v4.34.0 on PATH):\n${err}`);
  }

  const expected = hubHash(files);
  console.log(`expected hash ${expected} (${Object.keys(files).length} files)`);
  const taken = await fetch(`${hubUrl()}/name/${name}@${version}`);
  if (taken.ok) fail(`${name}@${version} already exists on the hub`);

  if (!doPublish) {
    console.log(`dry run. commands:\n  bend ${relative(ROOT, entry)} --publish\n  bend link ${name}@${version} ${expected}`);
    return;
  }
  try {
    const got = await publish(pkg, name, version, expected);
    console.log(`regenerated ${relative(ROOT, join(pkg, "README.md"))}; recorded in ${relative(ROOT, releasesFile())}; tag with: git tag ${name}-v${version} (${got})`);
  } catch (e) {
    fail(e instanceof Error ? e.message : String(e));
  }
}

if (import.meta.main) await main();
