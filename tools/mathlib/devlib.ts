// devlib: resolve local packages under `packages/` by their real publish hash, so sources can
// `import 0x…/file.bend` against a not-yet-published local package in dev mode (PLAN §3.5).
//
// `.devlib/` is rebuilt from empty on every run (git-ignored): each `<hash>` is a symlink to the
// package directory; the child gets `BEND_LIB=<root>/.devlib`, and bend fetches any other hash
// from the hub into the same directory, so hub imports keep resolving. `--check` fails when a
// package source pins a `0x…` that names a local package whose current content hash differs.
//
// usage: bun tools/mathlib/devlib.ts [--root <dir>] run -- <cmd…>
//        bun tools/mathlib/devlib.ts [--root <dir>] --check
// exit: run → the child's code · --check → 0 clean · 1 stale/malformed pin · 2 usage

import { existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, symlinkSync } from "node:fs";
import { join, relative, resolve, sep } from "node:path";
import { PkgError, ROOT, importPaths, packageModules } from "./lib.ts";
import { hubHash, packageFiles } from "./hash.ts";

const USAGE = "usage: bun tools/mathlib/devlib.ts [--root <dir>] run -- <cmd…>  |  [--root <dir>] --check";
const usage = (msg: string): never => { console.error(`devlib: ${msg}\n${USAGE}`); process.exit(2); };

const HASH = /^0x[0-9a-f]{32}$/;
const HASH_IMPORT = /^(0x[0-9a-fA-F]+)\/(\S+\.bend)$/;

export type LocalPackage = { name: string; dir: string; entry: string; hash: string; files: string[] };
export type Stale = { file: string; hash: string; path: string; owner: string; expected: string };

/** The publish entry of `pkgDir`: `all.bend`, or the sole top-level `.bend` file. */
function entryOf(pkgDir: string): string | null {
  const all = join(pkgDir, "all.bend");
  if (existsSync(all)) return all;
  const top = readdirSync(pkgDir, { withFileTypes: true })
    .filter((e) => e.isFile() && e.name.endsWith(".bend"))
    .map((e) => join(pkgDir, e.name)).sort();
  if (top.length === 0) return null;
  if (top.length === 1) return top[0];
  throw new PkgError(`${pkgDir}: multiple top-level .bend files and no all.bend; cannot choose an entry`);
}

/** Every `packages/<name>/` with an entry, keyed by its real content hash (hubHash over packageFiles). */
export function findLocalPackages(root: string): LocalPackage[] {
  const pkgs = join(root, "packages");
  if (!existsSync(pkgs)) return [];
  const out: LocalPackage[] = [];
  for (const e of readdirSync(pkgs, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
    if (!e.isDirectory()) continue;
    const dir = realpathSync(join(pkgs, e.name));
    const entry = entryOf(dir);
    if (entry === null) continue;
    let files: Record<string, string>;
    try { files = packageFiles(entry); } catch (err) { if (err instanceof PkgError) throw new PkgError(`packages/${e.name}: ${err.message}`); throw err; }
    out.push({ name: e.name, dir, entry, hash: hubHash(files), files: Object.keys(files) });
  }
  return out;
}

/** Rebuild `<root>/.devlib` with one `<hash>` symlink per local package. Returns the packages. */
export function buildDevlib(root: string): { dir: string; packages: LocalPackage[] } {
  let st;
  try { st = statSync(root); } catch { throw new PkgError(`no such directory: ${root}`); }
  if (!st.isDirectory()) throw new PkgError(`not a directory: ${root}`);
  const rootReal = realpathSync(root);
  const dir = join(rootReal, ".devlib");
  if (!dir.startsWith(rootReal + sep)) throw new PkgError(`refusing to write ${dir} outside the repo ${rootReal}`);
  if (existsSync(dir) && lstatSync(dir).isSymbolicLink()) throw new PkgError(`refusing to rebuild a symlinked .devlib (${dir})`);
  const packages = findLocalPackages(rootReal);
  rmSync(dir, { recursive: true, force: true });
  mkdirSync(dir, { recursive: true });
  const byHash = new Map<string, LocalPackage>();
  for (const p of packages) {
    if (!HASH.test(p.hash)) throw new PkgError(`${p.name}: content hash ${p.hash} is not 32 hex`);
    const clash = byHash.get(p.hash);
    if (clash) throw new PkgError(`content hash ${p.hash} is shared by ${clash.name} and ${p.name}`);
    byHash.set(p.hash, p);
    symlinkSync(p.dir, join(dir, p.hash), "dir");
  }
  return { dir, packages };
}

/** The `0x…/path.bend` pins in a package's modules, in file order. */
export function hashPins(pkgDir: string): { file: string; hash: string; path: string }[] {
  const out: { file: string; hash: string; path: string }[] = [];
  for (const file of packageModules(pkgDir)) {
    for (const p of importPaths(readFileSync(file, "utf8"))) {
      const m = HASH_IMPORT.exec(p);
      if (m) out.push({ file, hash: m[1], path: m[2] });
    }
  }
  return out;
}

/** A pin is stale when its path lives in other local packages and the pin is none of their hashes. */
export function staleDevlib(packages: LocalPackage[]): Stale[] {
  const stale: Stale[] = [];
  for (const p of packages) {
    for (const pin of hashPins(p.dir)) {
      if (!HASH.test(pin.hash)) { stale.push({ ...pin, owner: "", expected: "" }); continue; }
      const candidates = packages.filter((q) => q.dir !== p.dir && existsSync(join(q.dir, pin.path)));
      if (candidates.length === 0 || candidates.some((q) => q.hash === pin.hash)) continue;
      stale.push({ ...pin, owner: candidates.map((q) => q.name).join(" or "), expected: candidates.map((q) => q.hash).join(" or ") });
    }
  }
  return stale;
}

/** Rebuild `.devlib` from empty and report every local package plus every stale/malformed pin. */
export function checkDevlib(root: string): { dir: string; packages: LocalPackage[]; stale: Stale[] } {
  const { dir, packages } = buildDevlib(root);
  return { dir, packages, stale: staleDevlib(packages) };
}

/** Rebuild `.devlib`, run `cmd` with `BEND_LIB` pointed at it, echo its output, and return its code. */
export function runDevlib(root: string, cmd: string[]): { code: number; out: string } {
  const { dir } = buildDevlib(root);
  const p = Bun.spawnSync(cmd, { env: { ...process.env, BEND_LIB: dir }, stdin: "inherit", stdout: "pipe", stderr: "pipe" });
  const out = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
  process.stdout.write(new TextDecoder().decode(p.stdout));
  process.stderr.write(new TextDecoder().decode(p.stderr));
  return { code: p.exitCode ?? 1, out };
}

if (import.meta.main) {
  const args = process.argv.slice(2);
  const rootIdx = args.indexOf("--root");
  let rootOverride: string | undefined;
  if (rootIdx >= 0) {
    rootOverride = args[rootIdx + 1];
    if (rootOverride === undefined || rootOverride.startsWith("--")) usage("--root needs a directory");
    args.splice(rootIdx, 2);
  }
  const root = resolve(rootOverride ?? ROOT);
  if (args[0] === "--check") {
    let built: { dir: string; packages: LocalPackage[]; stale: Stale[] };
    try { built = checkDevlib(root); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
    for (const p of built.packages) console.log(`local  ${p.name}  ${p.hash}  (${p.files.length} files)`);
    for (const s of built.stale) {
      if (s.owner === "") console.log(`FAIL  ${relative(root, s.file)}: ${s.hash} is not 32 hex`);
      else console.log(`FAIL  ${relative(root, s.file)}: ${s.hash}/${s.path} is stale; local package ${s.owner} now hashes to ${s.expected}`);
    }
    console.log(`${built.packages.length} local package(s), ${built.stale.length} finding(s)`);
    process.exit(built.stale.length === 0 ? 0 : 1);
  }
  if (args[0] === "run" && args[1] === "--" && args.length > 2) {
    try { process.exit(runDevlib(root, args.slice(2)).code); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
  }
  usage("need `run -- <cmd…>` or `--check`");
}
