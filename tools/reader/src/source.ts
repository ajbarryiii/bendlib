// Locating the official Bend source (bend2/bend.ts) at the exact version of
// the installed compiler, and importing it.
//
// Rule: the reader parses with the bend.ts of the SAME version that
// `bend version` reports. The source comes from the GitHub tag archive
// refs/tags/v<version>, cached under ~/.cache/bendlib/bend/<version>/,
// or from a local checkout given by BENDLIB_BEND_SRC / {src}.
// For the pinned compiler, the file sha256s in toolchain.json are enforced on
// fetch and on every cache hit, and base.bend must match the installed one.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import toolchain from "../../../toolchain.json";

export const REPO = "bendlang/bend";

export class SourceError extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "SourceError";
  }
}

export type BendSource = {
  version: string;        // the version the source declares (main.ts VERSION)
  dir: string;            // the repo root (contains bend2/bend.ts)
  bendTs: string;         // absolute path to bend2/bend.ts
  origin: "cache" | "fetched" | "local";
  archiveSha256?: string; // sha256 of the tag archive (cache / fetched)
  commit?: string;        // commit the tag names, when GitHub's API answered on first fetch
};

function sha256(buf: Uint8Array | string): string {
  const h = new Bun.CryptoHasher("sha256");
  h.update(buf);
  return h.digest("hex");
}

export function cacheRoot(): string {
  return process.env.BENDLIB_CACHE ?? path.join(os.homedir(), ".cache", "bendlib");
}

const TOOLCHAIN = toolchain as {
  bend: { version: string; source?: { commit?: string; files?: Record<string, string> } };
};

let warnedUntested = false;

// A newer compiler is fine to read, but its output is unverified until the pin moves.
function warnUntested(version: string): void {
  if (warnedUntested || version === TOOLCHAIN.bend.version) return;
  warnedUntested = true;
  console.error(`reader: bend ${version} is untested with @bendlib/reader (tested: ${TOOLCHAIN.bend.version})`);
}

// A manifest is attacker-writable, so the pinned hashes in toolchain.json are the source of truth.
function verifyPinned(dir: string, version: string, label: string): void {
  if (version !== TOOLCHAIN.bend.version) return;
  for (const [f, h] of Object.entries(TOOLCHAIN.bend.source?.files ?? {})) {
    const p = path.join(dir, f);
    const g = fs.existsSync(p) ? sha256(fs.readFileSync(p)) : "<missing>";
    if (g !== h) {
      throw new SourceError(`${label} ${p} has sha256 ${g}, does not match the pinned sha256 ${h}`);
    }
  }
}

function resolveBend(bin?: string): { path: string; version: string } {
  const cands = [bin, process.env.BEND_BIN, path.join(os.homedir(), ".bend", "bin", "bend"), "bend"]
    .filter((x): x is string => typeof x === "string" && x !== "");
  const errs: string[] = [];
  for (const b of cands) {
    if (b.includes("/") && !fs.existsSync(b)) {
      errs.push(b + ": not found");
      continue;
    }
    try {
      const r = Bun.spawnSync([b, "version"], { stdout: "pipe", stderr: "pipe" });
      const out = r.stdout.toString().trim();
      const m = out.match(/^bend (\d+\.\d+\.\d+)$/);
      if (r.exitCode === 0 && m) {
        return { path: b.includes("/") ? path.resolve(b) : (Bun.which(b) ?? b), version: m[1] };
      }
      errs.push(b + ": unexpected output " + JSON.stringify(out + r.stderr.toString()));
    } catch (e) {
      errs.push(b + ": " + String(e));
    }
  }
  throw new SourceError("cannot determine the installed bend version (`bend version`):\n  " + errs.join("\n  "));
}

/** `bend version` of BEND_BIN, else ~/.bend/bin/bend, else `bend` on PATH, e.g. "2.0.37". */
export function installedVersion(bin?: string): string {
  return resolveBend(bin).version;
}

function installedVersionOrNull(bin?: string): string | null {
  try { return installedVersion(bin); } catch { return null; }
}

/** The `const VERSION` a bend checkout's bend2/main.ts declares. */
export function declaredVersion(dir: string): string {
  const main = path.join(dir, "bend2", "main.ts");
  if (!fs.existsSync(main)) {
    throw new SourceError("not a bend checkout (no bend2/main.ts): " + dir);
  }
  const m = fs.readFileSync(main, "utf8").match(/^const VERSION = "([^"]+)";$/m);
  if (!m) {
    throw new SourceError("no `const VERSION = \"...\"` in " + main);
  }
  return m[1];
}

// Files recorded in each manifest; for the pinned compiler verifyPinned enforces toolchain.json on top.
const PINNED = ["bend2/bend.ts", "bend2/main.ts", "bend2/base.bend"];

type Manifest = {
  version: string;
  tag: string;
  url: string;
  archive: string;
  archiveSha256: string;
  commit?: string;
  fetchedAt: string;
  files: Record<string, string>;
};

function verifyCache(vdir: string, version: string): BendSource {
  const manPath = path.join(vdir, "manifest.json");
  const man = JSON.parse(fs.readFileSync(manPath, "utf8")) as Manifest;
  const archive = path.join(vdir, man.archive);
  const shaFile = fs.readFileSync(path.join(vdir, "archive.sha256"), "utf8").trim().split(/\s+/)[0];
  if (shaFile !== man.archiveSha256) {
    throw new SourceError(`cache inconsistent: ${vdir}/archive.sha256 (${shaFile}) != manifest (${man.archiveSha256})`);
  }
  const got = sha256(fs.readFileSync(archive));
  if (got !== man.archiveSha256) {
    throw new SourceError(`cached archive ${archive} has sha256 ${got}, recorded ${man.archiveSha256}; remove ${vdir} to refetch`);
  }
  const dir = path.join(vdir, "src");
  for (const [f, h] of Object.entries(man.files)) {
    const g = sha256(fs.readFileSync(path.join(dir, f)));
    if (g !== h) {
      throw new SourceError(`cached ${dir}/${f} has sha256 ${g}, recorded ${h} at extraction; remove ${vdir} to refetch`);
    }
  }
  verifyPinned(dir, version, "cached");
  const dv = declaredVersion(dir);
  if (dv !== version) {
    throw new SourceError(`cached source declares VERSION ${dv}, expected ${version}`);
  }
  return { version, dir, bendTs: path.join(dir, "bend2", "bend.ts"), origin: "cache", archiveSha256: man.archiveSha256, commit: man.commit };
}

async function fetchTag(vdir: string, version: string): Promise<BendSource> {
  const tag = "v" + version;
  const url = `https://github.com/${REPO}/archive/refs/tags/${tag}.tar.gz`;
  const res = await fetch(url, { redirect: "follow" }).catch((e) => {
    throw new SourceError(`cannot fetch ${url}: ${String(e)} (offline? set BENDLIB_BEND_SRC to a local checkout)`);
  });
  if (!res.ok) {
    throw new SourceError(`tag ${tag} not available: GET ${url} -> HTTP ${res.status} (set BENDLIB_BEND_SRC to a local checkout at ${tag})`);
  }
  const buf = new Uint8Array(await res.arrayBuffer());
  const archiveSha256 = sha256(buf);
  // the commit the tag names (best effort: the unauthenticated API is rate limited)
  let commit: string | undefined;
  try {
    const r = await fetch(`https://api.github.com/repos/${REPO}/git/ref/tags/${tag}`);
    if (r.ok) {
      const j = (await r.json()) as { object?: { sha?: string; type?: string } };
      commit = j.object?.type === "commit" ? j.object.sha : undefined;
    }
  } catch { /* recorded as absent */ }
  if (version === TOOLCHAIN.bend.version && TOOLCHAIN.bend.source?.commit !== undefined && commit !== undefined && commit !== TOOLCHAIN.bend.source.commit) {
    throw new SourceError(`tag ${tag} names commit ${commit}, pinned commit is ${TOOLCHAIN.bend.source.commit}`);
  }

  fs.mkdirSync(path.dirname(vdir), { recursive: true });
  const tmp = fs.mkdtempSync(path.join(path.dirname(vdir), `.${version}.tmp-`));
  let moved = false;
  try {
    const archiveName = `${tag}.tar.gz`;
    fs.writeFileSync(path.join(tmp, archiveName), buf);
    fs.mkdirSync(path.join(tmp, "src"));
    // only bend2/ is read (bend.ts, base.bend, effs/); bench/ and media/ are ~69 MB of the archive
    const tar = Bun.spawnSync(["tar", "-xzf", path.join(tmp, archiveName), "-C", path.join(tmp, "src"),
      "--strip-components=1", "--wildcards", "*/bend2/*"], { stdout: "pipe", stderr: "pipe" });
    if (tar.exitCode !== 0) {
      throw new SourceError(`tar failed on ${url}: ${tar.stderr.toString()}`);
    }
    const dv = declaredVersion(path.join(tmp, "src"));
    if (dv !== version) {
      throw new SourceError(`${url} declares VERSION ${dv} in bend2/main.ts, expected ${version}`);
    }
    const files: Record<string, string> = {};
    for (const f of PINNED) {
      files[f] = sha256(fs.readFileSync(path.join(tmp, "src", f)));
    }
    verifyPinned(path.join(tmp, "src"), version, "fetched");
    const man: Manifest = { version, tag, url, archive: archiveName, archiveSha256, commit, fetchedAt: new Date().toISOString(), files };
    fs.writeFileSync(path.join(tmp, "manifest.json"), JSON.stringify(man, null, 2) + "\n");
    fs.writeFileSync(path.join(tmp, "archive.sha256"), `${archiveSha256}  ${archiveName}\n`);
    if (fs.existsSync(vdir)) {
      // another process won the race; use theirs, the finally removes ours
      return verifyCache(vdir, version);
    }
    try {
      fs.renameSync(tmp, vdir);
    } catch (e) {
      const code = (e as { code?: string }).code;
      if (code === "ENOTEMPTY" || code === "EEXIST") {
        return verifyCache(vdir, version); // a concurrent winner appeared between the check and the rename
      }
      throw e;
    }
    moved = true;
    const dir = path.join(vdir, "src");
    return { version, dir, bendTs: path.join(dir, "bend2", "bend.ts"), origin: "fetched", archiveSha256, commit };
  } finally {
    if (!moved) {
      try { fs.rmSync(tmp, { recursive: true, force: true }); } catch { /* best effort */ }
    }
  }
}

export type SourceOptions = {
  version?: string; // default: the installed compiler's version
  src?: string;     // local checkout; default: env BENDLIB_BEND_SRC
  bin?: string;     // bend binary used for `bend version`
};

// The release ships base.bend next to the binary; the fetched copy must be byte-identical.
function verifyAgainstInstalled(dir: string, bin?: string): void {
  let installed: string;
  try {
    installed = path.join(path.dirname(resolveBend(bin).path), "..", "bend2", "base.bend");
  } catch {
    return; // no binary to compare against
  }
  const fetched = path.join(dir, "bend2", "base.bend");
  if (!fs.existsSync(installed) || !fs.existsSync(fetched)) return;
  if (!fs.readFileSync(fetched).equals(fs.readFileSync(installed))) {
    throw new SourceError(`${fetched} differs from the installed compiler's ${installed} (not the pinned release)`);
  }
}

/** The bend source at the installed compiler's version: local checkout (must declare that VERSION), verified cache, or tag fetch. */
export async function bendSource(opts: SourceOptions | string = {}): Promise<BendSource> {
  const o: SourceOptions = typeof opts === "string" ? { version: opts } : opts;
  const version = o.version ?? installedVersion(o.bin);
  warnUntested(version);
  const local = o.src ?? process.env.BENDLIB_BEND_SRC;
  if (local !== undefined && local !== "") {
    const dir = path.resolve(local);
    const dv = declaredVersion(dir);
    if (dv !== version) {
      throw new SourceError(`local bend source ${dir} declares VERSION ${dv}, but the version wanted is ${version}`);
    }
    return { version, dir, bendTs: path.join(dir, "bend2", "bend.ts"), origin: "local" };
  }
  const vdir = path.join(cacheRoot(), "bend", version);
  const s = fs.existsSync(path.join(vdir, "manifest.json"))
    ? verifyCache(vdir, version)
    : await fetchTag(vdir, version);
  // Only the installed version can be compared with the installed compiler's Base.
  if (o.version === undefined || o.version === installedVersionOrNull(o.bin)) verifyAgainstInstalled(s.dir, o.bin);
  return s;
}

/** The source pin for a compiler version: the tag's commit (best effort) and the sha256 of each pinned file. */
export async function sourcePin(opts: SourceOptions | string = {}): Promise<{ version: string; commit?: string; files: Record<string, string> }> {
  const s = await bendSource(opts);
  const files: Record<string, string> = {};
  for (const f of PINNED) files[f] = sha256(fs.readFileSync(path.join(s.dir, f)));
  return { version: s.version, commit: s.commit, files };
}

// bend.ts reads BEND_LIB/BEND_HUB once, at module evaluation, so each distinct
// pair gets its own module instance (a query-string import).
const instances = new Map<string, Promise<any>>();
let chain: Promise<unknown> = Promise.resolve(); // serializes env-dependent module evaluation

/** Imports <src>/bend2/bend.ts with the given BEND_LIB/BEND_HUB (defaults: the environment). */
export function importBend(src: BendSource, env: { bendLib?: string; bendHub?: string } = {}): Promise<any> {
  const lib = env.bendLib === undefined ? (process.env.BEND_LIB ?? "") : path.resolve(env.bendLib);
  const hub = env.bendHub ?? process.env.BEND_HUB ?? "";
  const key = `${src.bendTs}\0${lib}\0${hub}`;
  let inst = instances.get(key);
  if (inst === undefined) {
    const q = `?bendlib=${encodeURIComponent(lib)}&hub=${encodeURIComponent(hub)}`;
    const set = (k: "BEND_LIB" | "BEND_HUB", v: string | undefined) => {
      if (v === undefined || v === "") delete process.env[k]; else process.env[k] = v;
    };
    inst = chain.then(async () => {
      const saved = { lib: process.env.BEND_LIB, hub: process.env.BEND_HUB };
      set("BEND_LIB", lib);
      set("BEND_HUB", hub);
      try {
        return await import(src.bendTs + q);
      } finally {
        set("BEND_LIB", saved.lib);
        set("BEND_HUB", saved.hub);
      }
    });
    chain = inst.catch(() => undefined);
    instances.set(key, inst);
  }
  return inst;
}
