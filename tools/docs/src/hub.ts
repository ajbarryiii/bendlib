// hub: fetch BendHub's index, names and package files into a private BEND_LIB.
// A package hash is the first 128 bits of sha256(manifest), and every manifest
// line is "<sha256> <path>", so both levels are verified before anything is cached.

import { existsSync, mkdirSync, readFileSync, writeFileSync, renameSync } from "node:fs";
import { dirname, join, resolve, sep } from "node:path";

export const HUB = process.env.BEND_HUB ?? "https://hub.bend-lang.com";

export const FETCH_TIMEOUT_MS = 30_000;

/** One hub request, bounded so a stalled hub cannot hang the build. */
export async function fetchHub(url: string, timeoutMs = FETCH_TIMEOUT_MS): Promise<Response> {
  return fetch(url, { signal: AbortSignal.timeout(timeoutMs) });
}

export type IndexEntry = { hash: string; files: Record<string, number>; bytes: number; ts: number; desc: string };
export type NameVersion = { version: string; hash: string; ts: number };
export type NameRecord = {
  name: string; owner_login: string; ts: number; dependents?: number; mentions?: number; score?: number;
  latest: { version: string; hash: string; ts: number; desc: string };
  versions: NameVersion[];
};

const HASH = /^0x[0-9a-f]{32}$/;
// PLAN F1: names are `^[a-z][a-z0-9-]{0,63}$`, versions are `a.b.c.d`.
const NAME = /^[a-z][a-z0-9-]{0,63}$/;
const VERSION = /^\d+\.\d+\.\d+\.\d+$/;

async function get(url: string, tries = 3): Promise<Response> {
  let last: unknown;
  for (let i = 0; i < tries; i++) {
    try {
      const r = await fetchHub(url);
      if (r.ok || r.status === 404 || r.status === 410) return r;
      last = new Error(`HTTP ${r.status} for ${url}`);
    } catch (e) {
      last = e;
    }
    await Bun.sleep(300 * (i + 1));
  }
  throw last instanceof Error ? last : new Error(String(last));
}

async function getJson<T>(url: string): Promise<T> {
  const r = await get(url);
  if (!r.ok) throw new Error(`HTTP ${r.status} for ${url}`);
  return (await r.json()) as T;
}

export function sha256(bytes: Uint8Array | string): string {
  return new Bun.CryptoHasher("sha256").update(bytes).digest("hex");
}

export async function fetchIndex(): Promise<IndexEntry[]> {
  const idx = await getJson<IndexEntry[]>(`${HUB}/index.json`);
  for (const e of idx) if (!HASH.test(e.hash)) throw new Error(`index.json: malformed hash ${JSON.stringify(e.hash)}`);
  return idx;
}

/** Keeps records with a well-formed name and at least one well-formed version/hash; logs and drops the rest (PLAN F1). */
export function validNameRecords(records: NameRecord[]): NameRecord[] {
  const kept: NameRecord[] = [];
  const invalid: string[] = [], empty: string[] = [];
  for (const n of records) {
    const versions = (n.versions ?? []).filter((v) => VERSION.test(v.version) && HASH.test(v.hash));
    if (NAME.test(n.name) && versions.length > 0) kept.push({ ...n, versions });
    else if (NAME.test(n.name) && (n.versions ?? []).length === 0) empty.push(n.name);
    else invalid.push(n.name);
  }
  if (invalid.length) console.error(`hub: dropped ${invalid.length} invalid name record(s): ${invalid.slice(0, 5).join(", ")}`);
  if (empty.length) console.error(`hub: skipped ${empty.length} name(s) with no versions: ${empty.slice(0, 5).join(", ")}`);
  return kept;
}

// names.json answers at most this many names whatever `limit` or paging asks, while stats.json
// counted 204 (observed 2026-10-17); a list this long is truncated, so packages.json fills it in.
export const NAMES_CAP = 100;
// packages.json pages by `after=<offset>` and answers at most 100 rows per page (observed 2026-10-17).
export const PACKAGES_PAGE = 100;

type Listed = { name: string; owner_login?: string; ts?: number; latest?: NameRecord["latest"] | null };
export type PackageRow = { hash: string; ts: number; name?: string | null; version?: string | null };

/** Every row of packages.json, all pages; an error when the pages hold fewer packages than its `total`. */
export async function fetchPackageList(hub = HUB): Promise<PackageRow[]> {
  const rows = new Map<string, PackageRow>();
  let total = 0;
  for (let after = 0; ; after += PACKAGES_PAGE) {
    const page = await getJson<{ total: number; packages: PackageRow[] }>(`${hub}/packages.json?sort=new&limit=${PACKAGES_PAGE}&after=${after}`);
    total = page.total;
    for (const r of page.packages) rows.set(r.hash, r);
    if (page.packages.length === 0 || after + PACKAGES_PAGE >= total) break;
  }
  if (rows.size < total) throw new Error(`packages.json listed ${rows.size} packages over its pages, but reports ${total}: the name list would be incomplete`);
  return [...rows.values()];
}

/** The union of names.json (top and newest) and every name packages.json carries, each completed by its `/name/<n>` record. */
export async function fetchNames(jobs = 8, hub = HUB): Promise<NameRecord[]> {
  const [top, newest, rows] = await Promise.all([
    getJson<Listed[]>(`${hub}/names.json?limit=${NAMES_CAP}`),
    getJson<Listed[]>(`${hub}/names.json?sort=new&limit=${NAMES_CAP}`),
    fetchPackageList(hub),
  ]);
  const listed = new Map<string, Listed>();
  for (const n of [...top, ...newest]) if (!listed.has(n.name)) listed.set(n.name, n);
  const before = listed.size;
  for (const r of rows) if (typeof r.name === "string" && !listed.has(r.name)) listed.set(r.name, { name: r.name });
  if (top.length >= NAMES_CAP) console.error(`hub: names.json stopped at its cap of ${NAMES_CAP}; packages.json added ${listed.size - before} more name(s)`);
  const all = [...listed.values()];
  const named = all.filter((n) => NAME.test(n.name));  // never even request a hostile name
  if (named.length !== all.length) console.error(`hub: dropped ${all.length - named.length} name record(s) with an invalid name`);
  const vanished: string[] = [], unreachable: string[] = [];
  const out = await pool(named, jobs, async (n): Promise<NameRecord | null> => {
    const latest = n.latest == null ? [] : [{ version: n.latest.version, hash: n.latest.hash, ts: n.latest.ts }];
    try {
      const r = await get(`${hub}/name/${encodeURIComponent(n.name)}`);
      if (r.status === 404 || r.status === 410) { vanished.push(n.name); return null; }
      if (!r.ok) throw new Error(`HTTP ${r.status}`);
      const full = (await r.json()) as NameRecord;
      return { ...n, ...full, versions: full.versions ?? latest } as NameRecord;
    } catch (e) {
      unreachable.push(`${n.name} (${e instanceof Error ? e.message : String(e)})`);
      // The listing's latest version is still a true name@version; without one the name is dropped.
      return n.latest == null ? null : ({ owner_login: "", ts: 0, ...n, versions: latest } as NameRecord);
    }
  });
  if (vanished.length) console.error(`hub: ${vanished.length} name(s) vanished since the listing: ${vanished.slice(0, 5).join(", ")}`);
  if (unreachable.length) console.error(`hub: ${unreachable.length} name record(s) could not be fetched, kept with the listing's latest version where it has one: ${unreachable.slice(0, 5).join(", ")}`);
  return validNameRecords(out.filter((n): n is NameRecord => n !== null));
}

export async function pool<T, R>(items: T[], jobs: number, f: (x: T, i: number) => Promise<R>): Promise<R[]> {
  const out: R[] = new Array(items.length);
  let next = 0;
  const worker = async () => {
    while (next < items.length) {
      const i = next++;
      out[i] = await f(items[i], i);
    }
  };
  await Promise.all(Array.from({ length: Math.max(1, Math.min(jobs, items.length)) }, worker));
  return out;
}

export type ManifestLine = { sha256: string; path: string };

export function parseManifest(text: string): ManifestLine[] {
  return text.trim().split("\n").filter((l) => l !== "").map((l) => {
    const m = l.match(/^([0-9a-f]{64}) (.+)$/);
    if (m === null) throw new Error(`malformed manifest line ${JSON.stringify(l)}`);
    return { sha256: m[1], path: m[2] };
  });
}

/** True when a manifest path is relative, has no `.`/`..`/empty segment, and no control chars, quotes or angle brackets. */
export function safePath(p: string): boolean {
  if (p === "" || p.startsWith("/") || /[\x00-\x1f\x7f"'<>]/.test(p)) return false;
  return !p.split("/").some((s) => s === ".." || s === "." || s === "");
}

/** Joins `rel` under `root`, refusing anything that resolves outside `root`. */
export function underRoot(root: string, rel: string): string {
  const base = resolve(root), r = resolve(base, rel);
  if (r !== base && !r.startsWith(base + sep)) throw new Error(`path escapes ${base}: ${JSON.stringify(rel)}`);
  return r;
}

export type Cached = { hash: string; manifest: ManifestLine[]; fetched: boolean };

// The manifest copy under `<cache>/manifests/<hash>` is written last, so its presence marks a complete package.
/** Ensures `<lib>/<hash>/<path>` holds every verified file of the package. */
export async function ensurePackage(hash: string, lib: string, cache: string): Promise<Cached> {
  const mfile = join(cache, "manifests", hash);
  if (existsSync(mfile)) {
    const mbytes = readFileSync(mfile);
    if (!sha256(mbytes).startsWith(hash.slice(2))) throw new Error(`cached manifest of ${hash} is corrupt; delete ${mfile} to refetch`);
    const manifest = parseManifest(mbytes.toString("utf8"));
    for (const { path } of manifest) if (!safePath(path)) throw new Error(`cached manifest of ${hash}: unsafe path ${JSON.stringify(path)}`);
    return { hash, manifest, fetched: false };
  }
  const r = await get(`${HUB}/${hash}/manifest`);
  if (!r.ok) throw new Error(`manifest of ${hash}: HTTP ${r.status}`);
  const mbytes = new Uint8Array(await r.arrayBuffer());
  if (!sha256(mbytes).startsWith(hash.slice(2))) throw new Error(`manifest of ${hash} does not hash to the package hash`);
  const manifest = parseManifest(new TextDecoder().decode(mbytes));
  for (const { path } of manifest) if (!safePath(path)) throw new Error(`manifest of ${hash}: unsafe path ${JSON.stringify(path)}`);
  const bodies = await pool(manifest, 4, async ({ sha256: want, path }) => {
    const target = join(lib, hash, path);
    if (existsSync(target) && sha256(readFileSync(target)) === want) return null;
    const fr = await get(`${HUB}/${hash}/${path.split("/").map(encodeURIComponent).join("/")}`);
    if (!fr.ok) throw new Error(`${hash}/${path}: HTTP ${fr.status}`);
    const body = new Uint8Array(await fr.arrayBuffer());
    const got = sha256(body);
    if (got !== want) throw new Error(`${hash}/${path}: sha256 ${got} does not match manifest ${want}`);
    return body;
  });
  manifest.forEach(({ path }, i) => {
    const body = bodies[i];
    if (body === null) return;
    const target = join(lib, hash, path);
    mkdirSync(dirname(target), { recursive: true });
    writeFileSync(target + ".part", body);
    renameSync(target + ".part", target);
  });
  mkdirSync(dirname(mfile), { recursive: true });
  writeFileSync(mfile + ".part", mbytes);
  renameSync(mfile + ".part", mfile);
  return { hash, manifest, fetched: true };
}

/** Pre-seeds `<lib>/names/<name>@<version>` exactly as bend.ts's name_hash would, so loads need no network for names. */
export function seedNames(lib: string, names: NameRecord[]): void {
  for (const n of names) {
    if (!NAME.test(n.name)) continue;
    for (const v of n.versions) {
      if (!HASH.test(v.hash) || !VERSION.test(v.version)) continue;
      const at = join(lib, "names", `${n.name}@${v.version}`);
      mkdirSync(dirname(at), { recursive: true });
      writeFileSync(at, v.hash + "\n");
    }
  }
}
