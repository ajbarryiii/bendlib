// Bend Docs build: fetch every BendHub package (verified, cached by hash), extract
// declarations with @bendlib/reader, check each .bend file on the pinned compiler,
// and render a static site with relative links into tools/docs/dist/.
//
// usage: bun tools/docs/build.ts [--limit N] [--only name@version|0xhash,...] [--no-check]
//          [--local entry.bend] [--jobs N] [--timeout SEC (default 180)] [--mem-mb MB] [--rss-mb MB] [--out DIR] [--cache DIR]
//          [--require-sandbox]
// exit: 0 site written · 1 fatal error or required-sandbox checks failed · 2 usage or toolchain mismatch

import { existsSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { bendSource } from "../reader/index.ts";
import { packageFiles, hubHash } from "../mathlib/hash.ts";
import { PkgError } from "../mathlib/lib.ts";
import { ensurePackage, fetchIndex, fetchNames, pool, seedNames, sha256, underRoot, type IndexEntry, type ManifestLine } from "./src/hub.ts";
import { extractFile, type FileDecls } from "./src/extract.ts";
import { dependencyEdges, foreignImports, parseImports } from "./src/imports.ts";
import { licenses } from "./src/license.ts";
import { attachEdges, displayOrder, finishPackage, groupPackages, moduleHeader, namesByHash, type Group, type Module, type Package, type Site } from "./src/model.ts";
import { renderAuthors, renderIndex, renderLemmas, renderLlms, renderModule, renderName, renderPackage, renderSearch, renderSource, modFile, pkgPage, srcFile, namePage, setBaseNamespaces } from "./src/render.ts";
import { baseNamespaces } from "./src/status.ts";
import { buildSearchIndex } from "./src/searchindex.ts";
import { checkFile, compilerVersion, crossCheck, readStatusCache, sandboxProbe, statusKey, writeStatusCache, type FileClass, type FileStatus } from "./src/status.ts";

const HERE = import.meta.dir;
const ROOT = resolve(HERE, "../..");
// Bump when the shape of cached extraction records changes.
const EXTRACT_FORMAT = 2;
// Modules larger than this get no source page; their declarations link to the raw hub file.
const MAX_SRC_BYTES = 400 * 1024;
// PLAN §5.2: big proofs check in ~29 s, so 20 s produced false timeouts (bend-4r8.12).
export const DEFAULT_TIMEOUT = 180;

type Args = { limit: number | null; only: string[] | null; local: string | null; check: boolean; jobs: number; timeout: number; memMb: number; rssMb: number; out: string; cache: string; requireSandbox: boolean };

function usage(msg: string): never {
  console.error(`build: ${msg}\nusage: bun tools/docs/build.ts [--limit N] [--only name@version|0xhash,...] [--no-check] [--local entry.bend] [--jobs N] [--timeout SEC (default 180)] [--mem-mb MB] [--rss-mb MB] [--out DIR] [--cache DIR] [--require-sandbox]`);
  process.exit(2);
}

function parseArgs(argv: string[]): Args {
  const a: Args = { limit: null, only: null, local: null, check: true, jobs: 8, timeout: DEFAULT_TIMEOUT, memMb: 16384, rssMb: 3072, out: join(HERE, "dist"), cache: join(HERE, ".cache"), requireSandbox: false };
  let outSet = false;
  const num = (i: number) => {
    const n = Number(argv[i + 1]);
    if (!Number.isFinite(n) || n <= 0) usage(`${argv[i]} needs a positive number`);
    return n;
  };
  for (let i = 0; i < argv.length; i++) {
    const f = argv[i];
    if (f === "--no-check") a.check = false;
    else if (f === "--require-sandbox") a.requireSandbox = true;
    else if (f === "--limit") a.limit = num(i++);
    else if (f === "--jobs") a.jobs = Math.floor(num(i++));
    else if (f === "--timeout") a.timeout = num(i++);
    else if (f === "--mem-mb") a.memMb = num(i++);
    else if (f === "--rss-mb") a.rssMb = num(i++);
    else if (f === "--local") { if (!argv[i + 1]) usage("--local needs an entry .bend file"); a.local = resolve(argv[++i]); }
    else if (f === "--only") { if (!argv[i + 1]) usage("--only needs a list"); a.only = argv[++i].split(",").filter(Boolean); }
    else if (f === "--out") { if (!argv[i + 1]) usage("--out needs a directory"); a.out = resolve(argv[++i]); outSet = true; }
    else if (f === "--cache") { if (!argv[i + 1]) usage("--cache needs a directory"); a.cache = resolve(argv[++i]); }
    else usage(`unknown argument ${f}`);
  }
  if (a.local !== null && !outSet) a.out = join(HERE, "dist", "local");
  return a;
}

/** A cached status is stale when absent, a timeout or memory limit with more room now, an address-space abort, a pre-probe sandbox failure, or a hub fetch failure. */
export function stale(c: FileStatus | undefined, timeout: number, rssMb = Infinity): boolean {
  return c === undefined
    || (c.class === "timeout" && c.seconds < timeout - 1)
    || (c.class === "limit" && (c.rssMb ?? 0) < rssMb)
    || (c.class === "fails" && /^ASSERTION FAILED: MemoryExhaustion\b/.test(c.detail))
    || (c.class === "fails" && /^bwrap: /.test(c.detail))
    // bend words a missing hub file and a network failure alike, so a fetch failure is re-tried every build.
    || (c.class === "fails" && /a file at https?:\/\//.test(c.detail));
}

/** True when a re-check reached the cached verdict again; only its time may differ (a timeout's time is its budget, so it always counts). */
export const sameVerdict = (a: FileStatus | undefined, b: FileStatus) =>
  a !== undefined && a.class !== "timeout" && a.class === b.class && a.summary === b.summary && a.detail === b.detail && a.rssMb === b.rssMb;

const log = (s: string) => console.error(s);
const secs = (t0: number) => ((performance.now() - t0) / 1000).toFixed(1) + " s";

function write(out: string, rel: string, text: string) {
  const p = underRoot(out, rel);
  mkdirSync(dirname(p), { recursive: true });
  writeFileSync(p, text);
}

function duBytes(dir: string): { bytes: number; files: number } {
  let bytes = 0, files = 0;
  for (const e of readdirSync(dir)) {
    const p = join(dir, e);
    const s = statSync(p);
    if (s.isDirectory()) { const r = duBytes(p); bytes += r.bytes; files += r.files; } else { bytes += s.size; files++; }
  }
  return { bytes, files };
}

async function bundle(entry: string): Promise<string> {
  const r = await Bun.build({ entrypoints: [entry], minify: true, target: "browser" });
  if (!r.success) throw new Error(`bundling ${entry} failed: ${r.logs.map(String).join("\n")}`);
  return await r.outputs[0].text();
}

/** Stages `bend <entry> --publish`'s file set into `<lib>/<hash>/`, keyed by its would-be hub hash. */
function stageLocal(entry: string, lib: string): { hash: string; files: Record<string, number>; bytes: number; manifest: ManifestLine[] } {
  const content = packageFiles(entry);
  const hash = hubHash(content);
  const files: Record<string, number> = {};
  const manifest: ManifestLine[] = [];
  for (const path of Object.keys(content).sort()) {
    files[path] = Buffer.byteLength(content[path]);
    manifest.push({ sha256: sha256(content[path]), path });
    const target = join(lib, hash, path);
    mkdirSync(dirname(target), { recursive: true });
    writeFileSync(target, content[path]);
  }
  return { hash, files, bytes: Object.values(files).reduce((a, b) => a + b, 0), manifest };
}

// Extraction cache keys embed the reader's source hash, so a reader or extractor fix re-extracts
// instead of reusing records built by the old code.
function readerKey(): string {
  const dir = join(ROOT, "tools", "reader", "src");
  const files = readdirSync(dir).filter((f) => f.endsWith(".ts")).sort().map((f) => join(dir, f));
  files.push(join(HERE, "src", "extract.ts"));
  return sha256(files.map((f) => readFileSync(f)).join("\0")).slice(0, 12);
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  if (args.local !== null) {
    let isFile = false;
    try { isFile = statSync(args.local).isFile(); } catch { isFile = false; }
    if (!isFile) usage(`--local: ${args.local} is not a file`);
  }
  const T0 = performance.now();
  const pinned = JSON.parse(readFileSync(join(ROOT, "toolchain.json"), "utf8")).bend.version as string;
  const compiler = compilerVersion();
  if (compiler !== pinned) {
    console.error(`build: toolchain.json pins bend ${pinned}, but the installed bend is ${compiler}; statuses must come from the pinned compiler`);
    process.exit(2);
  }
  const sandbox = sandboxProbe();
  if (args.check && !sandbox.ok) {
    const why = sandbox.why.split("\n")[0] || "probe failed";
    if (args.requireSandbox) { console.error(`build: sandbox required but unusable: ${why}`); process.exit(2); }
    log(`sandbox: unusable, checking unsandboxed (${why})`);
  }
  const lib = join(args.cache, "lib");
  mkdirSync(lib, { recursive: true });

  let t = performance.now();
  const [index, names] = await Promise.all([fetchIndex(), fetchNames()]);
  seedNames(lib, names);
  const nameMap = namesByHash(names);
  const resolveName = (nv: string) => {
    const [n, v] = nv.split("@");
    return names.find((x) => x.name === n)?.versions.find((x) => x.version === v)?.hash ?? null;
  };
  let local: { hash: string; files: Record<string, number>; bytes: number; manifest: ManifestLine[] } | null = null;
  let entries: IndexEntry[] = index;
  if (args.local !== null) {
    let staged: ReturnType<typeof stageLocal>;
    try { staged = stageLocal(args.local, lib); }
    catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
    local = staged;
    entries = [{ hash: local.hash, files: local.files, bytes: local.bytes, ts: Date.now(), desc: "" }];
    log(`local: staged ${args.local} as ${local.hash} (${Object.keys(local.files).length} files) (${secs(t)})`);
  } else if (args.only !== null) {
    const want = new Set(args.only.map((o) => (o.startsWith("0x") ? o : resolveName(o) ?? usage(`--only: ${o} is not a name@version on the hub`))));
    entries = index.filter((e) => want.has(e.hash));
    for (const h of want) if (!entries.some((e) => e.hash === h)) usage(`--only: ${h} is not in the hub index`);
  }
  const ordered = [...entries].sort((a, b) => (nameMap.has(a.hash) ? 0 : 1) - (nameMap.has(b.hash) ? 0 : 1) || b.ts - a.ts);
  if (args.limit !== null) entries = ordered.slice(0, args.limit); else entries = ordered;
  const partial = entries.length !== index.length;
  if (local === null) log(`hub: ${index.length} packages in index.json, ${names.length} names; building ${entries.length} (${secs(t)})`);

  t = performance.now();
  type Fetched = { entry: IndexEntry; manifest: ManifestLine[] };
  const good: Fetched[] = [];
  const fetchFails: { hash: string; error: string }[] = [];
  if (local !== null) {
    good.push({ entry: entries[0], manifest: local.manifest });
    log(`stage: local package staged (${secs(t)})`);
  } else {
    let fetched = 0;
    const results = await pool(entries, Math.min(16, args.jobs * 2), async (e): Promise<Fetched | { entry: IndexEntry; error: string }> => {
      try {
        const c = await ensurePackage(e.hash, lib, args.cache);
        if (c.fetched) fetched++;
        return { entry: e, manifest: c.manifest };
      } catch (err) {
        return { entry: e, error: err instanceof Error ? err.message : String(err) };
      }
    });
    for (const r of results) if ("manifest" in r) good.push(r); else fetchFails.push({ hash: r.entry.hash, error: r.error });
    log(`fetch: ${fetched} new packages fetched and verified, ${good.length - fetched} from cache${fetchFails.length ? `, ${fetchFails.length} could not fetch` : ""} (${secs(t)})`);
  }

  t = performance.now();
  const src = await bendSource();
  if (src.version !== compiler) usage(`reader parses with bend.ts ${src.version}, compiler is ${compiler}`);
  const extracted = new Map<string, Record<string, FileDecls>>();
  let extractedNew = 0;
  const declsDir = join(args.cache, "decls", `${compiler}-f${EXTRACT_FORMAT}-${readerKey()}`);
  for (const { entry: e, manifest } of good) {
    const cfile = join(declsDir, `${e.hash}.json`);
    if (existsSync(cfile)) { extracted.set(e.hash, JSON.parse(readFileSync(cfile, "utf8"))); continue; }
    const rec: Record<string, FileDecls> = {};
    for (const { path } of manifest) if (path.endsWith(".bend")) {
      rec[path] = await extractFile(join(lib, e.hash, path), join(lib, e.hash), lib, src);
      extractedNew++;
    }
    mkdirSync(dirname(cfile), { recursive: true });
    writeFileSync(cfile, JSON.stringify(rec));
    extracted.set(e.hash, rec);
  }
  log(`extract: ${extractedNew} files read with @bendlib/reader, the rest from cache (${secs(t)})`);

  t = performance.now();
  const statusFile = join(args.cache, "status.json");
  const cache = readStatusCache(statusFile);
  let checkedNew = 0;
  let sandboxFails = 0;
  if (args.check) {
    const todo: { hash: string; path: string }[] = [];
    for (const { entry: e, manifest } of good) for (const { path } of manifest) if (path.endsWith(".bend") && stale(cache[statusKey(e.hash, path, compiler)], args.timeout, args.rssMb)) todo.push({ hash: e.hash, path });
    let done = 0;
    await pool(todo, args.jobs, async ({ hash, path }) => {
      const s = await checkFile(join(lib, hash, path), { bendLib: lib, timeoutSec: args.timeout, memMb: args.memMb, rssMb: args.rssMb, cwd: join(lib, hash) });
      // A sandbox failure is not a file status: never cache it, so the next run retries the check.
      const key = statusKey(hash, path, compiler), old = cache[key];
      if (s.class === "sandbox") sandboxFails++;
      // An unchanged verdict keeps its entry, so status.json (the docs cache key) changes only with a verdict.
      else if (!sameVerdict(old, s)) cache[key] = s;
      checkedNew++;
      if (++done % 50 === 0) { log(`check: ${done}/${todo.length}`); writeStatusCache(statusFile, cache); }
    });
    writeStatusCache(statusFile, cache);
  }
  log(`check: ${args.check ? `${checkedNew} files checked, the rest from cache` : "skipped (--no-check)"} · sandbox: ${sandbox.ok ? "bwrap" : "none"} (${secs(t)})`);
  if (args.requireSandbox && sandboxFails > 0) {
    console.error(`build: ${sandboxFails} file(s) could not be checked: sandbox setup failed`);
    process.exit(1);
  }

  const pkgs: Package[] = good.map(({ entry: e, manifest }) => {
    const rec = extracted.get(e.hash)!;
    const fills = new Map<string, string[]>();
    const modules: Module[] = manifest.map((m) => m.path).filter((p) => p.endsWith(".bend")).sort().map((path) => {
      const text = readFileSync(join(lib, e.hash, path), "utf8");
      const r = rec[path] ?? { ok: false as const, error: { message: "not extracted", file: null, line: null }, ms: 0 };
      if (r.ok) fills.set(path, r.fills);
      const cached = args.check ? cache[statusKey(e.hash, path, compiler)] ?? null : null;
      return {
        path, header: moduleHeader(text), source: Buffer.byteLength(text) > MAX_SRC_BYTES ? null : text, imports: parseImports(text), foreign: foreignImports(text),
        decls: r.ok ? r.decls : null, error: r.ok ? null : r.error,
        status: cached === null ? null : crossCheck(cached, text), provedIn: {},
      };
    });
    const p: Package = {
      hash: e.hash, ts: e.ts, desc: e.desc, bytes: e.bytes,
      files: manifest.map((m) => ({ path: m.path, bytes: e.files[m.path] ?? 0 })),
      names: (nameMap.get(e.hash) ?? []).sort((a, b) => a.ts - b.ts),
      licenses: licenses(manifest.map((m) => ({ path: m.path, text: () => readFileSync(join(lib, e.hash, m.path), "utf8") }))),
      modules, deps: [], rdeps: [],
      status: null,
      counts: { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 },
    };
    finishPackage(p, fills, (path) => readFileSync(join(lib, e.hash, path), "utf8"), args.check);
    return p;
  });
  const edges = dependencyEdges(pkgs.map((p) => ({ hash: p.hash, files: p.modules })), resolveName);
  attachEdges(pkgs, edges);

  const groups = groupPackages(pkgs);
  const groupOf = new Map<string, Group>();
  for (const g of groups) for (const m of g.members) groupOf.set(m.hash, g);
  const site: Site = {
    built: new Date().toISOString().replace(/\.\d+Z$/, "Z"), compiler, checked: args.check, partial, local: local !== null,
    packages: displayOrder(pkgs), byHash: new Map(pkgs.map((p) => [p.hash, p])), groups, groupOf, fetchFails, names,
  };

  t = performance.now();
  const out = args.out;
  mkdirSync(out, { recursive: true });
  setBaseNamespaces(baseNamespaces());
  write(out, "index.html", renderIndex(site));
  write(out, "authors.html", renderAuthors(site));
  write(out, "search.html", renderSearch(site));
  write(out, "search-index.json", JSON.stringify(buildSearchIndex(site)));
  write(out, "llms.txt", renderLlms(site));
  write(out, "lemmas.txt", renderLemmas(site));
  write(out, "assets/style.css", readFileSync(join(HERE, "assets/style.css"), "utf8"));
  write(out, "assets/search.js", await bundle(join(HERE, "src/client/search.ts")));
  write(out, "assets/site.js", await bundle(join(HERE, "src/client/site.ts")));
  let pages = 3;
  for (const p of site.packages) {
    write(out, pkgPage(p.hash), renderPackage(site, p));
    pages++;
    for (const m of p.modules) {
      write(out, modFile(p.hash, m.path), renderModule(site, p, m)); pages++;
      if (m.source !== null) { write(out, srcFile(p.hash, m.path), renderSource(site, p, m)); pages++; }
    }
  }
  const built = new Set(site.packages.map((p) => p.hash));
  for (const n of names) {
    if (!n.versions.some((v) => built.has(v.hash))) continue;
    write(out, namePage(n.name), renderName(site, n.name));
    pages++;
  }
  log(`render: ${pages} pages (${secs(t)})`);

  const files = pkgs.flatMap((p) => p.modules);
  const decls = files.flatMap((m) => m.decls ?? []);
  const laws = decls.filter((d) => d.kind === "law");
  const byClass = (list: (FileClass | null | undefined)[]) => {
    const o: Record<string, number> = {};
    for (const c of list) o[c ?? "not checked"] = (o[c ?? "not checked"] ?? 0) + 1;
    return Object.entries(o).sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k} ${v}`).join(", ");
  };
  const failed = pkgs.flatMap((p) => p.modules.filter((m) => m.error !== null).map((m) => ({ p, m })));
  const du = duBytes(out);
  console.log(`Bend Docs build on bend ${compiler}${partial ? " (partial)" : ""}`);
  console.log(`packages   ${pkgs.length} (${pkgs.filter((p) => p.names.length > 0).length} carry a name@version), ${edges.length} dependency edges`);
  console.log(`files      ${files.length} .bend files, ${pkgs.reduce((a, p) => a + p.files.length, 0)} files in all`);
  console.log(`decls      ${decls.length} (${laws.length} laws: ${laws.filter((d) => d.proved).length} proved, ${laws.filter((d) => !d.proved).length} open)`);
  console.log(`kinds      ${Object.entries(decls.reduce<Record<string, number>>((a, d) => ({ ...a, [d.kind]: (a[d.kind] ?? 0) + 1 }), {})).map(([k, v]) => `${k} ${v}`).join(", ")}`);
  console.log(`status     files: ${byClass(files.map((m) => m.status?.class))}`);
  console.log(`status     packages: ${byClass(pkgs.map((p) => p.status))}`);
  for (const f of fetchFails) console.log(`fetch      ${f.hash.slice(0, 10)} could not fetch: ${f.error.split("\n")[0].slice(0, 160)}`);
  console.log(`load       ${files.length - failed.length}/${files.length} files loaded by the reader; ${failed.length} failed:`);
  for (const { p, m } of failed) console.log(`  ${p.hash.slice(0, 10)} ${m.path}: ${m.error!.message.split("\n").map((l) => l.trim()).filter((l) => l && l !== "Error:").slice(0, 2).join(" ").slice(0, 160)}`);
  console.log(`dist       ${out}: ${du.files} files, ${(du.bytes / 1048576).toFixed(1)} MiB (search-index.json ${(statSync(join(out, "search-index.json")).size / 1048576).toFixed(2)} MiB)`);
  console.log(`wall       ${secs(T0)}`);
  if (local !== null) console.log(`local package page: ${pkgPage(local.hash)}`);
}

if (import.meta.main) main().catch((e) => {
  console.error(`build: ${e instanceof Error ? e.stack ?? e.message : String(e)}`);
  process.exit(1);
});
