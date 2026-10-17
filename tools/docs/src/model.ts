// model: everything the renderer needs, assembled from hub metadata, extracted
// declarations, import edges and checker statuses.

import type { NameRecord } from "./hub.ts";
import type { DocDecl, FileError } from "./extract.ts";
import type { Edge, Import } from "./imports.ts";
import { worst, type FileClass, type FileStatus } from "./status.ts";
import type { License } from "./license.ts";

export type Module = {
  path: string;
  header: string | null;            // the module's top `#` comment block, when it is not a declaration's doc
  source: string | null;            // the file text for the source page, or null when it is too large
  imports: Import[];
  foreign: string[];
  decls: DocDecl[] | null;          // null when the reader could not load the file
  error: FileError | null;
  status: FileStatus | null;        // null with --no-check
  provedIn: Record<string, string>; // law local name -> file that fills it (other than this one)
  settled?: FileClass;              // an `open` LAWS file whose every open law a checking sibling proves
};

export type PkgName = { name: string; version: string; owner: string; ts: number };

export type Package = {
  hash: string; ts: number; desc: string; bytes: number;
  files: { path: string; bytes: number }[];
  names: PkgName[];
  licenses: License[];
  modules: Module[];
  deps: Edge[]; rdeps: Edge[];
  status: FileClass | null;
  counts: { laws: number; proved: number; defs: number; types: number; decls: number };
};

export type Site = {
  built: string; compiler: string; checked: boolean; partial: boolean; local: boolean;
  packages: Package[];                // display order: named first, then by recency
  byHash: Map<string, Package>;
  groups: Group[];                    // one per lineage, in display order
  groupOf: Map<string, Group>;        // every member hash -> its lineage
  fetchFails: { hash: string; error: string }[];  // hub packages this build could not fetch or verify
  names: NameRecord[];
};

export const label = (p: Package) => (p.names.length > 0 ? `${p.names[0].name}@${p.names[0].version}` : shortHash(p.hash));
export const shortHash = (h: string) => h.slice(0, 10);
export const published = (p: Package) => (p.names.length > 0 ? Math.min(...p.names.map((n) => n.ts)) : p.ts);

export function namesByHash(names: NameRecord[]): Map<string, PkgName[]> {
  const m = new Map<string, PkgName[]>();
  for (const n of names) {
    for (const v of n.versions) {
      const list = m.get(v.hash) ?? [];
      list.push({ name: n.name, version: v.version, owner: n.owner_login, ts: v.ts });
      m.set(v.hash, list);
    }
  }
  return m;
}

export type Group = { key: string; latest: Package; members: Package[] };

export const versionKey = (v: string) => v.split(".").map((x) => x.padStart(8, "0")).join(".");
const newest = (a: Package, b: Package) => {
  const va = a.names[0]?.version, vb = b.names[0]?.version;
  // A named release always outranks an anonymous upload of the same lineage, however new.
  if (!!va !== !!vb) return va ? a : b;
  if (va && vb && va !== vb) return versionKey(va) > versionKey(vb) ? a : b;
  return a.ts >= b.ts ? a : b;
};

/** One group per package lineage: a name, or (for anonymous uploads) the same file set and description. */
export function groupPackages(pkgs: Package[]): Group[] {
  const sig = (p: Package) => `${p.files.map((f) => f.path).sort().join("\n")}\n${p.desc}`;
  const groups = new Map<string, Group>();
  const bySig = new Map<string, string>();
  const add = (key: string, p: Package) => {
    const g = groups.get(key);
    if (g) { g.members.push(p); g.latest = newest(g.latest, p); } else groups.set(key, { key, latest: p, members: [p] });
  };
  for (const p of pkgs) if (p.names.length > 0) { add(`name:${p.names[0].name}`, p); bySig.set(sig(p), `name:${p.names[0].name}`); }
  for (const p of pkgs) if (p.names.length === 0) add(bySig.get(sig(p)) ?? `files:${sig(p)}`, p);
  for (const g of groups.values()) g.members.sort((a, b) => (newest(a, b) === a ? -1 : 1));
  return [...groups.values()].sort((x, y) => order(x.latest, y.latest));
}

const order = (a: Package, b: Package) => {
  const na = a.names.length > 0 ? 0 : 1, nb = b.names.length > 0 ? 0 : 1;
  return na - nb || b.ts - a.ts || a.hash.localeCompare(b.hash);
};

export function displayOrder(pkgs: Package[]): Package[] {
  return [...pkgs].sort(order);
}

export type ApiDiff = { added: string[]; removed: string[]; changed: string[] };

// The declaration kinds that make up a package's API; effects and unsafe defs are not compared.
const API_KINDS = new Set(["def", "law", "template", "type", "ctor"]);

/** Compares two packages' APIs by `<module path>/<decl name>`; `changed` means the signature differs. */
export function apiDiff(older: Package, newer: Package): ApiDiff {
  const index = (p: Package) => {
    const m = new Map<string, string>();
    for (const mod of p.modules) for (const d of mod.decls ?? []) {
      if (API_KINDS.has(d.kind)) m.set(`${mod.path}/${d.name}`, d.signature);
    }
    return m;
  };
  const a = index(older), b = index(newer);
  const added: string[] = [], removed: string[] = [], changed: string[] = [];
  for (const [k, sig] of b) {
    if (!a.has(k)) added.push(k);
    else if (a.get(k) !== sig) changed.push(k);
  }
  for (const k of a.keys()) if (!b.has(k)) removed.push(k);
  return { added: added.sort(), removed: removed.sort(), changed: changed.sort() };
}

const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

/** The module's top `#` run with `#` and one space stripped; null when line 1 is not `#` or it documents a declaration. */
export function moduleHeader(text: string): string | null {
  const lines = text.split("\n");
  if (!lines[0]?.startsWith("#")) return null;
  let end = 0;
  while (end < lines.length && lines[end].startsWith("#")) end++;
  const after = lines[end];
  if (after !== undefined && after.trim() !== "" && !/^import\b/.test(after)) return null;
  return lines.slice(0, end).map((l) => l.replace(/^# ?/, "")).join("\n");
}

/** Lines of the def starting at `line` (1-based), up to the next top-level declaration, strings and comments blanked. */
export function defBody(text: string, line: number): string {
  const lines = text.split("\n");
  const out: string[] = [];
  for (let i = line - 1; i < lines.length; i++) {
    if (i > line - 1 && /^[^\s#]/.test(lines[i])) break;
    out.push(blankLine(lines[i]));
  }
  return out.join("\n");
}

const blankLine = (l: string) => l.replace(/"(\\.|[^"\\])*"|'(\\.|[^'\\])*'/g, '""').replace(/#.*$/, "");
const HOLE = /(^|[^\w?])\?[A-Za-z_]\w*/g;

/** A `?name` hole anywhere in the def's body; `bend guide` says such a hole leaves the goal open. */
export const hasHole = (body: string) => body.match(HOLE) !== null;

/** 1-based lines of the top-level defs of `text` that hold a `?hole` or call a def that does: a proof among them rests on an open goal. */
export function holedDefs(text: string): Set<number> {
  const defs: { line: number; name: string; body: string }[] = [];
  text.split("\n").forEach((l, i) => {
    const m = l.match(/^(?:@unsafe\s+)?def\s+([A-Za-z_][\w.]*)\s*\(/);
    if (m !== null) defs.push({ line: i + 1, name: m[1], body: defBody(text, i + 1) });
  });
  const holed = defs.filter((d) => hasHole(d.body));
  for (let grew = true; grew;) {
    grew = false;
    for (const d of defs) {
      if (holed.includes(d) || !holed.some((h) => new RegExp(`(?<![\\w.])${esc(h.name)}(?!\\w)`).test(d.body))) continue;
      holed.push(d);
      grew = true;
    }
  }
  return new Set(holed.map((d) => d.line));
}

// bend prints its count of open goals only when every other proof checks (observed on 2.0.37), so a proof
// in an `open` file is verified unless it rests on a hole or an open goal lies outside the file (an import's).
function openVerified(m: Module | undefined, src: string): (proofLine: number) => boolean {
  const s = m?.status;
  if (s == null || s.class !== "open" || m!.decls === null) return () => false;
  const todo = Number(s.summary.match(/^(\d+) TODO/)?.[1] ?? NaN);
  const holes = src.split("\n").map(blankLine).join("\n").match(HOLE)?.length ?? 0;
  const lawsWithoutDef = m!.decls.filter((d) => d.kind === "law" && d.proofLine === undefined).length;
  if (todo !== holes + lawsWithoutDef) return () => false;
  const holed = holedDefs(src);
  return (line) => !holed.has(line);
}

/** 1-based line of `def [Alias.]<local>(` in a file that fills an imported law, or null. */
export function fillerLine(text: string, local: string): number | null {
  const re = new RegExp(`^(@unsafe\\s+)?def\\s+([A-Za-z_][\\w]*\\.)*${esc(local)}\\s*\\(`);
  const i = text.split("\n").findIndex((l) => re.test(l));
  return i < 0 ? null : i + 1;
}

const passes = (s: FileStatus | null | undefined) => s == null || s.class === "checks" || s.class === "unsafe";

/** Settles each law (proved here, proved in a checking sibling, or open), counts declarations, and sets the package status. */
export function finishPackage(p: Package, fills: Map<string, string[]>, text: (path: string) => string, checked = true): void {
  const filledBy = new Map<string, string>();
  for (const [file, list] of fills) for (const f of list) if (!filledBy.has(f)) filledBy.set(f, file);
  const byPath = new Map(p.modules.map((m) => [m.path, m]));
  const c = { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 };
  const effective: FileClass[] = [];
  let unchecked = false;
  for (const m of p.modules) {
    let unfilled = 0, rescued = 0, rescuedUnsafe = false;
    const src = m.decls ? text(m.path) : "";
    const ownOpen = openVerified(m, src);
    for (const d of m.decls ?? []) {
      c.decls++;
      if (d.kind === "type") { c.types++; continue; }
      if (d.kind === "ctor") continue;
      if (d.kind !== "law") { c.defs++; continue; }
      c.laws++;
      if (d.proved && d.proofLine !== undefined && hasHole(defBody(src, d.proofLine))) { d.proved = false; d.holes = true; }
      // A proof in a file the checker did not accept is not a proof, whatever the reader inferred.
      const accepted = passes(m.status) || (d.proofLine !== undefined && ownOpen(d.proofLine));
      if (d.proved && m.status !== null && !accepted) { d.proved = false; d.unverified = m.status.class; }
      if (!d.proved && !d.holes) {
        // Only a law without a def here is among the open goals bend counts for this file alone.
        if (d.proofLine === undefined) unfilled++;
        const by = filledBy.get(`${m.path}#${d.name}`);
        if (by !== undefined && by !== m.path) {
          m.provedIn[d.name] = by;
          const fl = fillerLine(text(by), d.name);
          const holes = fl !== null && hasHole(defBody(text(by), fl));
          const st = byPath.get(by)?.status;
          if (holes) d.holes = true;
          else if (passes(st) || (fl !== null && openVerified(byPath.get(by), text(by))(fl))) {
            d.proved = true;
            if (d.proofLine === undefined) rescued++;
            if (st?.class === "unsafe") rescuedUnsafe = true;
          }
        }
      }
      if (d.proved) c.proved++;
    }
    const s = m.status;
    if (s === null) { unchecked = true; continue; }
    const todo = s.class === "open" ? Number(s.summary.match(/^(\d+) TODO/)?.[1] ?? NaN) : NaN;
    // Checked alone, a LAWS.bend reports each law without a def as open; when that count is exactly
    // its laws proved by siblings that check, the file counts as checking for the package.
    if (s.class === "open" && todo === unfilled && rescued === unfilled && unfilled > 0) {
      m.settled = rescuedUnsafe ? "unsafe" : "checks";
      effective.push(m.settled);
    } else effective.push(s.class);
  }
  p.counts = c;
  // A package with a file the checker never ran on is not checked, not the worst of the rest.
  p.status = checked && unchecked ? null : effective.length > 0 ? worst(effective) : null;
}

export function attachEdges(pkgs: Package[], edges: Edge[]): void {
  const by = new Map(pkgs.map((p) => [p.hash, p]));
  for (const e of edges) {
    by.get(e.from)?.deps.push(e);
    by.get(e.to)?.rdeps.push(e);
  }
}

/** A law's statement up to its binder names and quantities: `@-x:Nat -> {f(x) …}` and `@n:Nat -> {f(n) …}` agree. */
export function lawKey(signature: string): string {
  const names: string[] = [];
  let s = signature.replace(/@[-+~]?([A-Za-z_][\w.]*)\s*:/g, (_, n: string) => { names.push(n); return `@${n}:`; });
  names.forEach((n, i) => {
    s = s.replace(new RegExp(`(?<![\\w.])${n.replace(/\./g, "\\.")}(?![\\w.])`, "g"), `v${i}`);
  });
  return s.replace(/\s+/g, " ").trim();
}

export type LemmaRef = { pkg: Package; module: string; name: string };

/** Every proved law of the latest bend-mathlib, by lawKey; the library other packages can import instead of re-proving. */
export function mathlibIndex(site: Site): Map<string, LemmaRef> {
  const out = new Map<string, LemmaRef>();
  const g = site.groups.find((x) => x.latest.names.some((n) => n.name === "bend-mathlib"));
  if (g === undefined) return out;
  for (const m of g.latest.modules) {
    for (const d of m.decls ?? []) {
      if (d.kind !== "law" || !d.proved || d.name.endsWith("_sym")) continue;
      const k = lawKey(d.signature);
      if (!out.has(k)) out.set(k, { pkg: g.latest, module: m.path, name: d.name });
    }
  }
  return out;
}
