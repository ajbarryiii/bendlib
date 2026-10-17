// render: static HTML pages with relative links only, so the site works under
// any path prefix (a Pages project path today, a domain root later).

import { posix } from "node:path";
import type { DocDecl } from "./extract.ts";
import type { Edge } from "./imports.ts";
import { HUB, type NameRecord } from "./hub.ts";
import { apiDiff, label, lawKey, mathlibIndex, published, shortHash, versionKey, type LemmaRef, type Module, type Package, type Site } from "./model.ts";
import type { FileClass } from "./status.ts";

export const esc = (s: string) => s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]!);

export const pkgPage = (hash: string) => `pkg/${hash}/index.html`;
// Page URLs percent-encode each path segment (`#`, `?`, `%` break links); the on-disk names stay raw.
export const encPath = (p: string) => p.split("/").map(encodeURIComponent).join("/");
export const modPage = (hash: string, path: string) => `pkg/${hash}/${encPath(path)}.html`;
export const modFile = (hash: string, path: string) => `pkg/${hash}/${path}.html`;
export const srcPage = (hash: string, path: string) => `pkg/${hash}/${encPath(path)}.src.html`;
export const srcFile = (hash: string, path: string) => `pkg/${hash}/${path}.src.html`;
export const namePage = (name: string) => `name/${name}/index.html`;

function rel(from: string, to: string): string {
  const r = posix.relative(posix.dirname(from), to);
  return r === "" ? posix.basename(to) : r;
}

const date = (ts: number) => new Date(ts).toISOString().slice(0, 10);

const STATUS_TEXT: Record<FileClass, string> = {
  checks: "checks", unsafe: "relies on unsafe/foreign", open: "open laws/TODOs", fails: "fails", timeout: "timeout",
  limit: "not checked (memory cap)", sandbox: "not checked",
};

function statusBadge(c: FileClass | null, title = ""): string {
  if (c === null || c === "sandbox") return `<span class="st st-none" title="not checked in this build">not checked</span>`;
  return `<span class="st st-${c}"${title ? ` title="${esc(title)}"` : ""}>${STATUS_TEXT[c]}</span>`;
}

const kindBadge = (k: string) => `<span class="k k-${k}">${k}</span>`;

function docHtml(doc: string | null): string {
  if (doc === null || doc.trim() === "") return "";
  const inline = (s: string) => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");
  return `<div class="doc">${doc.split(/\n\s*\n/).map((p) => `<p>${inline(p)}</p>`).join("")}</div>`;
}

export function anchor(name: string): string {
  return name.replace(/[^A-Za-z0-9_.-]/g, "-");
}

type PageOpts = { path: string; title: string; body: string; site: Site; scripts?: string[]; description?: string };

export function page(o: PageOpts): string {
  const r = (p: string) => rel(o.path, p);
  const scripts = (o.scripts ?? []).map((s) => `<script src="${r(s)}" defer></script>`).join("");
  const partial = o.site.partial && !o.site.local ? ` · partial build (a subset of the hub): dependents and counts cover only the packages built` : "";
  return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${esc(o.title)}</title>
<meta name="description" content="${esc(o.description ?? "Documentation for every package on BendHub, the Bend 2 package hub.")}">
<meta name="color-scheme" content="light">
<link rel="stylesheet" href="${r("assets/style.css")}">${scripts}
</head><body>
<a class="skip" href="#main">Skip to content</a>
<header class="top"><div class="wrap">
<a class="brand" href="${r("index.html")}">~/bend-docs<span class="pill">community</span></a>
<nav aria-label="Site"><a href="${r("index.html")}">Packages</a><a href="${r("search.html")}">Search</a><a href="${r("authors.html")}">Authors</a></nav>
</div></header>
<main id="main" class="wrap">
${o.site.local ? `<p class="err">Local preview of an unpublished package — not on BendHub.</p>` : ""}
${o.body}
</main>
<footer class="foot"><div class="wrap">
<p>Community docs for BendHub packages · not affiliated with Higher Order Company · source <a href="https://github.com/bendlib/bendlib">github.com/bendlib/bendlib</a> · <a href="${r("llms.txt")}">llms.txt</a></p>
<p>Built ${esc(o.site.built)} · statuses are <code>bend --check-only</code> results on bend ${esc(o.site.compiler)} only${o.site.checked ? "" : " (checking was skipped in this build)"}${partial}</p>
</div></footer>
</body></html>
`;
}

export function renderIndex(site: Site): string {
  const path = "index.html";
  const groups = site.groups;
  const allChecked = site.checked && site.packages.every((p) => p.modules.every((m) => m.status !== null));
  const rows = groups.map((g) => {
    const p = g.latest, n = p.names[0];
    const search = [label(p), p.desc, n?.owner ?? "", ...g.members.map((m) => m.hash), ...p.names.map((x) => x.name)].join(" ").toLowerCase();
    const title = n ? `${esc(n.name)}</a> <span class="pill">@${esc(n.version)}</span>` : `${esc(shortHash(p.hash))}…</a>`;
    const more = g.members.length < 2 ? "" : n
      ? ` <a class="more" href="${esc(rel(path, namePage(n.name)))}">${g.members.length} versions</a>`
      : ` <span class="more" title="${esc(g.members.map((m) => shortHash(m.hash)).join(", "))}">${g.members.length} uploads</span>`;
    return `<tr data-s="${esc(search)}">
<td class="pk"><a class="t" href="${rel(path, pkgPage(p.hash))}">${title}${more}<div class="h">${p.hash}</div></td>
<td class="ds"><div class="clamp" title="${esc(p.desc)}">${esc(p.desc) || `<span class="muted">no description</span>`}</div></td>
<td data-l="status">${statusBadge(p.status)}</td>
<td data-l="laws" class="num">${p.counts.laws}</td>
<td data-l="used by" class="num">${g.members.reduce((a, m) => a + m.rdeps.length, 0)}</td>
<td data-l="updated" class="num">${date(p.ts)}</td></tr>`;
  }).join("\n");
  const totals = groups.reduce((a, g) => ({ laws: a.laws + g.latest.counts.laws, decls: a.decls + g.latest.counts.decls }), { laws: 0, decls: 0 });
  const body = `<div id="hero"><h1>Bend Docs</h1>
<p class="sub">every <b>BendHub</b> package, documented</p>
<p class="tag">${totals.decls.toLocaleString("en")} declarations and ${totals.laws.toLocaleString("en")} laws${allChecked ? `, each package checked on bend ${esc(site.compiler)}` : ""}</p>
<form class="q find" role="search" action="${rel(path, "search.html")}" method="get"><label class="vh" for="filter">Search packages, declarations and laws</label><input id="filter" name="q" type="search" placeholder="a package, a name, a doc word, or a law shape like Nat.add(_, 0n)" spellcheck="false" autocomplete="off"><button class="btn" type="submit">find</button></form>
<p class="hint">typing filters the packages below · <b>find</b> searches every declaration and law <span id="shown" aria-live="polite"></span></p></div>
<section><h2>Packages <span class="n">${groups.length} packages · ${site.packages.length} uploads</span></h2>
<div class="tablewrap"><table class="pkgs" id="pkgs">
<thead><tr><th scope="col">name / version</th><th scope="col">description</th><th scope="col">status</th><th scope="col" class="num">laws</th><th scope="col" class="num">used by</th><th scope="col" class="num">updated</th></tr></thead>
<tbody>
${rows}
</tbody></table></div></section>
${site.fetchFails.length ? `<section id="unfetched"><h2>Could not fetch <span class="n">${site.fetchFails.length}</span></h2>
<p class="muted">These hub packages failed download or verification this build; their pages are missing until a later run.</p>
<ul>${site.fetchFails.map((f) => `<li><code>${esc(f.hash)}</code> could not fetch: ${esc(f.error)}</li>`).join("")}</ul></section>` : ""}`;
  return page({ path, title: "Bend Docs: BendHub packages", body, site, scripts: ["assets/site.js"] });
}

// An alias spelled like a Base namespace (Nat, List, …) lets a future Base def shadow the module's (PLAN F16).
let baseNamespaces = new Set<string>();

/** The namespaces the pinned compiler's Base defines (from `bend base`), so suggested aliases never shadow them. */
export function setBaseNamespaces(names: Iterable<string>) {
  baseNamespaces = new Set(names);
}

function aliasFor(path: string): string {
  const base = posix.basename(path, ".bend").replace(/[^A-Za-z0-9_]/g, "_");
  const a = base.charAt(0).toUpperCase() + base.slice(1);
  return /^[A-Za-z_]/.test(a) && !baseNamespaces.has(a) ? a : `M${a}`;
}

function edgeList(path: string, edges: Edge[], side: "from" | "to", site: Site, empty: string): string {
  if (edges.length === 0) return `<p class="muted">${empty}</p>`;
  return `<ul class="edges">${edges.map((e) => {
    const other = site.byHash.get(e[side]);
    const name = other ? label(other) : shortHash(e[side]);
    const link = other ? `<a href="${rel(path, pkgPage(other.hash))}">${esc(name)}</a>` : `<span>${esc(e[side])}</span> <span class="muted">(${site.partial ? "not in this build" : "not on the hub index"})</span>`;
    return `<li>${link} <span class="via">via <code>${esc(e.via)}</code></span></li>`;
  }).join("")}</ul>`;
}

function statusTable(path: string, p: Package): string {
  const rows = p.modules.map((m) => {
    const s = m.status;
    const detail = s && s.detail && s.class !== "checks"
      ? `<details><summary>output</summary><pre>${esc(s.detail)}</pre></details>` : "";
    const rely = s?.unsafeDefs?.length ? `<div class="muted">defs: ${s.unsafeDefs.map((d) => `<code>${esc(d)}</code>`).join(", ")}</div>` : "";
    const settled = m.settled ? `<div class="muted">Checked alone, a law without a def is a TODO; all of them are proved in files that check, so the package counts this file as ${STATUS_TEXT[m.settled]}.</div>` : "";
    return `<tr><td><a href="${esc(rel(path, modPage(p.hash, m.path)))}">${esc(m.path)}</a></td><td>${statusBadge(s?.class ?? null)}</td>
<td>${s ? esc(s.summary) : ""}${rely}${settled}${detail}</td><td class="num">${s ? s.seconds.toFixed(1) + " s" : ""}</td></tr>`;
  }).join("\n");
  return `<div class="tablewrap"><table class="files"><thead><tr><th scope="col">File</th><th scope="col">Status</th><th scope="col">Checker says</th><th scope="col" class="num">Time</th></tr></thead><tbody>${rows}</tbody></table></div>`;
}

export function renderPackage(site: Site, p: Package): string {
  const path = pkgPage(p.hash);
  const bend = p.modules.map((m) => m.path);
  const importLines = bend.map((f) => {
    const a = aliasFor(f);
    const named = p.names.map((n) => `import ${n.name}@${n.version}/${f} as ${a}`);
    return [...named, `import ${p.hash}/${f} as ${a}`].join("\n");
  }).join("\n");
  const others = p.files.filter((f) => !f.path.endsWith(".bend"));
  const namesHtml = p.names.length
    ? `<p>${p.names.map((n) => `<a href="${esc(rel(path, namePage(n.name)))}">${esc(n.name)}</a>@${esc(n.version)} by ${esc(n.owner)}`).join("; ")}</p>`
    : `<p class="muted">Anonymous package: import it by hash.</p>`;
  const g = site.groupOf.get(p.hash)!;
  const siblings = g.members.filter((m) => m !== p);
  const versionsHtml = siblings.length === 0 ? "" : `<details class="vers"><summary>${g.latest === p ? "Earlier versions" : "Other versions"} (${siblings.length})</summary><ul class="edges">${siblings.map((m) =>
    `<li><a href="${rel(path, pkgPage(m.hash))}">${esc(label(m))}</a> <span class="muted">${date(m.ts)}</span>${m === g.latest ? ` <span class="pill">latest</span>` : ""}</li>`).join("")}</ul></details>`;
  const lic = p.licenses.map((l) => l.from === null
    ? `${esc(l.id)} <span class="muted">(no LICENSE file; the hub's default)</span>`
    : `${esc(l.id)} <span class="muted">(<a href="${HUB}/${p.hash}/${encPath(l.from)}">${esc(l.from)}</a>)</span>`).join("<br>");
  const modules = p.modules.map((m) => {
    const c = m.decls === null ? `<span class="st st-fails">not loaded</span>` : `${m.decls.length} declarations${lawCount(m.decls)}`;
    const h = m.header ? `<span class="muted"> — ${esc(m.header.split("\n")[0])}</span>` : "";
    return `<li><a href="${esc(rel(path, modPage(p.hash, m.path)))}">${esc(m.path)}</a> <span class="muted">${c}</span>${h}</li>`;
  }).join("");
  const body = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / ${esc(label(p))}</nav>
<h1>${esc(label(p))} ${statusBadge(p.status)}</h1>
<p class="hash"><code>${p.hash}</code></p>
<p class="lead">${esc(p.desc) || `<span class="muted">no description</span>`}</p>
${namesHtml}
${versionsHtml}
<dl class="facts"><dt>Published</dt><dd>${date(published(p))}</dd><dt>Size</dt><dd>${p.bytes.toLocaleString("en")} bytes, ${p.files.length} files</dd>
<dt>License</dt><dd>${lic}</dd><dt>Declarations</dt><dd>${p.counts.laws} laws (${p.counts.proved} proved), ${p.counts.defs} defs, ${p.counts.types} types</dd></dl>
<h2 id="import">Import</h2>
<pre class="code">${esc(importLines)}</pre>
<h2 id="modules">Modules</h2>
<ul class="mods">${modules}</ul>
${others.length ? `<h2 id="files">Other files</h2><ul class="mods">${others.map((f) => `<li><a href="${HUB}/${p.hash}/${encPath(f.path)}">${esc(f.path)}</a> <span class="muted">${f.bytes.toLocaleString("en")} bytes</span></li>`).join("")}</ul>` : ""}
<h2 id="deps">Dependencies</h2>
${edgeList(path, p.deps, "to", site, "No imports from other hub packages.")}
<h2 id="rdeps">Dependents</h2>
${edgeList(path, p.rdeps, "from", site, "No package in this build imports it.")}
<h2 id="status">Status on bend ${esc(site.compiler)}</h2>
${site.checked ? statusTable(path, p) : `<p class="muted">Checking was skipped in this build (--no-check).</p>`}`;
  return page({ path, title: `${label(p)} · Bend Docs`, body, site, description: p.desc });
}

function lawCount(ds: DocDecl[]): string {
  const laws = ds.filter((d) => d.kind === "law");
  return laws.length ? `, ${laws.length} laws` : "";
}

const GROUPS: [string, string][] = [["law", "Laws"], ["type", "Types"], ["def", "Definitions"], ["template", "Templates"], ["effect", "Effects (foreign code)"], ["unsafe", "Unsafe"]];

/** The signature text before its statement brace; the muted span, e.g. `@-x:U32 -> ` for `@-x:U32 -> {f(x) == Some{x} : Maybe<U32>}`. */
export function statementHead(signature: string): string {
  let depth = 0;
  for (let i = signature.length - 1; i >= 0; i--) {
    if (signature[i] === "}") depth++;
    else if (signature[i] === "{" && --depth === 0) return signature.slice(0, i);
  }
  return "";
}

const mathlibOf = new WeakMap<Site, Map<string, LemmaRef>>();

/** The bend-mathlib lemma a law of another package restates, if any. */
function inMathlib(site: Site, p: Package, d: DocDecl): LemmaRef | null {
  if (d.kind !== "law") return null;
  let idx = mathlibOf.get(site);
  if (idx === undefined) mathlibOf.set(site, idx = mathlibIndex(site));
  const ref = idx.get(lawKey(d.signature));
  return ref === undefined || site.groupOf.get(p.hash) === site.groupOf.get(ref.pkg.hash) ? null : ref;
}

function declHtml(site: Site, p: Package, m: Module, d: DocDecl, ids: Map<DocDecl, string>, ctors: DocDecl[]): string {
  const id = ids.get(d)!;
  const rawHref = `${HUB}/${p.hash}/${encPath(m.path)}`;
  const srcLink = m.source === null
    ? `<a class="src" href="${rawHref}" title="raw source on the hub; the declaration starts at line ${d.line}">source · line ${d.line}</a>`
    : `<span class="src"><a href="${esc(rel(modPage(p.hash, m.path), srcPage(p.hash, m.path)))}#L${d.line}" title="source, line ${d.line}">source · line ${d.line}</a> · <a href="${rawHref}" title="raw source on the hub">raw</a></span>`;
  let marker = "";
  if (d.kind === "law") {
    const by = m.provedIn[d.name];
    const byLink = by ? `<a href="${esc(rel(modPage(p.hash, m.path), modPage(p.hash, by)))}">${esc(by)}</a>` : "";
    const fst = by ? p.modules.find((x) => x.path === by)?.status?.class : undefined;
    marker = d.proved
      ? `<span class="pr pr-yes">proved</span>${by ? `<span class="muted">in ${byLink}</span>` : ""}`
      : d.unverified
        ? `<span class="pr pr-open">unverified</span><span class="muted">its file does not pass the checker (${d.unverified})</span>`
        : d.holes
          ? `<span class="pr pr-open">open</span><span class="muted">a ?hole is left in its proof${by ? ` in ${byLink}` : ""}</span>`
          : by
            ? `<span class="pr pr-open">open</span><span class="muted">its proof in ${byLink} does not pass the checker (${fst ? STATUS_TEXT[fst] : "not loaded"})</span>`
            : `<span class="pr pr-open">open</span><span class="muted">no def in the package proves it</span>`;
  }
  if (d.unsafe && d.kind !== "unsafe") marker += ` <span class="k k-unsafe">@unsafe</span>`;
  const lib = inMathlib(site, p, d);
  if (lib !== null) {
    const at = modPage(lib.pkg.hash, lib.module);
    const alias = aliasFor(lib.module);
    const tm = lib.pkg.modules.find((x) => x.path === lib.module)!;
    const tid = [...declIds(tm)].find(([x]) => x.kind === "law" && x.name === lib.name)?.[1] ?? "";
    marker += `<p class="muted">Also proved in bend-mathlib as <a href="${esc(rel(modPage(p.hash, m.path), at))}#${esc(tid)}">${esc(lib.module.replace(/\.bend$/, ""))}.${esc(lib.name)}</a>: <code>import ${esc(label(lib.pkg))}/${esc(lib.module)} as ${alias}</code>, then <code>${alias}.${esc(lib.name)}</code>.</p>`;
  }
  const head = d.statement ? statementHead(d.signature) : null;
  const stmt = head === null
    ? `<pre class="code sig">${esc(d.signature)}</pre>`
    : `<pre class="code sig"><span class="muted">${esc(head)}</span>${esc(d.signature.slice(head.length))}</pre>`;
  const effects = d.effects?.length ? `<p class="muted">foreign: ${d.effects.map((e) => `<code>${esc(e)}</code>`).join(", ")}</p>` : "";
  const cs = ctors.length
    ? `<ul class="ctors">${ctors.map((c) => `<li id="${ids.get(c)!}"><code>${esc(c.name)}</code> <pre class="code sig">${esc(c.signature)}</pre>${docHtml(c.doc)}</li>`).join("")}</ul>` : "";
  return `<section class="decl" id="${id}" aria-labelledby="${id}-h">
<h3 id="${id}-h">${kindBadge(d.kind)} <a class="self" href="#${id}">${esc(d.name)}</a> ${marker}${srcLink}</h3>
${stmt}${docHtml(d.doc)}${effects}${cs}
</section>`;
}

/** Declaration anchors of a module page, in page order (the search index links to the same ids). */
export function declIds(m: Module): Map<DocDecl, string> {
  const ids = new Map<DocDecl, string>();
  // Ids the page layout itself uses; a def named `main` must not take the <main> landmark's id.
  const used = new Map<string, number>([["main", 1], ["hq", 1], ...GROUPS.map(([k]): [string, number] => [`g-${k}`, 1])]);
  const take = (d: DocDecl) => {
    const base = anchor(d.name);
    const n = used.get(base) ?? 0;
    used.set(base, n + 1);
    ids.set(d, n === 0 ? base : `${base}-${d.kind}${n > 1 ? n : ""}`);
  };
  const ctors = ctorsByType(m);
  for (const [k] of GROUPS) {
    for (const d of (m.decls ?? []).filter((x) => x.kind === k)) {
      take(d);
      if (k === "type") for (const c of ctors.get(d.name) ?? []) take(c);
    }
  }
  return ids;
}

function ctorsByType(m: Module): Map<string, DocDecl[]> {
  const out = new Map<string, DocDecl[]>();
  for (const d of m.decls ?? []) if (d.kind === "ctor" && d.type) out.set(d.type, [...(out.get(d.type) ?? []), d]);
  return out;
}

export function renderModule(site: Site, p: Package, m: Module): string {
  const path = modPage(p.hash, m.path);
  const headerHtml = m.header === null ? "" : `<div class="modhead">${docHtml(m.header)}</div>`;
  const head = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / <a href="${rel(path, pkgPage(p.hash))}">${esc(label(p))}</a> / ${esc(m.path)}</nav>
<h1>${esc(m.path)} ${m.status ? statusBadge(m.status.class, m.status.summary) : ""}</h1>
<p><a href="${HUB}/${p.hash}/${encPath(m.path)}">raw source on the hub</a> · <code>import ${esc(p.names.length ? `${p.names[0].name}@${p.names[0].version}` : p.hash)}/${esc(m.path)} as ${aliasFor(m.path)}</code></p>${headerHtml}`;
  const imports = m.imports.length
    ? `<details class="imps"><summary>${m.imports.length} import${m.imports.length > 1 ? "s" : ""}</summary><pre class="code">${m.imports.map((i) => esc(i.raw)).join("\n")}</pre></details>` : "";
  if (m.decls === null) {
    const e = m.error!;
    const body = `${head}${imports}<div class="err" role="alert"><p><strong>The reader could not load this file</strong>${e.file ? ` (at <code>${esc(e.file)}${e.line ? ":" + e.line : ""}</code>)` : ""}. What bend.ts says:</p><pre>${esc(e.message)}</pre></div>`;
    return page({ path, title: `${m.path} · ${label(p)} · Bend Docs`, body, site });
  }
  const ids = declIds(m);
  const ctorsOf = ctorsByType(m);
  const toc: string[] = [];
  const sections = GROUPS.map(([k, title]) => {
    const ds = m.decls!.filter((d) => d.kind === k);
    if (ds.length === 0) return "";
    toc.push(`<a href="#g-${k}">${title} <span class="muted">${ds.length}</span></a>`);
    return `<h2 id="g-${k}">${title}</h2>\n${ds.map((d) => declHtml(site, p, m, d, ids, k === "type" ? ctorsOf.get(d.name) ?? [] : [])).join("\n")}`;
  }).join("\n");
  const body = `${head}${imports}${toc.length ? `<nav class="toc" aria-label="Declaration kinds">${toc.join("")}</nav>` : `<p class="muted">This file declares nothing of its own.</p>`}${sections}`;
  return page({ path, title: `${m.path} · ${label(p)} · Bend Docs`, body, site });
}

/** The module's source with one anchor per line; declaration "src" links point at these. */
export function renderSource(site: Site, p: Package, m: Module): string {
  const path = srcPage(p.hash, m.path);
  const lines = (m.source ?? "").replace(/\n$/, "").split("\n");
  const body = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / <a href="${rel(path, pkgPage(p.hash))}">${esc(label(p))}</a> / <a href="${rel(path, modPage(p.hash, m.path))}">${esc(m.path)}</a> / source</nav>
<h1>${esc(m.path)} <span class="muted">source</span></h1>
<p><a href="${HUB}/${p.hash}/${encPath(m.path)}">${esc(m.path)} on the hub</a> · <a href="${rel(path, modPage(p.hash, m.path))}">documented module</a></p>
<pre class="code src">${lines.map((l, i) => `<span class="ln" id="L${i + 1}">${esc(l)}</span>`).join("")}</pre>`;
  return page({ path, title: `${m.path} source · ${label(p)} · Bend Docs`, body, site });
}

export function renderName(site: Site, name: string): string {
  const path = namePage(name);
  const rec = site.names.find((n) => n.name === name)!;
  const rows = [...rec.versions].sort((a, b) => b.ts - a.ts).map((v) => {
    const p = site.byHash.get(v.hash);
    return `<tr><td>${esc(v.version)}${v.version === rec.latest.version ? ` <span class="muted">latest</span>` : ""}</td>
<td>${p ? `<a href="${esc(rel(path, pkgPage(v.hash)))}"><code>${esc(v.hash)}</code></a>` : `<code>${esc(v.hash)}</code> <span class="muted">(not in this build)</span>`}</td>
<td>${p ? statusBadge(p.status) : ""}</td><td class="num">${date(v.ts)}</td></tr>`;
  }).join("");
  const body = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / ${esc(name)}</nav>
<h1>${esc(name)}</h1><p class="lead">${esc(rec.latest.desc)}</p><p>Owner: ${esc(rec.owner_login)}</p>
<h2>Versions</h2><div class="tablewrap"><table class="files"><thead><tr><th scope="col">Version</th><th scope="col">Hash</th><th scope="col">Status</th><th scope="col" class="num">Named on</th></tr></thead><tbody>${rows}</tbody></table></div>
${changesHtml(site, rec)}`;
  return page({ path, title: `${name} · Bend Docs`, body, site, description: rec.latest.desc });
}

/** "Changes between versions" for the versions present in this build, oldest pair first. */
function changesHtml(site: Site, rec: NameRecord): string {
  const built = [...rec.versions].filter((v) => site.byHash.has(v.hash)).sort((a, b) => versionKey(a.version).localeCompare(versionKey(b.version)));
  if (built.length < 2) return "";
  const list = (xs: string[]) => xs.map((n) => `<code>${esc(n)}</code>`).join(", ");
  const items = built.slice(1).map((v, i) => {
    const d = apiDiff(site.byHash.get(built[i].hash)!, site.byHash.get(v.hash)!);
    const parts: string[] = [];
    if (d.added.length) parts.push(`added: ${list(d.added)}`);
    if (d.removed.length) parts.push(`removed: ${list(d.removed)} <span class="st st-fails">breaking</span>`);
    if (d.changed.length) parts.push(`changed: ${list(d.changed)} <span class="st st-fails">breaking</span>`);
    return `<li><code>${esc(built[i].version)}</code> → <code>${esc(v.version)}</code>: ${parts.length > 0 ? parts.join("; ") : "no API changes"}</li>`;
  }).join("");
  return `<h2>Changes between versions</h2><ul class="edges">${items}</ul>`;
}

export function renderSearch(site: Site): string {
  const path = "search.html";
  const body = `<h1>Search</h1>
<form id="sf" class="q sform" role="search" onsubmit="return false">
<label class="vh" for="q">Query</label>
<input id="q" name="q" type="search" autocomplete="off" spellcheck="false" placeholder="add_comm, reverse, or List.append(_, Nil{})" aria-describedby="how">
<fieldset class="modes"><legend class="vh">Mode</legend>
<label><input type="radio" name="mode" value="auto" checked> auto</label>
<label><input type="radio" name="mode" value="text"> names &amp; docs</label>
<label><input type="radio" name="mode" value="shape"> law shape</label>
<label><input type="checkbox" id="lawsonly"> laws only</label></fieldset>
</form>
<p id="state" class="muted" aria-live="polite">Loading the index…</p>
<ol id="results" class="results"></ol>
<section id="how" class="how">
<h2>Law-shape search</h2>
<p>A query with a standalone <code>_</code>, with brackets or <code>==</code>, or that is one dotted name, is a <strong>shape</strong>. It finds every law (and every def whose type is an equation) whose statement contains that shape somewhere, on either side.</p>
<ul>
<li><code>_</code> matches one balanced sub-term: a name, a literal, a call like <code>List.append(a, A, xs, ys)</code>, or an operator term like <code>1n+m</code>. It never spans a comma, so it never matches two arguments.</li>
<li><strong>Leading arguments can be left out.</strong> <code>List.append(_, Nil{})</code> matches <code>List.append(a, A, xs, [])</code>: a call pattern with <var>k</var> arguments matches the <em>last</em> <var>k</var> arguments, because quantities and types come first in Bend.</li>
<li>Names match on a namespace suffix: <code>Csv.encode_row(_)</code> finds <code>lib.Csv.encode_row([])</code>, but <code>ode_row</code> finds nothing.</li>
<li>Write constructors either way. Queries are rewritten the way bend prints terms: <code>Nil{}</code> is <code>[]</code>, <code>Zero{}</code> is <code>0n</code>, <code>Succ{n}</code> is <code>1n+n</code>, and <code>Con{h, t}</code> is <code>h &lt;&gt; t</code> (a chain ending in <code>Nil{}</code> is a list literal).</li>
<li><code>lhs == rhs</code> matches a whole equation, and each side of the pattern must cover a whole side: <code>Nat.add(_, _) == Nat.add(_, _)</code> finds commutativity-shaped laws.</li>
<li>A dotted name such as <code>List.length</code> finds every statement that mentions it; an undotted name such as <code>None</code> does so in <em>law shape</em> mode.</li>
</ul>
<p>Examples: <a href="?q=List.append(_%2C%20Nil%7B%7D)">List.append(_, Nil{})</a> · <a href="?q=Nat.add(_%2C%200n)">Nat.add(_, 0n)</a> · <a href="?q=List.reverse(List.reverse(_))">List.reverse(List.reverse(_))</a> · <a href="?q=Nat.add(_%2C%20_)%20%3D%3D%20Nat.add(_%2C%20_)">Nat.add(_, _) == Nat.add(_, _)</a></p>
<h2>Names and docs</h2>
<p>Any other query searches declaration names and doc comments. Every word must appear. Exact names rank first, then prefixes, then names containing the word, then docs.</p>
<p>Statements are shown as bend ${esc(site.compiler)} prints them. The index covers ${site.groups.length} packages (latest version of each).</p>
</section>`;
  return page({ path, title: "Search · Bend Docs", body, site, scripts: ["assets/search.js"] });
}

// The package identity plain-text files use: name@version, or the full hash when anonymous.
const pkgRef = (p: Package) => (p.names.length > 0 ? `${p.names[0].name}@${p.names[0].version}` : p.hash);

/** The AI-facing `llms.txt` index of the site (see https://llmstxt.org). */
export function renderLlms(site: Site): string {
  const lines = [
    "# Bend Docs",
    `> Community documentation for every package on BendHub, the Bend 2 package hub. Statuses are \`bend --check-only\` results on bend ${site.compiler}.`,
    "",
    "- [Every proved law, one per line](lemmas.txt): package@version/module, law name, statement as bend prints it.",
    "- [Search](search.html): names, docs and law-shape search.",
    "",
    "## Packages",
  ];
  for (const g of site.groups) {
    const p = g.latest;
    const status = p.status === null ? "not checked" : STATUS_TEXT[p.status];
    lines.push(`- [${label(p)}](${pkgPage(p.hash)}): ${p.desc.replace(/\s+/g, " ").trim()} (${status}, ${p.counts.proved}/${p.counts.laws} laws proved)`);
  }
  return lines.join("\n") + "\n";
}

/** The AI-facing `lemmas.txt`: every proved law of every latest package lineage, tab-separated. */
export function renderLemmas(site: Site): string {
  const rows: { pkg: string; ref: string; module: string; line: number; name: string; signature: string }[] = [];
  for (const g of site.groups) {
    const p = g.latest;
    for (const m of p.modules) for (const d of m.decls ?? []) {
      if (d.kind === "law" && d.proved) {
        rows.push({ pkg: label(p), ref: pkgRef(p), module: m.path, line: d.line, name: d.name, signature: d.signature.replace(/\n/g, " ") });
      }
    }
  }
  rows.sort((a, b) => a.pkg.localeCompare(b.pkg) || a.module.localeCompare(b.module) || a.line - b.line);
  const packages = new Set(rows.map((r) => r.pkg)).size;
  const head = `# ${rows.length} proved laws from ${packages} packages on BendHub, checked with bend ${site.compiler}. Fields are tab-separated: package/module, law, statement.`;
  return [head, ...rows.map((r) => `${r.ref}/${r.module}\t${r.name}\t${r.signature}`)].join("\n") + "\n";
}

/** The author-facing "Document your package" page. */
export function renderAuthors(site: Site): string {
  const example = `# fastsort: a merge sort for Bend 2 with laws.
import Base

# Sorts a list of U32 in ascending order.
#
# Stable; runs in parallel on the CPU pool.
def sort(xs: List<&2, U32>) -> List<&2, U32>:
  ...
`;
  const body = `<h1>Document your package</h1>
<p class="lead">Put ordinary comments in your Bend source and publish; there is nothing else to configure.</p>
<p>No signup or config beyond your BendHub account: publish to BendHub and the next scheduled rebuild (every few hours) shows your package on this site.</p>
<h2>What the site reads</h2>
<div class="tablewrap"><table class="files">
<thead><tr><th scope="col">On the page</th><th scope="col">Where it comes from</th></tr></thead>
<tbody>
<tr><td>Package description</td><td>The hub's description for the upload; observed to be the first <code>#</code> line of the published entry file (bend-mathlib and bend-tensors). The hub's own code is not public, so this is observed.</td></tr>
<tr><td>Module header</td><td>The run of <code>#</code> lines at the top of a module, when the line after the run is blank, an <code>import</code>, or the end of the file; a run followed by a declaration is that declaration's doc instead.</td></tr>
<tr><td>Declaration docs</td><td>The contiguous <code>#</code> lines directly above a <code>def</code>, <code>law</code> or <code>type</code> (no blank line between). A line that is just <code>#</code> is a paragraph break, and backticks render as code.</td></tr>
<tr><td>Name and version</td><td><code>bend &lt;entry&gt;.bend --publish</code> publishes by hash; <code>bend link &lt;name&gt;@&lt;version&gt; 0x&lt;hash&gt;</code> names a package already on the hub, or <code>bend &lt;entry&gt;.bend --publish &lt;name&gt;@&lt;version&gt;</code> after <code>bend login</code> names it at publish time.</td></tr>
<tr><td>License</td><td>Every file named exactly <code>LICENSE</code> (the entry directory or a subdirectory): an <code>SPDX-License-Identifier</code> is read first, otherwise a known license text is matched (MIT, Apache-2.0, GPL, …). A package without one shows <code>MIT-0</code>.</td></tr>
<tr><td>Status</td><td><code>bend &lt;file&gt;.bend --check-only</code> for every <code>.bend</code> file, run on the pinned compiler (bend ${esc(site.compiler)}); each law is marked proved or open.</td></tr>
</tbody></table></div>
<h2>An example</h2>
<pre class="code">${esc(example)}</pre>
<h2>For AI agents</h2>
<p>The build writes <a href="lemmas.txt">lemmas.txt</a>, one tab-separated line per proved law (package/module, law, statement), and <a href="llms.txt">llms.txt</a>, a plain-text index of the site.</p>`;
  return page({ path: "authors.html", title: "Document your package · Bend Docs", body, site });
}
