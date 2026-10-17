// Search page client: names/docs search and law-shape search over search-index.json.
// Bundled by build.ts into assets/search.js; builds DOM with textContent only (hub text is untrusted).

import { compile, statementNodes, contains, looksLikeShape, ShapeError, type Node, type Pattern } from "../shape.ts";
import type { SearchIndex } from "../searchindex.ts";

type Row = SearchIndex["d"][number];
const LIMIT = 200;
const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;

let index: SearchIndex | null = null;
const parsed = new Map<number, Node[] | null>();

function nodesOf(i: number): Node[] | null {
  if (!parsed.has(i)) {
    const r = index!.d[i];
    try { parsed.set(i, statementNodes(r[5], r[6])); } catch { parsed.set(i, null); }
  }
  return parsed.get(i)!;
}


function shapeSearch(q: string, lawsOnly: boolean): number[] {
  const pat: Pattern = compile(q);
  const out: number[] = [];
  index!.d.forEach((r, i) => {
    if (r[5] === "" || (lawsOnly && r[2] !== "law")) return;
    const n = nodesOf(i);
    if (n !== null && contains(pat, n)) out.push(i);
  });
  return out.sort((a, b) => (index!.d[a][2] === "law" ? 0 : 1) - (index!.d[b][2] === "law" ? 0 : 1));
}

function textSearch(q: string, lawsOnly: boolean): number[] {
  const words = q.toLowerCase().split(/\s+/).filter(Boolean);
  const scored: [number, number][] = [];
  index!.d.forEach((r, i) => {
    if (lawsOnly && r[2] !== "law") return;
    const name = r[1].toLowerCase(), last = name.slice(Math.max(name.lastIndexOf("."), name.lastIndexOf("/")) + 1);
    const doc = r[4].toLowerCase();
    let score = 0;
    for (const w of words) {
      const s = last === w || name === w ? 100 : last.startsWith(w) ? 50 : name.includes(w) ? 20 : doc.includes(w) ? 5 : 0;
      if (s === 0) return;
      score += s;
    }
    scored.push([i, score - name.length / 100 + (r[2] === "law" ? 0.5 : 0)]);
  });
  return scored.sort((a, b) => b[1] - a[1]).map(([i]) => i);
}

function el(tag: string, cls?: string, text?: string): HTMLElement {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}

function show(hits: number[], what: string) {
  const list = $<HTMLOListElement>("results");
  list.replaceChildren();
  $("state").textContent = `${hits.length.toLocaleString("en")} ${what}${hits.length > LIMIT ? `, showing the first ${LIMIT}` : ""}.`;
  for (const i of hits.slice(0, LIMIT)) {
    const [fi, name, kind, id, doc, lhs, rhs, proved] = index!.d[i];
    const [pi, path, page] = index!.f[fi];
    const li = el("li");
    const h = el("div", "rh");
    h.append(el("span", `k k-${kind}`, kind), " ");
    const a = el("a", "rn", name) as HTMLAnchorElement;
    a.href = `${page}#${id}`;
    h.append(a);
    if (proved === 1) h.append(" ", el("span", "pr pr-yes", "proved"));
    if (proved === 0) h.append(" ", el("span", "pr pr-open", "open"));
    const where = el("span", "rw");
    const pa = el("a", "", `${index!.p[pi][0]} / ${path}`) as HTMLAnchorElement;
    pa.href = page;
    where.append(pa);
    li.append(h, where);
    if (lhs !== "") li.append(el("pre", "code sig", `${lhs} == ${rhs}`));
    if (doc !== "") li.append(el("p", "rd", doc));
    list.append(li);
  }
}

function run() {
  if (index === null) return;
  const q = $<HTMLInputElement>("q").value.trim();
  const mode = (document.querySelector('input[name="mode"]:checked') as HTMLInputElement).value;
  const lawsOnly = $<HTMLInputElement>("lawsonly").checked;
  const url = new URL(location.href);
  url.searchParams.set("q", q);
  if (mode !== "auto") url.searchParams.set("mode", mode); else url.searchParams.delete("mode");
  if (lawsOnly) url.searchParams.set("laws", "1"); else url.searchParams.delete("laws");
  history.replaceState(null, "", url);
  if (q === "") {
    $("results").replaceChildren();
    $("state").textContent = `Index loaded: ${index.d.length.toLocaleString("en")} declarations in ${index.p.length} packages.`;
    return;
  }
  const shape = mode === "shape" || (mode === "auto" && looksLikeShape(q));
  try {
    if (shape) show(shapeSearch(q, lawsOnly), "statements contain this shape");
    else show(textSearch(q, lawsOnly), "declarations match");
  } catch (e) {
    $("results").replaceChildren();
    $("state").textContent = e instanceof ShapeError ? `Not a shape: ${e.message}.` : `Search failed: ${String(e)}`;
  }
}

async function main() {
  const params = new URLSearchParams(location.search);
  $<HTMLInputElement>("q").value = params.get("q") ?? "";
  const m = params.get("mode");
  if (m === "text" || m === "shape") (document.querySelector(`input[name="mode"][value="${m}"]`) as HTMLInputElement).checked = true;
  $<HTMLInputElement>("lawsonly").checked = params.get("laws") === "1";
  let t: ReturnType<typeof setTimeout> | undefined;
  const later = () => { clearTimeout(t); t = setTimeout(run, 120); };
  $("q").addEventListener("input", later);
  $("sf").addEventListener("change", run);
  try {
    const r = await fetch("search-index.json");
    if (!r.ok) throw new Error(`HTTP ${r.status}`);
    index = (await r.json()) as SearchIndex;
  } catch (e) {
    $("state").textContent = `Could not load search-index.json (${String(e)}).`;
    return;
  }
  run();
  $("q").focus();
}

main();
