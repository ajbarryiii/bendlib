// shape: law-shape search. A query such as `List.append(_, Nil{})` is tokenized
// into bracket-balanced trees and matched against law statements, where `_`
// stands for one balanced sub-term. Runs in the browser too (bundled by build.ts).

export type Tok = { t: "id" | "num" | "str" | "op" | "sep" | "wild"; v: string };
export type Group = { t: "grp"; open: "(" | "[" | "{" | "<"; items: Node[] };
export type Node = Tok | Group;

const CLOSE: Record<string, string> = { "(": ")", "[": "]", "{": "}", "<": ">" };
const OPCH = /[=<>+\-*/%&|^!:?@#~\\$;]/;
const IDSTART = /[\p{L}_]/u;
const IDCH = /[\p{L}\p{N}_./]/u;

export class ShapeError extends Error {}

/** Tokens and bracket groups; `<` right after an identifier opens a type-argument group, as bend prints `List<a, A>`. */
export function parse(src: string): Node[] {
  const root: Group = { t: "grp", open: "(", items: [] };
  const stack: Group[] = [root];
  const top = () => stack[stack.length - 1];
  let i = 0;
  let prevIdEnd = -1;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    const start = i;
    let tok: Tok | null = null;
    if (c === '"' || c === "'") {
      let j = i + 1;
      while (j < src.length && src[j] !== c) j += src[j] === "\\" ? 2 : 1;
      if (j >= src.length) throw new ShapeError(`unterminated ${c === '"' ? "string" : "character"} literal`);
      tok = { t: "str", v: src.slice(i, j + 1) };
      i = j + 1;
    } else if (/^0x[0-9a-f]+\//.test(src.slice(i, i + 40))) {
      let j = i;
      while (j < src.length && IDCH.test(src[j])) j++;
      tok = { t: "id", v: src.slice(i, j) };
      i = j;
    } else if (/[0-9]/.test(c)) {
      const m = src.slice(i).match(/^(0x[0-9a-fA-F]+|[0-9]+(\.[0-9]+)?(e[+-]?[0-9]+)?[a-z]*)/)!;
      tok = { t: "num", v: m[0] };
      i += m[0].length;
    } else if (IDSTART.test(c) || (c === "." && /^\.\.?\//.test(src.slice(i)))) {
      let j = i + 1;
      while (j < src.length && IDCH.test(src[j])) j++;
      while (j > i + 1 && src[j - 1] === ".") j--;
      const v = src.slice(i, j);
      tok = v === "_" ? { t: "wild", v } : { t: "id", v };
      i = j;
    } else if (c === "(" || c === "[" || c === "{") {
      const g: Group = { t: "grp", open: c, items: [] };
      top().items.push(g);
      stack.push(g);
      i++;
      prevIdEnd = -1;
      continue;
    } else if (c === ")" || c === "]" || c === "}") {
      const g = top();
      if (stack.length === 1 || CLOSE[g.open] !== c) throw new ShapeError(`unbalanced '${c}' at column ${i + 1}`);
      stack.pop();
      i++;
      prevIdEnd = -1;
      continue;
    } else if (c === ",") {
      tok = { t: "sep", v: "," };
      i++;
    } else if (OPCH.test(c)) {
      let j = i;
      while (j < src.length && OPCH.test(src[j])) j++;
      const v = src.slice(i, j);
      if (v === "<" && prevIdEnd === i) {
        const g: Group = { t: "grp", open: "<", items: [] };
        top().items.push(g);
        stack.push(g);
        i = j;
        continue;
      }
      if (v === ">" && top().open === "<" && stack.length > 1) {
        stack.pop();
        i = j;
        continue;
      }
      tok = { t: "op", v };
      i = j;
    } else {
      tok = { t: "op", v: c };
      i++;
    }
    top().items.push(tok);
    prevIdEnd = tok.t === "id" ? i : -1;
    if (start === i) throw new ShapeError(`cannot read column ${i + 1}`);
  }
  if (stack.length > 1) throw new ShapeError(`unclosed '${top().open}'`);
  return root.items;
}

function splitArgs(items: Node[]): Node[][] {
  const args: Node[][] = [[]];
  for (const n of items) {
    if (n.t === "sep") args.push([]);
    else args[args.length - 1].push(n);
  }
  return items.length === 0 ? [] : args;
}

function joinArgs(args: Node[][]): Node[] {
  const out: Node[] = [];
  args.forEach((a, i) => { if (i > 0) out.push({ t: "sep", v: "," }); out.push(...a); });
  return out;
}

const isCtor = (n: Node | undefined, name: string): n is Tok => n !== undefined && n.t === "id" && n.v === name;
const braces = (n: Node | undefined): n is Group => n !== undefined && n.t === "grp" && n.open === "{";

/** Rewrites Base constructors the way bend's printer shows them: Nil{} → [], Zero{} → 0n, Succ{x} → 1n+x, Con{h, t} → h <> t. */
export function normalize(items: Node[]): Node[] {
  const out: Node[] = [];
  for (let i = 0; i < items.length; i++) {
    const n = items[i], g = items[i + 1];
    if (n.t === "grp") { out.push({ ...n, items: normalize(n.items) }); continue; }
    if (braces(g)) {
      const args = splitArgs(normalize(g.items));
      if (isCtor(n, "Nil") && args.length === 0) { out.push({ t: "grp", open: "[", items: [] }); i++; continue; }
      if (isCtor(n, "Zero") && args.length === 0) { out.push({ t: "num", v: "0n" }); i++; continue; }
      if (isCtor(n, "Succ") && args.length === 1) { out.push(...succ(args[0])); i++; continue; }
      if (isCtor(n, "Con") && args.length === 2) {
        const [h, t] = args;
        if (t.length === 1 && t[0].t === "grp" && t[0].open === "[") {
          const rest = splitArgs(t[0].items);
          out.push({ t: "grp", open: "[", items: joinArgs([h, ...rest]) });
        } else out.push(...h, { t: "op", v: "<>" }, ...t);
        i++;
        continue;
      }
    }
    out.push(n);
  }
  return out;
}

function succ(arg: Node[]): Node[] {
  const lit = (k: bigint): Tok => ({ t: "num", v: `${k}n` });
  const a0 = arg[0];
  if (a0 !== undefined && a0.t === "num" && /^[0-9]+n$/.test(a0.v)) {
    const k = BigInt(a0.v.slice(0, -1)) + 1n;
    if (arg.length === 1) return [lit(k)];
    if (arg[1].t === "op" && arg[1].v === "+") return [lit(k), ...arg.slice(1)];
  }
  return [lit(1n), { t: "op", v: "+" }, ...arg];
}

export type Pattern = { src: string; items: Node[] };

/** Auto mode's test: a standalone `_`, a bracket, `==`, or one dotted name such as `List.length` is a shape. */
export const looksLikeShape = (q: string) =>
  /(^|[^\p{L}\p{N}_])_($|[^\p{L}\p{N}_])|[(){}[\]]|==/u.test(q) || /^[\p{L}_][\p{L}\p{N}_]*(\.[\p{L}_][\p{L}\p{N}_]*)+$/u.test(q.trim());

export function compile(query: string): Pattern {
  const items = normalize(parse(query));
  if (items.length === 0) throw new ShapeError("empty pattern");
  return { src: query, items };
}

const isBoundary = (n: Node | undefined) => n === undefined || n.t === "sep" || n.t === "op";
const isStop = (n: Node) => n.t === "sep" || (n.t === "op" && (n.v === "==" || n.v === ":"));

function idMatch(p: string, s: string): boolean {
  return p === s || s.endsWith("." + p) || s.endsWith("/" + p);
}

function nodeEq(p: Node, s: Node): boolean {
  if (p.t === "grp" || s.t === "grp") {
    return p.t === "grp" && s.t === "grp" && p.open === s.open && seq(p.items, 0, s.items, 0, s.items.length);
  }
  if (p.t !== s.t) return false;
  return p.t === "id" ? idMatch(p.v, s.v) : p.v === s.v;
}

// A call `f(p1..pk)` matches `f(a1..an)` when n >= k and p1..pk match the LAST k
// arguments: bend passes quantities/types first, so queries may leave them out.
function callEq(p: Group, s: Group): boolean {
  const pa = splitArgs(p.items), sa = splitArgs(s.items);
  if (pa.length === 0) return sa.length === 0;
  if (pa.length > sa.length) return false;
  const off = sa.length - pa.length;
  return pa.every((a, i) => seq(a, 0, sa[off + i], 0, sa[off + i].length));
}

/** Whether pat[pi..] matches exactly subj[si..end). */
function seq(pat: Node[], pi: number, subj: Node[], si: number, end: number): boolean {
  if (pi === pat.length) return si === end;
  if (si >= end) return false;
  const p = pat[pi];
  if (p.t === "wild") {
    if (subj[si].t === "grp" && si > 0 && subj[si - 1].t === "id") return false;
    for (let j = si + 1; j <= end; j++) {
      if (isStop(subj[j - 1])) return false;
      const nx = subj[j];
      if (j < end && nx.t === "grp" && subj[j - 1].t === "id") continue;
      if (seq(pat, pi + 1, subj, j, end)) return true;
    }
    return false;
  }
  const pg = pat[pi + 1], sg = subj[si + 1];
  if (p.t === "id" && pg?.t === "grp" && pg.open === "(" && subj[si].t === "id" && si + 1 < end && sg.t === "grp" && sg.open === "(") {
    return idMatch(p.v, (subj[si] as Tok).v) && callEq(pg, sg) && seq(pat, pi + 2, subj, si + 2, end);
  }
  return nodeEq(p, subj[si]) && seq(pat, pi + 1, subj, si + 1, end);
}

/** Whether some balanced window of `items`, at any nesting depth, matches the pattern exactly. */
export function contains(pat: Pattern, items: Node[]): boolean {
  const only = pat.items.length === 1 ? pat.items[0] : null;
  if (only !== null && only.t === "id") return mentions(only.v, items);
  const n = items.length;
  for (let s = 0; s < n; s++) {
    if (!isBoundary(items[s - 1])) continue;
    for (let e = n; e > s; e--) {
      if (e < n && !isBoundary(items[e])) continue;
      if (seq(pat.items, 0, items, s, e)) return true;
    }
  }
  for (const it of items) if (it.t === "grp" && contains(pat, it.items)) return true;
  return false;
}

function mentions(id: string, items: Node[]): boolean {
  return items.some((it) => (it.t === "grp" ? mentions(id, it.items) : it.t === "id" && idMatch(id, it.v)));
}

/** The searchable form of an equation: `lhs == rhs`, type left out. */
export function statementNodes(lhs: string, rhs: string): Node[] {
  return [...parse(lhs), { t: "op", v: "==" }, ...parse(rhs)];
}

export function matchStatement(pat: Pattern, lhs: string, rhs: string): boolean {
  return contains(pat, statementNodes(lhs, rhs));
}
