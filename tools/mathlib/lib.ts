// Shared helpers for the bend-mathlib tools (check, lint, twins, lock).
//
// These tools parse only OUR package sources, which follow strict conventions
// (PLAN.md §3.1): top-level items start at column 0, every law is a `law name:`
// block with one-line claims, immediately followed by its `def name(...)` proof.
// Third-party code is read with tools/reader (the official parser) instead.

import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import { join, basename } from "node:path";
import { homedir } from "node:os";

export const ROOT = join(import.meta.dir, "..", "..");
export const BEND = process.env.BEND_CLI ?? join(homedir(), ".bend", "bin", "bend");
/** The whole output of a clean `bend <file> --check-only` (PLAN F18). */
export const CLEAN = "ALL PROOFS CHECK\nUse --verdict for mathematical validity.";

export type Binder = { raw: string; name: string; mark: "" | "-" | "+" | "~"; type: string; where: boolean };
export type Law = {
  name: string; line: number; doc: string[]; binders: Binder[]; claimLines: string[]; exs: string[];
  proof?: { line: number; args: string[]; body: string[] };
};
export type Def = { name: string; line: number; doc: string[]; header: string; body: string[] };
/** `stray`: lines holding a `law` the strict parser did not take (indented, one-line); the tools reject them. */
export type Module = { file: string; name: string; text: string; laws: Law[]; defs: Def[]; types: { name: string; line: number }[]; imports: string[]; stray: number[] };

// Strip `#` comments and string/char literals so scans do not match inside them.
export function stripCommentsAndStrings(src: string): string {
  let out = "";
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === "#") { while (i < src.length && src[i] !== "\n") i++; continue; }
    if (c === '"' || c === "'") {
      const q = c; out += q; i++;
      while (i < src.length && src[i] !== q && src[i] !== "\n") { if (src[i] === "\\") i++; i++; }
      out += q; i++; continue;
    }
    out += c; i++;
  }
  return out;
}

function parseBinder(line: string): Binder | null {
  const m = line.match(/^\s+for\s+([-+~]?)([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$/);
  if (!m) return null;
  const rest = m[3];
  const w = rest.search(/\swhere\s/);
  return { raw: line.trim(), mark: m[1] as Binder["mark"], name: m[2], type: (w >= 0 ? rest.slice(0, w) : rest).trim(), where: w >= 0 };
}

// 0-based index of the last physical line of a `def` header: the first line at paren depth 0 that ends with `:`.
function headerEnd(code: string[], start: number): number {
  let depth = 0;
  for (let i = start; i < code.length; i++) {
    for (const ch of code[i]) { if (ch === "(") depth++; else if (ch === ")") depth--; }
    if (depth === 0 && /:\s*$/.test(code[i])) return i;
  }
  return start;
}

export function parseModule(file: string, source?: string): Module {
  const text = source ?? readFileSync(file, "utf8");
  const lines = text.split("\n");
  // Headers are matched without comments, so `law foo: # note` is still a law; line numbers are kept.
  const code = stripCommentsAndStrings(text).split("\n");
  const mod: Module = { file, name: basename(file, ".bend"), text, laws: [], defs: [], types: [], imports: [], stray: [] };
  const lawByName = new Map<string, Law>();
  const docAbove = (i: number) => {
    const d: string[] = [];
    for (let j = i - 1; j >= 0 && lines[j].startsWith("#"); j--) d.unshift(lines[j].replace(/^#\s?/, ""));
    return d;
  };
  const block = (i: number) => { // indented body lines after a top-level header
    const b: string[] = [];
    for (let j = i + 1; j < lines.length && (lines[j].startsWith(" ") || lines[j] === ""); j++) b.push(lines[j]);
    while (b.length && b[b.length - 1] === "") b.pop();
    return b;
  };
  for (let i = 0; i < lines.length; i++) {
    const l = code[i];
    let m: RegExpMatchArray | null;
    if ((m = lines[i].match(/^import\s+(\S+)/))) mod.imports.push(m[1]);
    else if ((m = l.match(/^law\s+([A-Za-z_][A-Za-z0-9_.]*)\s*:\s*$/))) {
      const law: Law = { name: m[1], line: i + 1, doc: docAbove(i), binders: [], claimLines: [], exs: [] };
      for (const b of block(i)) {
        if (b.trim() === "") continue;
        const bd = parseBinder(b);
        if (bd) law.binders.push(bd);
        else if (/^\s+exs\s/.test(b)) law.exs.push(b.trim());
        else law.claimLines.push(b.trim());
      }
      mod.laws.push(law); lawByName.set(law.name, law);
    } else if ((m = l.match(/^(?:@unsafe\s+)?def\s+([A-Za-z_][A-Za-z0-9_.]*)(\??)\s*\((.*)$/))) {
      const name = m[1];
      const law = lawByName.get(name);
      const end = headerEnd(code, i);
      const body = block(end);
      if (law && !law.proof) {
        const args = (l.match(/^def\s+[^(]+\(([^)]*)\)/)?.[1] ?? "").split(",").map((s) => s.trim()).filter(Boolean);
        law.proof = { line: i + 1, args, body };
      } else {
        mod.defs.push({ name, line: i + 1, doc: docAbove(i), header: lines.slice(i, end + 1).join("\n"), body });
      }
    } else if ((m = l.match(/^type\s+([A-Za-z_][A-Za-z0-9_.]*)/))) mod.types.push({ name: m[1], line: i + 1 });
    else if (/(^|[^A-Za-z0-9_.])law\s+[A-Za-z_]/.test(l)) mod.stray.push(i + 1);
  }
  return mod;
}

/** The paths a file imports, read as bend's book_load reads them: the leading block of import, blank and `#` lines, trimmed. */
export function importPaths(text: string): string[] {
  const out: string[] = [];
  for (const raw of text.replace(/^﻿/, "").split("\n")) {
    const line = raw.trim();
    if (line === "" || line.startsWith("#")) continue;
    if (!/^import(\s|$)/.test(line)) break;
    const m = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(line);
    if (m !== null && m[2] !== undefined) out.push(m[1]);
  }
  return out;
}

/** A hub import (`0x…/` or `name@version/`), as opposed to a file of the importing package. */
export const isHubImport = (p: string): boolean => /^0x[0-9a-fA-F]+\//.test(p) || /^[^/]*@[^/]*\//.test(p);

/** A type-level def (`-> Data` / `-> Type`), which mathlib treats as a predicate. */
export const isPredicate = (d: Def): boolean => /->\s*(Data|Type)\s*:\s*$/.test(stripCommentsAndStrings(d.header));

/** A bad package path; each CLI reports it as a usage error (exit 2). */
export class PkgError extends Error {}

export type LockEntry = { kind: "law" | "predicate" | "def"; text: string; sha256: string; since: string | null };
export const LOCK_FORMAT = 2;

// v2 is {format, entries}; a bare entry map is v1 (and what `git show <old-tag>` returns).
export function parseLock(text: string): Record<string, LockEntry> {
  const doc = JSON.parse(text) as { entries?: unknown };
  return (doc.entries !== null && typeof doc.entries === "object" ? doc.entries : doc) as Record<string, LockEntry>;
}

export function readLock(file: string): Record<string, LockEntry> {
  return existsSync(file) ? parseLock(readFileSync(file, "utf8")) : {};
}

export function packageModules(pkgDir: string): string[] {
  let st;
  try { st = statSync(pkgDir); } catch { throw new PkgError(`no such package directory: ${pkgDir}`); }
  if (!st.isDirectory()) throw new PkgError(`not a directory: ${pkgDir}`);
  const out: string[] = [];
  const walk = (dir: string) => {
    for (const e of readdirSync(dir, { withFileTypes: true })) {
      if (e.isDirectory()) walk(join(dir, e.name));
      else if (e.name.endsWith(".bend")) out.push(join(dir, e.name));
    }
  };
  walk(pkgDir);
  return out.sort();
}

// Split `{L == R : T}` at depth 0 (parens/braces/brackets). Returns null if not an equation.
export function splitEquation(claim: string): { lhs: string; rhs: string; type: string } | null {
  const s = claim.trim();
  if (!s.startsWith("{") || !s.endsWith("}")) return null;
  const inner = s.slice(1, -1);
  let depth = 0, eq = -1, colon = -1;
  for (let i = 0; i < inner.length; i++) {
    const c = inner[i];
    if ("({[".includes(c)) depth++;
    else if (")}]".includes(c)) depth--;
    else if (depth === 0 && inner.startsWith(" == ", i) && eq < 0) eq = i;
    else if (depth === 0 && inner.startsWith(" : ", i)) colon = i;
  }
  if (eq < 0 || colon < 0 || colon < eq) return null;
  return { lhs: inner.slice(0, eq).trim(), rhs: inner.slice(eq + 4, colon).trim(), type: inner.slice(colon + 3).trim() };
}

// Names defined by the pinned compiler's Base (for the predicate Base-function check).
export async function baseNames(): Promise<Set<string>> {
  const p = Bun.spawnSync([BEND, "base"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  const out = new TextDecoder().decode(p.stdout);
  if (p.exitCode !== 0) throw new Error(`'${BEND} base' failed (exit ${p.exitCode}): ${new TextDecoder().decode(p.stderr).trim()}`);
  const names = new Set<string>();
  for (const m of out.matchAll(/^(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/gm)) names.add(m[1]);
  for (const m of out.matchAll(/^\s+([A-Z][A-Za-z0-9_]*)\{/gm)) names.add(m[1]); // constructors
  if (names.size < 10) throw new Error(`'${BEND} base' listed only ${names.size} names`);
  return names;
}

export const GENERATED_MARK = "# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---";
