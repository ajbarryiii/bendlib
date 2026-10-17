// Engine C (PLAN F22): closed instances are proved with `{==}` by `bend --check-only`.
// The checker stops at the first failing declaration, in file order, so a batch
// is re-run from the instance after each failure.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

export type Item = { id: string; claim: string; hole?: boolean };

export type Outcome =
  | { r: "pass" }
  | { r: "fail"; expected: string; observed: string }
  | { r: "goal"; goal: string }
  | { r: "undecidable"; detail: string }
  | { r: "illtyped"; detail: string }
  | { r: "toolarge" }
  | { r: "unsafe"; count: number }
  | { r: "open" }
  | { r: "error"; detail: string };

export class ModuleError extends Error {}

export type Engine = {
  header: string;
  dir: string;
  bend: string;
  timeoutMs: number;
  jobs: number;
  runs: number;
  display: (s: string) => string;
  unsafe: string[];
};

export function bendBin(): string {
  if (process.env.BEND_BIN) return process.env.BEND_BIN;
  const home = path.join(os.homedir(), ".bend", "bin", "bend");
  return fs.existsSync(home) ? home : "bend";
}

let active = 0;
const waiting: (() => void)[] = [];

/** Runs `fn` once fewer than `jobs` bend processes (checker runs and native builds/runs) are active. */
export async function slot<T>(jobs: number, fn: () => Promise<T>): Promise<T> {
  if (active >= jobs) await new Promise<void>((res) => waiting.push(res));
  active++;
  try {
    return await fn();
  } finally {
    active--;
    waiting.shift()?.();
  }
}

let counter = 0;

export async function runBatch(E: Engine, items: Item[]): Promise<{ out: string; code: number | null; timedOut: boolean }> {
  const file = path.join(E.dir, `b${counter++}.bend`);
  const src = [E.header, ...items.map((it) => `law ${it.id}:\n  ${it.claim}\n\ndef ${it.id}():\n  ${it.hole ? "?g" : "{==}"}\n`)].join("\n");
  fs.writeFileSync(file, src);
  return slot(E.jobs, async () => {
    E.runs++;
    const p = Bun.spawn([E.bend, file, "--check-only"], {
      env: { ...process.env, BEND_NO_TELEMETRY: "1" },
      stdout: "pipe",
      stderr: "pipe",
    });
    let timedOut = false;
    const timer = setTimeout(() => { timedOut = true; p.kill(); }, E.timeoutMs);
    const [o, e] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
    const code = await p.exited;
    clearTimeout(timer);
    return { out: o + e, code, timedOut };
  });
}

type Located = { def: string; expected: string | null; observed: string | null; pointed: string; text: string };

function field(lines: string[], key: string): string | null {
  const i = lines.findIndex((l) => l.startsWith(`- ${key} : `));
  if (i < 0) return null;
  const parts = [lines[i].slice(key.length + 5)];
  for (let j = i + 1; j < lines.length && !/^(- \w+ : |Context:|Location:)/.test(lines[j]); j++) parts.push(lines[j].trim());
  return parts.join(" ");
}

export function locate(out: string): Located | null {
  const lines = out.split("\n");
  const li = lines.findIndex((l) => l.startsWith("Location: "));
  if (li < 0) return null;
  const errAt = lines.slice(0, li).lastIndexOf("Error:");
  const block = lines.slice(Math.max(0, errAt), li);
  const pointed = lines.slice(li + 1).find((l) => /^\s*\d+>\|/.test(l))?.replace(/^\s*\d+>\|/, "").trim() ?? "";
  return { def: lines[li].slice(10).trim(), expected: field(block, "expected"), observed: field(block, "observed"), pointed, text: lines.slice(Math.max(0, errAt)).join("\n").trim() };
}

/** A clean batch is exactly the two-line clean verdict; `Error: N TODOs found.` means open proofs in an import. */
export const cleanCheck = (out: string) => out.trim() === "ALL PROOFS CHECK\nUse --verdict for mathematical validity.";
const openCheck = (out: string) => /\d+ TODOs? found/.test(out);

/** The "Error: N defs rely on unsafe or foreign code:" verdict, with the relying defs. */
function unsafeVerdict(out: string): { count: number; defs: string[] } | null {
  const lines = out.split("\n");
  const i = lines.findIndex((l) => /^Error: \d+ defs? (?:rely|relies) on unsafe or foreign code:?\s*$/.test(l.trim()));
  if (i < 0) return null;
  const m = /\d+/.exec(lines[i].trim());
  const defs: string[] = [];
  for (let j = i + 1; j < lines.length; j++) {
    const d = /^- (\S+)$/.exec(lines[j].trim());
    if (d === null) break;
    defs.push(d[1]);
  }
  return { count: m === null ? 0 : Number(m[0]), defs };
}

// A huge unary Nat can overflow either the checker's own guard or the host JS
// stack, depending on the term (F31).
export const overflowed = (out: string) => /the machine stack overflowed|Maximum call stack size exceeded/.test(out);
/** Evaluates every item; with `stopAtFail`, returns as soon as one item genuinely fails. */
export async function evaluate(E: Engine, items: Item[], stopAtFail = false, stopAtUndecidable = false): Promise<Map<string, Outcome>> {
  const res = new Map<string, Outcome>();
  let rest = items;
  while (rest.length > 0) {
    const { out, timedOut } = await runBatch(E, rest);
    if (timedOut) {
      for (const it of rest) res.set(it.id, { r: "error", detail: `bend timed out after ${E.timeoutMs} ms` });
      break;
    }
    const loc = locate(out);
    if (loc === null) {
      if (!timedOut && overflowed(out)) {
        if (rest.length === 1) {
          res.set(rest[0].id, { r: "toolarge" });
        } else {
          const mid = Math.ceil(rest.length / 2);
          const halves = await Promise.all([evaluate(E, rest.slice(0, mid), stopAtFail, stopAtUndecidable), evaluate(E, rest.slice(mid), stopAtFail, stopAtUndecidable)]);
          for (const m of halves) for (const [k, v] of m) res.set(k, v);
        }
        break;
      }
      const unsafe = unsafeVerdict(out);
      if (unsafe !== null) {
        const tainted = unsafe.defs.length === 0 ? rest.map((it) => it.id) : unsafe.defs;
        const set = new Set(tainted);
        for (const it of rest) res.set(it.id, set.has(it.id) ? { r: "unsafe", count: unsafe.count } : { r: "pass" });
        break;
      }
      if (cleanCheck(out)) {
        for (const it of rest) res.set(it.id, { r: "pass" });
        break;
      }
      if (openCheck(out)) {
        for (const it of rest) res.set(it.id, { r: "open" });
        break;
      }
      const o: Outcome = { r: "error", detail: E.display(out.trim()) };
      for (const it of rest) res.set(it.id, o);
      break;
    }
    const idx = rest.findIndex((it) => it.id === loc.def);
    if (idx < 0) throw new ModuleError(E.display(loc.text));
    for (const it of rest.slice(0, idx)) res.set(it.id, { r: "pass" });
    const it = rest[idx];
    const expected = E.display(loc.expected ?? ""), observed = E.display(loc.observed ?? "");
    let o: Outcome;
    if (it.hole && loc.pointed === "?g") o = { r: "goal", goal: expected };
    else if (loc.pointed !== "{==}") o = { r: "illtyped", detail: E.display(loc.text) };
    else if (/non-inferrable term/.test(loc.observed ?? "")) {
      // A Type-valued predicate claim normalizes to Unit (inhabited, so it holds) or Empty
      // (refuted); any other normal form is not a proposition lawcheck can decide (PLAN F22).
      if (loc.expected === "Unit") o = { r: "pass" };
      else if (loc.expected === "Empty") o = { r: "fail", expected: "Empty", observed: "Unit" };
      else o = { r: "undecidable", detail: `goal ${expected} is not an equation` };
    }
    else if (loc.expected === null || loc.observed === null) o = { r: "illtyped", detail: E.display(loc.text) };
    else o = { r: "fail", expected, observed };
    res.set(it.id, o);
    if (stopAtFail && o.r === "fail") break;
    if (stopAtUndecidable && o.r === "undecidable") break;
    rest = rest.slice(idx + 1);
  }
  return res;
}

/** Splits items into batches and evaluates them concurrently. */
export async function evaluateAll(E: Engine, items: Item[]): Promise<Map<string, Outcome>> {
  // A `bend --check-only` spawn is ~0.13 s of startup, so spawn count matters more than batch
  // size: a fixed batch keeps runs independent of `--jobs` (slot(E.jobs) still caps concurrency).
  const BATCH = 32;
  const parts: Item[][] = [];
  for (let i = 0; i < items.length; i += BATCH) parts.push(items.slice(i, i + BATCH));
  const maps = await Promise.all(parts.map((c) => evaluate(E, c)));
  return new Map(maps.flatMap((m) => [...m]));
}
