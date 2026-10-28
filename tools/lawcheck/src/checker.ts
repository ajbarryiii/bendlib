// Engine C (PLAN F22): closed instances are proved with `{==}` by `bend --check-only`.
// The checker stops at the first failing declaration, in file order, so a batch
// is re-run from the instance after each failure.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { treeRssKb } from "../../mathlib/lib.ts";

export type Item = { id: string; claim: string; hole?: boolean };

export type Outcome =
  | { r: "pass" }
  | { r: "fail"; expected: string; observed: string }
  | { r: "goal"; goal: string }
  | { r: "undecidable"; detail: string }
  | { r: "illtyped"; detail: string }
  | { r: "toolarge" }
  | { r: "timeout" }
  | { r: "unsafe"; count: number }
  | { r: "open" }
  | { r: "error"; detail: string };

export class ModuleError extends Error {}

export type Engine = {
  header: string;
  dir: string;
  bend: string;
  timeoutMs: number;
  memMb: number;
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

const GIB = 1024 ** 3;
/** Default `--mem-mb`: the resident memory one bend process may use before it is killed. */
export const DEFAULT_MEM_MB = 1024;

/** Default `--jobs`: at most 4 bend processes, fewer with few cores or under 2 GiB free memory each. */
export function defaultJobs(): number {
  // macOS counts its file cache as used, so freemem() stays tiny there and would always give 1
  const free = process.platform === "darwin" ? os.totalmem() / 2 : os.freemem();
  return Math.max(1, Math.min(4, os.availableParallelism(), Math.floor(free / (2 * GIB))));
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

export type Run = { out: string; code: number | null; timedOut: boolean; overMemory: boolean };

/** Runs one bend process in a job slot, killed at the timeout or above `E.memMb` resident memory. */
export function runBounded(E: Engine, args: string[]): Promise<Run> {
  return slot(E.jobs, async () => {
    E.runs++;
    const p = Bun.spawn(args, { env: { ...process.env, BEND_NO_TELEMETRY: "1" }, stdout: "pipe", stderr: "pipe" });
    let timedOut = false, overMemory = false;
    const timer = setTimeout(() => { timedOut = true; p.kill(); }, E.timeoutMs);
    const watch = setInterval(() => { if (treeRssKb(p.pid) > E.memMb * 1024) { overMemory = true; p.kill(9); } }, 200);
    const [o, e] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
    const code = await p.exited;
    clearTimeout(timer);
    clearInterval(watch);
    return { out: o + e, code, timedOut, overMemory };
  });
}

let counter = 0;

export async function runBatch(E: Engine, items: Item[]): Promise<Run> {
  const file = path.join(E.dir, `b${counter++}.bend`);
  const src = [E.header, ...items.map((it) => `law ${it.id}:\n  ${it.claim}\n\ndef ${it.id}():\n  ${it.hole ? "?g" : "{==}"}\n`)].join("\n");
  fs.writeFileSync(file, src);
  return runBounded(E, [E.bend, file, "--check-only"]);
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
// When only timeouts split a batch it spends at most 11 timed-out runs and 6 timeouts of wall time.
// Memory and overflow splits and reruns after a fail are not charged; the halving depth bounds them.
export const TIMEOUT_BUDGET = 6;

/** Evaluates every item; with `stopAtFail`, returns as soon as one item genuinely fails. */
export async function evaluate(E: Engine, items: Item[], stopAtFail = false, stopAtUndecidable = false, budget = { timeouts: 0 }): Promise<Map<string, Outcome>> {
  const res = new Map<string, Outcome>();
  let rest = items;
  const halves = async () => {
    const mid = Math.ceil(rest.length / 2);
    const ms = await Promise.all([rest.slice(0, mid), rest.slice(mid)].map((h) => evaluate(E, h, stopAtFail, stopAtUndecidable, budget)));
    for (const m of ms) for (const [k, v] of m) res.set(k, v);
  };
  while (rest.length > 0) {
    const { out, timedOut, overMemory } = await runBatch(E, rest);
    if (timedOut) {
      // A timed-out run may split only while the batch has seen fewer than TIMEOUT_BUDGET of them, which
      // isolates one slow instance among 32. Past that the instances stay undecided: timed out, never passed.
      budget.timeouts++;
      if (rest.length > 1 && budget.timeouts < TIMEOUT_BUDGET) await halves();
      else for (const it of rest) res.set(it.id, { r: "timeout" });
      break;
    }
    const loc = overMemory ? null : locate(out);
    if (loc === null) {
      // a batch killed over the memory limit is split like an overflow, down to the instance too large to evaluate
      if (overMemory || overflowed(out)) {
        if (rest.length === 1) res.set(rest[0].id, { r: "toolarge" });
        else await halves();
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
