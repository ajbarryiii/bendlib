#!/usr/bin/env bun
// lawcheck: search for counterexamples to the laws of a Bend 2 file before anyone
// tries to prove them, and shrink them. Passing laws are NOT proved. `mutate`
// checks the laws against every small mutant of the target's defs instead.
// usage: bun tools/lawcheck/cli.ts <file.bend> [--impl <file>] [--size N] [--max-instances N]
//          [--max-nat N] [--seed S] [--json] [--law name] [--jobs N] [--timeout MS] [--mem-mb MB]
//          [--native] [--strict] [--allow-skip name,…]
//        bun tools/lawcheck/cli.ts mutate <laws.bend> [--impl <file>] [--def <name>]
//          [--json] [--max-instances N] [--seed S] [--size N] [--jobs N] [--timeout MS] [--mem-mb MB]
//   --impl swaps a local import; --native adds engine N; --strict makes a skipped law fail
//           the gate unless named in --allow-skip, and fails on any timed-out instance.
// exit: lawcheck 0 no counterexample · 1 counterexample (or, with --strict, a disallowed skip or a timeout) · 2 error
//       mutate 0 no survivors · 1 survivor · 2 usage, load, tool error or error mutant

import * as path from "node:path";
import { BendReadError, SourceError } from "../reader/index.ts";

import { ModuleError } from "./src/checker.ts";
import {
  lawcheck, mutate, UsageError, VERSION,
  type LawResult, type MutateOptions, type MutateReport, type Options, type Report,
} from "./src/lawcheck.ts";

const USAGE = "usage: bun tools/lawcheck/cli.ts <file.bend> [--impl <file>] [--size N] [--max-instances N] [--max-nat N] [--seed S] [--json] [--law name] [--native] [--jobs N] [--timeout MS] [--mem-mb MB] [--strict] [--allow-skip name,…]";
const MUTATE_USAGE = "usage: bun tools/lawcheck/cli.ts mutate <laws.bend> [--impl <file>] [--def <name>] [--json] [--max-instances N] [--seed S] [--size N] [--jobs N] [--timeout MS] [--mem-mb MB]";

function die(msg: string, kind = "error"): never {
  if (JSON_MODE) process.stdout.write(JSON.stringify({ error: { kind, message: msg } }) + "\n");
  else process.stderr.write(`lawcheck: ${msg}\n`);
  process.exit(2);
}

let JSON_MODE = false;

function num(flag: string, v: string | undefined, min: number, usage: string): number {
  const n = Number(v);
  if (v === undefined || !/^\d+$/.test(v) || !Number.isSafeInteger(n) || n < min) die(`${flag} needs an integer ≥ ${min}\n${usage}`, "usage");
  return n;
}

function parseArgs(argv: string[]) {
  const o: Options & { file: string; json: boolean; strict: boolean; allowSkip: Set<string> } = { file: "", json: false, strict: false, allowSkip: new Set(), size: 3, maxInstances: 200, seed: 1, maxNat: 30 };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--json") o.json = true;
    else if (a === "--native") o.native = true;
    else if (a === "--strict") o.strict = true;
    else if (a === "--size") o.size = num(a, argv[++i], 0, USAGE);
    else if (a === "--max-instances") o.maxInstances = num(a, argv[++i], 1, USAGE);
    else if (a === "--max-nat") o.maxNat = num(a, argv[++i], 1, USAGE);
    else if (a === "--seed") o.seed = num(a, argv[++i], 0, USAGE);
    else if (a === "--jobs") o.jobs = num(a, argv[++i], 1, USAGE);
    else if (a === "--timeout") o.timeoutMs = num(a, argv[++i], 1, USAGE);
    else if (a === "--mem-mb") o.memMb = num(a, argv[++i], 64, USAGE);
    else if (a === "--allow-skip") {
      const v = argv[++i];
      if (v === undefined) die(`${a} needs a comma-separated list\n${USAGE}`, "usage");
      for (const nm of v.split(",")) if (nm.trim() !== "") o.allowSkip.add(nm.trim());
    }
    else if (a === "--law" || a === "--impl") {
      const v = argv[++i];
      if (v === undefined) die(`${a} needs a value\n${USAGE}`, "usage");
      if (a === "--law") o.law = v; else o.impl = v;
    } else if (a === "-h" || a === "--help") {
      console.log(USAGE);
      process.exit(0);
    } else if (a.startsWith("-")) die(`unknown flag ${a}\n${USAGE}`, "usage");
    else if (o.file === "") o.file = a;
    else die(`one file only (got ${o.file} and ${a})\n${USAGE}`, "usage");
  }
  if (o.file === "") die(`no file given\n${USAGE}`, "usage");
  return o;
}

function parseMutateArgs(argv: string[]) {
  const o: MutateOptions & { file: string; json: boolean } = { file: "", json: false, size: 3, maxInstances: 50, seed: 1 };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--json") o.json = true;
    else if (a === "--size") o.size = num(a, argv[++i], 0, MUTATE_USAGE);
    else if (a === "--max-instances") o.maxInstances = num(a, argv[++i], 1, MUTATE_USAGE);
    else if (a === "--seed") o.seed = num(a, argv[++i], 0, MUTATE_USAGE);
    else if (a === "--jobs") o.jobs = num(a, argv[++i], 1, MUTATE_USAGE);
    else if (a === "--timeout") o.timeoutMs = num(a, argv[++i], 1, MUTATE_USAGE);
    else if (a === "--mem-mb") o.memMb = num(a, argv[++i], 64, MUTATE_USAGE);
    else if (a === "--def" || a === "--impl") {
      const v = argv[++i];
      if (v === undefined) die(`${a} needs a value\n${MUTATE_USAGE}`, "usage");
      if (a === "--def") o.def = v; else o.impl = v;
    } else if (a === "-h" || a === "--help") {
      console.log(MUTATE_USAGE);
      process.exit(0);
    } else if (a.startsWith("-")) die(`unknown flag ${a}\n${MUTATE_USAGE}`, "usage");
    else if (o.file === "") o.file = a;
    else die(`one file only (got ${o.file} and ${a})\n${MUTATE_USAGE}`, "usage");
  }
  if (o.file === "") die(`no file given\n${MUTATE_USAGE}`, "usage");
  return o;
}

const MARK = { pass: "✓", fail: "✗", skip: "~", error: "!" } as const;

function human(r: Report): string {
  const w = Math.max(...r.laws.map((l) => l.name.length), 4);
  const pad = " ".repeat(w + 3);
  const out = [`lawcheck ${r.version} · ${path.relative(process.cwd(), r.file)} · bend ${r.bend} · seed ${r.seed} · size ${r.size} · ≤${r.maxInstances} instances/law`];
  for (const l of r.laws) {
    const head = `${MARK[l.status]} ${l.name.padEnd(w)}  `;
    const nv = l.native;
    const native = nv === undefined ? "" : nv.skip !== undefined
      ? `, native skipped: ${nv.skip.replace(/\s+/g, " ")}`
      : `, native ${nv.checked} compared${nv.disagreements.length ? `, ${nv.disagreements.length} DISAGREE` : ""}`;
    const extra = (l.status === "pass" || l.status === "fail" ? dropped(l) : [l.tooLarge ? `, ${l.tooLarge} too large to evaluate` : "", l.timedOut ? `, ${l.timedOut} timed out` : ""].join("")) + native;
    out.push(head + lawLine(l, r) + extra);
    for (const x of nv?.disagreements ?? []) {
      out.push(`${pad}native DISAGREES: engine C ${x.engineC}, native ${x.engineN ? "1" : "0"} · ${x.bindings.map((b) => `${b.name} = ${b.value}`).join(", ")} · repro ${x.repro}`);
    }
    if (l.status === "fail" && l.counterexample) {
      const c = l.counterexample;
      for (const b of [...c.types, ...c.bindings]) out.push(`${pad}${b.name} = ${b.value}`);
      for (const pr of c.premises ?? []) out.push(`${pad}premise  ${pr}  (holds)`);
      if (c.lhs && c.rhs) {
        out.push(`${pad}lhs  ${c.lhs.term} = ${c.lhs.value}`);
        out.push(`${pad}rhs  ${c.rhs.term} = ${c.rhs.value}`);
      } else {
        out.push(`${pad}claim  ${c.claim}`);
        if (c.goal) out.push(`${pad}goal   ${c.goal}`);
      }
      if (c.expected !== undefined) out.push(`${pad}checker: expected ${c.expected} · observed ${c.observed}`);
    }
    if (l.status === "error" && l.reason?.includes("\n")) out.push(...l.reason.split("\n").slice(1).map((s) => pad + s));
  }
  const n = (s: LawResult["status"]) => r.laws.filter((l) => l.status === s).length;
  out.push(`${r.laws.length} laws: ${n("pass")} ✓ · ${n("fail")} ✗ · ${n("skip")} ~ · ${n("error")} !  (${r.checkerRuns} checker runs; batches in ${r.tmpDir})`);
  out.push("note: ✓ means no counterexample among the instances tried; it proves nothing about all inputs.");
  return out.join("\n");
}

/** The generated instances that were not evaluated, so the law's line adds up to `generated`. */
function dropped(l: LawResult): string {
  const parts = [l.premiseFalse ? `${l.premiseFalse} with premises false` : "", l.tooLarge ? `${l.tooLarge} too large to evaluate` : "", l.timedOut ? `${l.timedOut} timed out` : ""].filter((x) => x !== "");
  return parts.length === 0 ? "" : `, ${parts.join(", ")} (${l.generated} generated)`;
}

function lawLine(l: LawResult, r: Report): string {
  switch (l.status) {
    case "pass": return `${l.instances} instance${l.instances === 1 ? "" : "s"}, 0 failures (sizes ≤ ${r.size})`;
    case "skip": return `skipped: ${l.reason}`;
    case "error": return `error: ${l.reason?.split("\n")[0]}`;
    case "fail": {
      const c = l.counterexample!;
      const orig = c.shrinkSteps > 0 ? ` from ${c.original.map((b) => `${b.name} = ${b.value}`).join(", ")} in ${c.shrinkSteps} step${c.shrinkSteps === 1 ? "" : "s"}` : "";
      const kind = l.claim === "refutation" ? "all premises hold (the law says they cannot)" : "counterexample";
      return `${kind} (shrunk${orig}); ${l.failures}/${l.instances} instances failed`;
    }
  }
}

function humanMutate(r: MutateReport): string {
  const w = Math.max(...r.defs.map((d) => d.name.length), 4);
  const impl = r.impl === null ? "in-file" : `impl ${path.basename(r.impl)}`;
  const out = [`lawcheck mutate ${r.version} · ${path.relative(process.cwd(), r.file)} (${impl}) · bend ${r.bend} · ≤${r.maxInstances} instances/law`];
  let survivors = 0, unknown = 0, valid = 0;
  for (const d of r.defs) {
    const killed = d.mutants.filter((m) => m.status === "killed").length;
    const survived = d.mutants.filter((m) => m.status === "survived").length;
    const unknowns = d.mutants.filter((m) => m.status === "unknown").length;
    const invalid = d.mutants.filter((m) => m.status === "invalid").length;
    const ok = killed + survived + unknowns;
    survivors += survived;
    unknown += unknowns;
    valid += ok;
    if (ok === 0) out.push(`${d.name.padEnd(w)}  no valid mutants: not tested${invalid ? ` · ${invalid} invalid` : ""}`);
    else out.push(`${d.name.padEnd(w)}  ${killed}/${ok} valid mutants killed · ${survived} survived${unknowns ? ` · ${unknowns} unknown` : ""} · ${invalid} invalid`);
    for (const m of d.mutants) if (m.status === "survived") out.push(`${" ".repeat(w + 2)}survived  ${m.op}  line ${m.line}  ${m.before} → ${m.after}`);
    for (const m of d.mutants) if (m.status === "unknown") out.push(`${" ".repeat(w + 2)}unknown   ${m.op}  line ${m.line}  ${m.before} → ${m.after}${m.detail ? `  (${m.detail})` : ""}`);
  }
  if (survivors === 0 && unknown === 0) out.push(valid === 0 ? "no valid mutants: nothing was tested." : "no survivors: every valid mutant broke a law.");
  else if (survivors === 0) out.push(`${unknown} unknown mutant(s): a law that passed on the unmutated code was not evaluated on them (not survivors).`);
  else out.push(`${survivors} survivor(s): your laws do not pin these changes. A survivor can also be an equivalent mutant (same behaviour); check it by hand.`);
  return out.join("\n");
}

async function runLawcheck(argv: string[]) {
  const o = parseArgs(argv);
  let report: Report;
  try {
    report = await lawcheck(o.file, o);
  } catch (e) {
    if (e instanceof UsageError) die(`${e.message}\n${USAGE}`, "usage");
    if (e instanceof BendReadError) die(`cannot load ${o.file}:\n${e.message}`, "load");
    if (e instanceof SourceError) die(e.message, "source");
    if (e instanceof ModuleError) die(`${o.file} does not type-check, so no instance can be evaluated:\n${e.message}`, "module");
    die(e instanceof Error ? e.message : String(e), "error");
  }
  console.log(o.json ? JSON.stringify(report, null, 2) : human(report));
  const has = (s: LawResult["status"]) => report.laws.some((l) => l.status === s);
  const skipped = report.laws.filter((l) => l.status === "skip" && !o.allowSkip.has(l.name));
  // --strict: a skipped law is a gap in the gate unless explicitly allowed, and a timed-out instance
  // always is: it may be the counterexample (README).
  const slow = o.strict ? report.laws.filter((l) => (l.timedOut ?? 0) > 0) : [];
  if (slow.length > 0 && !o.json) console.log(`strict: ${slow.map((l) => `${l.name} (${l.timedOut} timed out)`).join(", ")}: timed-out instances fail --strict; raise --timeout`);
  process.exit(has("fail") || (o.strict && (skipped.length > 0 || slow.length > 0)) ? 1 : has("error") ? 2 : 0);
}

async function runMutate(argv: string[]) {
  const o = parseMutateArgs(argv);
  let report: MutateReport;
  try {
    report = await mutate(o.file, o);
  } catch (e) {
    if (e instanceof UsageError) die(`${e.message}\n${MUTATE_USAGE}`, "usage");
    if (e instanceof BendReadError) die(`cannot load ${o.file}:\n${e.message}`, "load");
    if (e instanceof SourceError) die(e.message, "source");
    if (e instanceof ModuleError) die(`${o.file} does not type-check:\n${e.message}`, "module");
    die(e instanceof Error ? e.message : String(e), "error");
  }
  console.log(o.json ? JSON.stringify(report, null, 2) : humanMutate(report));
  const ms = report.defs.flatMap((d) => d.mutants);
  const valid = ms.filter((m) => m.status !== "invalid");
  // Nothing valid to test, or a mutant the laws could not decide, is "no answer": exit 2, so a CI
  // gate cannot pass on nothing (README).
  process.exit(valid.length === 0 || valid.some((m) => m.status === "unknown") ? 2 : valid.some((m) => m.status === "survived") ? 1 : 0);
}

const argv = process.argv.slice(2);
JSON_MODE = argv.includes("--json");
if (argv.includes("--version")) {
  console.log(`lawcheck ${VERSION}`);
  process.exit(0);
}
if (argv[0] === "mutate") await runMutate(argv.slice(1));
else await runLawcheck(argv);
