// lock: PUBLIC_API.lock makes published statements append-only (PLAN.md §3.1 rule 2).
// Entries: every public (non-`internal_`) law and def; the normalized text covers `for` binders,
// `exs` clauses and the claim, or the def header+body. An entry with "since" set was published and
// may never change or disappear; unpublished entries follow the source. The document is
// `{format, entries}` (v2); a bare entry map is v1, which is also what `git show <old-tag>` returns.
//
// usage: bun tools/mathlib/lock.ts [pkgdir] (--check [--against <tag>] | --update | --freeze <version>)
// exit: 0 ok · 1 a published entry changed or vanished, the lock is stale (--check), a law is not in
//       the strict form, a key is defined twice, or `--against` disagrees · 2 usage

import { createHash } from "node:crypto";
import { writeFileSync } from "node:fs";
import { join, relative, resolve, sep } from "node:path";
import { LOCK_FORMAT, PkgError, ROOT, isPredicate, packageModules, parseLock, parseModule, readLock, type Def, type Law, type LockEntry } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/lock.ts [pkgdir] (--check [--against <tag>] | --update | --freeze <version>)";
const usage = (msg: string): never => { console.error(`lock: ${msg}\n${USAGE}`); process.exit(2); };

const lawText = (law: Law): string => [...law.binders.map((b) => b.raw), ...law.exs, ...law.claimLines].join("\n");
const defText = (d: Def): string => [d.header.trim(), ...d.body.map((l) => l.trim()).filter(Boolean)].join("\n");
const defKind = (d: Def): LockEntry["kind"] => isPredicate(d) ? "predicate" : "def";

/** Every entry published in an older lock must be byte-identical in the current one (additions are fine). */
export function lockAgainstErrors(old: Record<string, LockEntry>, current: Record<string, LockEntry>): string[] {
  const errors: string[] = [];
  for (const [k, e] of Object.entries(old)) {
    if (!e.since) continue;
    const c = current[k];
    if (!c || c.kind !== e.kind || c.text !== e.text || c.sha256 !== e.sha256 || c.since !== e.since) {
      errors.push(`${k} (published in ${e.since}) is not byte-identical in the current lock`);
    }
  }
  return errors;
}

function main(): void {
  const args = process.argv.slice(2);
  const pkg = resolve(args.find((a, i) => !a.startsWith("--") && args[i - 1] !== "--freeze" && args[i - 1] !== "--against")
    ?? join(ROOT, "packages", "bend-mathlib"));
  const mode = args.find((a) => ["--check", "--update", "--freeze"].includes(a));
  if (!mode) usage("one of --check | --update | --freeze <version> is required");
  const hasAgainst = args.includes("--against");
  const against = hasAgainst ? args[args.indexOf("--against") + 1] : null;
  if (hasAgainst && mode !== "--check") usage("--against needs --check");
  if (hasAgainst && !against) usage("--against needs a git tag");

  const current = new Map<string, Omit<LockEntry, "since">>();
  let files: string[];
  try { files = packageModules(pkg); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
  const unreadable: string[] = [];
  for (const file of files) {
    const mod = parseModule(file);
    for (const line of mod.stray) unreadable.push(`${relative(ROOT, file)}:${line}: a law outside the column-0 'law name:' form is not locked`);
    const put = (name: string, kind: LockEntry["kind"], text: string) => {
      // Keys are `<module>.<name>`, so two modules with one basename would share entries.
      if (current.has(`${mod.name}.${name}`)) unreadable.push(`${relative(ROOT, file)}: '${mod.name}.${name}' is defined twice in the package`);
      current.set(`${mod.name}.${name}`, { kind, text, sha256: createHash("sha256").update(text).digest("hex") });
    };
    for (const law of mod.laws) if (!law.name.startsWith("internal_")) put(law.name, "law", lawText(law));
    for (const d of mod.defs) if (!d.name.startsWith("internal_")) put(d.name, defKind(d), defText(d));
  }

  for (const u of unreadable) console.log(u);
  if (unreadable.length) process.exit(1);

  const lockFile = join(pkg, "PUBLIC_API.lock");
  const locked = readLock(lockFile);
  const broken = Object.entries(locked)
    .filter(([k, e]) => e.since !== null && current.get(k)?.sha256 !== e.sha256)
    .map(([k, e]) => `${k} (published in ${e.since}) ${current.has(k) ? "changed" : "was removed"}`);
  for (const b of broken) console.log(`frozen entry violated: ${b}`);
  if (broken.length) process.exit(1);

  if (mode === "--check") {
    const unlisted = [...current.keys()].filter((k) => !(k in locked) || (locked[k].since === null && locked[k].sha256 !== current.get(k)!.sha256));
    for (const k of unlisted) console.log(`not in lock (run --update): ${k}`);
    const gone = Object.keys(locked).filter((k) => locked[k].since === null && !current.has(k));
    for (const k of gone) console.log(`no longer in the source (run --update): ${k}`);
    console.log(`${Object.keys(locked).length} entries locked, ${Object.values(locked).filter((e) => e.since).length} published`);
    let bad = unlisted.length > 0 || gone.length > 0;
    if (against) {
      const rel = relative(ROOT, lockFile).split(sep).join("/");
      const p = Bun.spawnSync(["git", "show", `${against}:${rel}`], { cwd: ROOT });
      if (p.exitCode !== 0) {
        console.log(`against: cannot read ${rel} at ${against}`);
        bad = true;
      } else {
        const errs = lockAgainstErrors(parseLock(new TextDecoder().decode(p.stdout)), locked);
        for (const e of errs) console.log(`against ${against}: ${e}`);
        console.log(`against ${against}: ${errs.length} check(s) failed`);
        if (errs.length) bad = true;
      }
    }
    process.exit(bad ? 1 : 0);
  }

  const next: Record<string, LockEntry> = {};
  for (const [k, e] of Object.entries(locked)) if (e.since !== null) next[k] = e;
  for (const [k, e] of current) if (!(k in next)) next[k] = { ...e, since: null };
  if (mode === "--freeze") {
    const version = args[args.indexOf("--freeze") + 1];
    if (!/^\d+\.\d+\.\d+\.\d+$/.test(version ?? "")) { console.error("--freeze needs a version like 0.1.0.0"); process.exit(2); }
    for (const e of Object.values(next)) if (e.since === null) e.since = version;
  }
  const sorted = Object.fromEntries(Object.keys(next).sort().map((k) => [k, next[k]]));
  writeFileSync(lockFile, JSON.stringify({ format: LOCK_FORMAT, entries: sorted }, null, 2) + "\n");
  console.log(`wrote ${lockFile}: ${Object.keys(sorted).length} entries`);
}

if (import.meta.main) main();
