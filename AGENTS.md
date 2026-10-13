# AGENTS.md — bend

---

## RULE 1 – ABSOLUTE (DO NOT EVER VIOLATE THIS)

You may NOT delete any file or directory unless I explicitly give the exact command **in this session**.

- This includes files you just created (tests, tmp files, scripts, etc.).
- You do not get to decide that something is "safe" to remove.
- If you think something should be removed, stop and ask. You must receive clear written approval **before** any deletion command is even proposed.

Treat "never delete files without permission" as a hard invariant.

---

## IRREVERSIBLE GIT & FILESYSTEM ACTIONS

Absolutely forbidden unless I give the **exact command and explicit approval** in the same message:

- `git reset --hard`
- `git clean -fd`
- `rm -rf`
- Any command that can delete or overwrite code/data

Rules:

1. If you are not 100% sure what a command will delete, do not propose or run it. Ask first.
2. Prefer safe tools: `git status`, `git diff`, `git stash`, copying to backups, etc.
3. After approval, restate the command verbatim, list what it will affect, and wait for confirmation.
4. When a destructive command is run, record in your response:
   - The exact user text authorizing it
   - The command run
   - When you ran it

If that audit trail is missing, then you must act as if the operation never happened.

---

## Project Architecture

bendlib is the foundation library for Bend 2 (https://github.com/bendlang/bend). Design, verified
facts F1–F34 about bend 2.0.27 (re-run on 2.0.32), and the build order are in `PLAN.md`; cite a fact ID in a
why-comment instead of re-explaining it.

- **A) bend-mathlib** (`packages/bend-mathlib`, Bend): proved lemmas and Base-only predicates,
  published on BendHub. Its public API is append-only (`PUBLIC_API.lock`, PLAN §3.1).
- **B) lawcheck** (`tools/lawcheck`, TypeScript/Bun): finds counterexamples to laws by having
  the bend checker evaluate closed instances (PLAN §4).
- **C) Bend Docs** (`tools/docs`, TypeScript/Bun): static docs for every hub package, rebuilt on a
  schedule (GitHub runs it every few hours) and deployed to https://bendlib.github.io/bendlib/ by
  `.github/workflows/docs.yml` (PLAN §5).
- **Keystone `@bendlib/reader`** (`tools/reader`): reads Bend with the official `bend.ts` of the
  installed compiler version. lawcheck and docs sit on it.
- **mathlib tools** (`tools/mathlib`): `check`, `lint`, `twins`, `lock`, `index`, `hash`, `release`.

---

## Repo Layout

```
bend/
├── PLAN.md  README.md  AGENTS.md  RELEASES.md  LICENSE  toolchain.json (pinned bend + sha256)
├── .beads/                     issue tracking (br); commit it with code
├── .github/workflows/          ci.yml (gates, nightly newest-compiler job), docs.yml (site),
│                               lawcheck-release.yml (tag-triggered lawcheck binaries)
├── packages/bend-mathlib/      all.bend equal.bend bool.bend nat.bend list.bend LICENSE
│                               PUBLIC_API.lock README.md (generated)
├── tools/
│   ├── comments.ts             comment lint (see "Comments" below)
│   ├── install-bend.ts         installs the pinned compiler
│   ├── mathlib/                check lint twins lock index hash release (+ fixtures, tools.test.ts)
│   ├── reader/                 @bendlib/reader (src/, test/, cli.ts)
│   ├── lawcheck/               cli.ts, src/{lawcheck,checker,values,terms,types,mutate}.ts, test/
│   └── docs/                   build.ts, src/, assets/, test/  (dist/ and .cache/ are git-ignored)
├── .claude-plugin/marketplace.json  the Claude Code marketplace; plugins/bend-mathlib/ is its plugin (the agent skill)
├── examples/demo/              before.bend after.bend demo.gif demo.mp4 demo.sh
└── research/
    ├── experiments/            the evidence behind F1–F34
    └── candidates/             lawchecked statements waiting to be proved (mathlib-0.2/, perm/, predicates/)
```

---

## Generated Files — NEVER Edit Manually

| File | Regenerate with |
|---|---|
| `packages/bend-mathlib/README.md` | `bun tools/mathlib/index.ts packages/bend-mathlib bend-mathlib <latest version in RELEASES.md>` |
| Everything below the line `# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---` in a mathlib module | `bun tools/mathlib/twins.ts packages/bend-mathlib` |
| `packages/bend-mathlib/PUBLIC_API.lock` | `bun tools/mathlib/lock.ts packages/bend-mathlib --update` (entries with a `since` version are frozen forever; only `--freeze` in a release sets `since`) |
| `tools/reader/test/golden/*.json` | `bun tools/reader/test/golden.ts`, only after reviewing the diff a compiler bump caused |
| `RELEASES.md` rows | `tools/mathlib/release.ts` (owner) |
| `tools/docs/dist/` (git-ignored) | `bun tools/docs/build.ts` |

---

## Code Editing Discipline

- Do **not** run scripts that bulk-modify code (codemods, invented one-off scripts, giant `sed`/regex refactors).
- Large mechanical changes: break into smaller, explicit edits and review diffs.
- Subtle/complex changes: edit by hand, file-by-file, with careful reasoning.

---

## Backwards Compatibility & File Sprawl

We optimize for a clean architecture now, not backwards compatibility.

- No "compat shims" or "v2" file clones.
- When changing behavior, migrate callers and remove old code.
- New files are only for genuinely new domains that don't fit existing modules.
- The bar for adding files is very high.

---

## Issue Tracking with br (Beads)

All issue tracking goes through **Beads**. No other TODO systems.

Key invariants:

- `.beads/` is authoritative state and **must always be committed** with code changes.
- Do not edit `.beads/*.jsonl` directly; only via `br`.

### Basics

Check, create, update and close:

```bash
br ready --json
br create "Issue title" -t bug|feature|task -p 0-4 --json
br create "Issue title" -p 1 --deps discovered-from:br-123 --json
br update br-42 --status in_progress --json
br update br-42 --priority 1 --json
br close br-42 --reason "Completed" --json
```

Types: `bug`, `feature`, `task`, `epic`, `chore`. Priorities: `0` critical, `1` high, `2` medium (default), `3` low, `4` backlog.

Never: markdown TODO lists, other trackers, or duplicate tracking.

---

## Working the beads (agents)

The beads are the work queue. Each one is self-contained: context, steps, acceptance commands with
their expected output, and what not to do. Read the whole bead before starting.

1. `br ready --label agent --json` lists the beads agents may take; take the highest-priority one.
   Beads labelled `owner` need contact with people or a purchase: never start them. Beads labelled
   `release` publish to BendHub, `bend link`, tag or create GitHub releases: take them only when
   every dependency is closed and the full gate is green on `origin/main` (PLAN §9 D-release). `br show <id>`, then `br update <id> --status in_progress`.
2. Environment: `~/.bend/bin/bend version` must print `bend 2.0.37` (else `bun tools/install-bend.ts`).
   Run commands from the repository root. For Bend itself: `bend guide`, `bend base <Name>` (e.g.
   `bend base List`), and `~/.claude/skills/bend2-mega-skill/references/` (`CHEATSHEET.md`,
   `LAWS-AND-PROOFS.md`, `PROOF-COOKBOOK.md`, `ERROR-TAXONOMY.md`).
3. The full gate, the same list as `.github/workflows/ci.yml`. Run it before every commit:
   ```sh
   bun test tools/                 # includes a docs end-to-end test against the live hub (minutes)
   bun tools/comments.ts
   bun tools/mathlib/devlib.ts --check
   bun tools/mathlib/devlib.ts run -- bun tools/mathlib/check.ts packages/bend-mathlib
   for m in $(find packages/bend-mathlib -name '*.bend' | sort); do bun tools/mathlib/devlib.ts run -- bun tools/lawcheck/cli.ts "$m" --max-instances 100 --strict --allow-skip cong2,eq_true_of_ne_false,foldl_eq_foldr,foldl_eq_foldr_sym,foldl_op_eq_foldr_op,foldl_op_eq_foldr_op_sym,le_antisymm_eq,le_total,le_total_d,le_total_of_not_le,le_total_true,le_total_true_sym,le_trans3,le_trans4,maybe_bind_assoc,maybe_bind_assoc_sym,maybe_bind_map,maybe_bind_map_sym,maybe_map_bind,maybe_map_bind_sym,maybe_map_compose,maybe_map_compose_sym,maybe_map_pure,maybe_map_pure_sym,maybe_pure_bind,maybe_pure_bind_sym,op_assoc4,op_assoc4_sym,op_comm3,op_comm3_sym,op_four,op_four_sym,op_left_comm,op_left_comm_sym,op_right_comm,op_right_comm_sym,subst || exit 1; done
   bun tools/mathlib/lint.ts packages/bend-mathlib --erasure
   bun tools/mathlib/twins.ts packages/bend-mathlib --check
   bun tools/mathlib/check.ts packages/bendlib-kernel-list
   bun tools/mathlib/lint.ts packages/bendlib-kernel-list --kernel --erasure
   bun tools/mathlib/twins.ts packages/bendlib-kernel-list --check
   bun tools/mathlib/lock.ts packages/bend-mathlib --check
   tag=$(git describe --tags --match 'bend-mathlib-v*' --abbrev=0 2>/dev/null || true)
   if [ -n "$tag" ]; then bun tools/mathlib/lock.ts packages/bend-mathlib --check --against "$tag"; else echo "no bend-mathlib-v* tag yet; skipping --against"; fi
   bun tools/mathlib/index.ts packages/bend-mathlib bend-mathlib 0.7.3.0 --check   # version: latest row of RELEASES.md
   ```
4. One commit per bead: `<area>: <what>` and a last line `Closes <id>`; run the full gate first.
   `br sync --flush-only`, `git add .beads/`, commit, then `git pull --rebase`, `git push`, and
   `git status` must show "up to date with origin". Never force-push or rewrite history.
5. Close with evidence: `br close <id> --reason "<each acceptance command and its last output lines>"`.
6. **When a bead cannot be finished** (a proof that will not check, a statement lawcheck refutes, a
   missing capability): never weaken a statement, a test, an assertion or a gate to get green. Keep
   the bead open, record what you tried and the exact error with `br comments add <id> "..."`, and
   take the next bead. Partial work that passes the full gate may be committed; the comment says
   what is missing.
7. **Never**: publish, name or link anything on BendHub (`--publish`, `bend link`, `bend login`);
   create git tags or GitHub releases; change an entry of `PUBLIC_API.lock` that has a `since`;
   put `@unsafe`, `?holes` or `def f?(` into `packages/`; delete files (RULE 1); read or print
   `~/.bend/bendai.json` (`~/.bend/bender.json` before bend 2.0.36); contact anyone; install anything globally.
8. New work you discover: `br create "<title>" -p 2 --deps discovered-from:<id> --description-file <file>`
   with a self-contained description.

### Adding a lemma to bend-mathlib

1. Copy the statement **verbatim** from the candidate file the bead names
   (`research/candidates/mathlib-0.2/`). Put the law and its proof into the target module, above
   the line `# --- generated: _sym twins ...` (never below it). Layout, exactly:
   ```python
   # <One sentence, ending with a period.>
   law name:
     for x: Nat
     {claim on exactly one line}

   def name(x):
     <proof>
   ```
   The proof `def` comes directly after its law. Helpers are named `internal_<something>` and go
   above their first use (Bend resolves definitions in source order).
2. `bun tools/lawcheck/cli.ts packages/bend-mathlib/<module>.bend --law <name>` must print `✓` (or
   `~ skipped` for template binders). A `✗` means the statement is false: stop and comment.
3. Prove it. While working, a `?goal` hole makes the checker print the goal; none may remain.
   `~/.bend/bin/bend packages/bend-mathlib/<module>.bend --check-only` must print exactly
   `ALL PROOFS CHECK` and `Use --verdict for mathematical validity.`
4. `bun tools/mathlib/lint.ts packages/bend-mathlib --erasure`: for each "can be erased" finding,
   change `for x:` to `for -x:` and re-check (PLAN F26).
5. Regenerate: `bun tools/mathlib/twins.ts packages/bend-mathlib`, then
   `bun tools/mathlib/lock.ts packages/bend-mathlib --update`, then the index command from step 3
   of the bead workflow above without `--check`.
6. Run the full gate.

Proof patterns already in the package, to copy:
- Induction with a rewrite by the induction hypothesis: `add_assoc` (nat.bend), `append_assoc` (list.bend).
- Two-argument induction with rewrites by earlier lemmas: `add_comm`.
- Order facts with impossible cases: `le_trans`, `le_antisymm`, `lt_trans`
  (`Empty.absurd(<goal>, internal_false_ne_true(h))`).
- Case splits on Bool: any law in bool.bend.
- A rewrite `%e : P` replaces the right side of `e` with its left side inside `P`; `_` in `P`
  marks the spot. `Equal.sym(T, l, r, e)` flips an equation.

---

## Optional helpers

`bv --robot-triage`, `cass search … --robot`, `cm context … --json`; never run them bare (TUI).

---

## Honest Work and Anti-Ceremony (binding for agents and humans alike)

The purpose of agent work here is working, deployable capability. Process
serves that outcome and never becomes the product.

- A process artifact (certificate, ledger, dashboard, matrix, meta-report,
  speculative check) may be created only if it names a concrete consumer,
  the named feature it gates, the observed defect class justifying it, and
  its deletion condition. Otherwise it does not get created. Boundary test:
  if running code branches on it, it is product; if only humans and status
  reports read it, it is process and the creation-gate rule above applies;
  code written just to flip this answer counts as the pathology, not as a
  consumer. Sole exception: a minimal
  integrity/recovery control (crash-recovery state, provenance snapshot) is
  legitimate when it prevents a named evidence-loss or corruption mode and
  is necessary and minimal.
- Real code + real tests in the same unit of work. Forbidden: faked tests,
  fixtures/mocks presented as live proof, weakened assertions, golden
  regeneration to force green, hard-coded success paths, placeholder macros
  in commits, editing the spec instead of implementing it, narrowing scope
  while claiming full success.
- No self-certification: work is closed by an independent verifier citing
  evidence at an exact revision. Solo sessions re-verify by re-execution and
  state what was not independently verified.
- A typed refusal beats a fabricated result and is less valuable than the
  real capability; refusal-only work stays open and says so.
- Truthful null results ("checked X, found no material increment") are
  successful outcomes. Unsupported claims are worse than silence.
- Metrics predeclare denominator and countermetric; agreement between
  agents may raise confidence but is never independent evidence; never
  silence stderr in evidence-bearing commands.
- Name these pathologies when they occur (gate self-weakening, proof-class
  inflation, golden regeneration, tolerance widening, suppression-pragma
  laundering, refusal farming, follow-up laundering); the names are the
  deterrent. The full catalog with countermeasures lives in the
  just-say-no-to-process-porn-and-ceremony skill; ask the operator for it
  if you cannot resolve that reference.

---

## Comments (lean by default; `bun tools/comments.ts` enforces the mechanical part)

Default is **no comment**: names and structure say what code does. Write a comment only when it
carries information the code cannot: **why** (a non-obvious constraint, a Bend quirk — cite the
fact ID from PLAN.md, e.g. `F26`), or public API documentation.

Formats:
- **Bend (`packages/`)**: exactly one doc line `# <Sentence ending with a period.>` directly above
  every public `law` and every predicate `def`. Optional module header of at most 3 `#` lines at the
  top. Inside proofs, only single-line `#` notes explaining a non-obvious step.
- **TypeScript (`tools/`)**: one header block per file (purpose, usage, exit codes; ≤ 12 lines).
  Elsewhere short `//` why-comments (at most 2 lines), or one-line `/** … */` on exported API functions.

Forbidden (lint fails): commented-out code; `TODO`/`FIXME`/`XXX`/`HACK` (open an issue instead);
comment blocks over the limits above; files whose comment lines exceed 25% of non-blank lines.
Not linted but rejected in review: comments that restate the code, history/changelog comments,
authorship or "generated by" banners (except the twins tool's generated-section marker).
