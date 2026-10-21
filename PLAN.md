# bendlib — plan

> **Date:** 2026-09-24 · **Owner:** Muhammed Durakovic · **Compiler:** `bend 2.0.38` since 2026-10-21
> (linux-x64 archive sha256 `02089dc0eed0fd5fd6d73c74cc9cffcb2c6638dd3b02ae83f7b8cc57fbe381ba`; 2.0.35 before)
> **Brand:** GitHub org `bendlib` · hub package `bend-mathlib` (D1: decided) · Apache-2.0
>
> Scope rule: this document holds architecture, design and build order. Process, publicity cadence
> and governance paperwork are deliberately left out; they come with time.

## 0. What we are building (three products, one foundation)

| Product | What | Why it matters |
|---|---|---|
| **`bend-mathlib`** (Bend, hub package) | Machine-checked lemmas, predicates and abstract (algebra/order) theorems over Base | Every proof bottoms out in basic facts Base doesn't ship; Bend's own repo re-proves `add_succ` in 23 files; the creator said "We need a mathlib!" |
| **`lawcheck`** (TypeScript/Bun CLI) | Finds counterexamples to laws before anyone tries to prove them, shrinks them, and measures law strength by mutating the implementation | Loose/wrong laws are Bend's main criticism (the "can't win" law satisfied by breaking movement; issue #880); a false law wastes an AI's proof budget |
| **Bend docs** (static site + generator) | docs.rs for BendHub: rendered API docs of every hub package, checked status on the current compiler, reverse deps, lemma search by statement shape | The hub shows hashes and file lists only; people and agents can't browse APIs or find lemmas |

They share one keystone: **`@bendlib/reader`**, a TypeScript library that loads Bend source with the
*official* parser/elaborator (`bend2/bend.ts`) matching the user's installed compiler version. lawcheck
and the docs generator both sit on it; mathlib is the first customer of both (lawcheck screens lemma
candidates; docs render the lemma index).

**Backlog (not now):** `bendlib-par` (parallel Array algorithms with laws, CPU/GPU), proved data
structures (`bendlib-heap`, `bendlib-rbmap` over frozen kernels, §3.4), lawful codecs.
**Not doing:** bend-ci/GitHub Action products, LSP, playground, compiler forks, F32 numerics.

---

## 1. Grounded facts (verified on 2.0.27, experiments in `research/experiments/`)

Re-run on 2.0.38 (2026-10-21, `research/experiments/run.sh`): 56 passed, 0 failed, after the shared helper `review2/t4core.bend` was re-proved for Base's new `List.all` (F39); no replayed outcome changed.

Re-run on 2.0.37 (2026-10-13, `research/experiments/run.sh`): 56 passed, 0 failed; no replayed outcome changed. F37 is new since 2.0.35.

Re-run on 2.0.34 (2026-09-29, `research/experiments/run.sh`): 56 passed, 0 failed; no replayed outcome changed. F35 was checked separately with `--verdict` on bool and algebra.

Re-run on 2.0.32 (2026-09-28, `research/experiments/run.sh`): F1, F3, F4, F8, F18, F24 and F33 changed as
noted in their rows; every other replayed outcome is unchanged. The F31/F34 files sit under
`research/candidates/mathlib-0.2/`, whose `.` is not a plain name (F3), so run.sh's lawcheck lines for them
fail until lawcheck checks such files through a scratch copy (bead `bend-85q`); run on a plain-path copy of
those files, their outcomes are unchanged.

| ID | Fact | How verified | Consequence |
|---|---|---|---|
| F1 | Hub names match `^[a-z][a-z0-9-]{11,63}$`; versions are `a.b.c.d`, strictly increasing; names are permanent and owned by the publisher's GitHub login. **2.0.28:** names match `^[a-z][a-z0-9-]{0,63}$`; one under 12 characters is won at auction on the hub | `bend.ts NAMED`, CLI, hub `names.json`, 2.0.28 release notes | `mathlib`/`bendlib` are now valid names but auctioned; only the owner publishes named versions; our tools accept 1–64 characters |
| F2 | Publish bundles local imports, never hub (`0x…`) imports | source: `main.ts pkg_files` | Packages can depend on packages by name/hash without vendoring |
| F3 | Namespace = file path; hub package namespace = `0x<hash>/<path>`; two versions of a package = unrelated namespaces. **2.0.28:** a local namespace is the file's real path relative to the root file's directory (so it can start with `../`), and an import path must be plain names (`/`, `../`, then components `[A-Za-z_][A-Za-z0-9_-]*`); a relative import cannot reach into `BEND_LIB`, only `0x<hash>/` and `name@version/` go to the hub. **2.0.32:** one file is one module however an import spells its path | source `book_load`; `v1/ v2/` experiment | Version skew between dependents is the core interop risk; tools must run on files under plain-named paths (lawcheck imports the user's file by path) |
| F4 | A def unifies across package versions **iff its body is a plain application of Base functions** (`le` via `Nat.is_le`, `mem` via `List.contains`, `sorted` via `List.all/zip/tail`). Any def that `match`es — recursive or not — and any datatype is **nominal** at variable arguments (`expected rv1/pred.isz(n) / observed rv2/pred.isz(n)`; 2.0.32 prints the importer's alias, `observed P2.allz(xs)`); closed instances still normalize and unify (why the first experiment, `le(5n,5n)`, misled) | `review2/t4a,t4b,t4d,t4e,t4f,t4g,t13a,t13b`; `user_adt.bend` | **Encoding rule** (§3.1): mathlib predicates are Base-only; everything nominal (`count`, `perm`, datatypes) lives in a **kernel** package frozen at one hash that every mathlib version imports |
| F4b | Two lemma packages importing **one shared predicate file** interoperate at variables | `review2/t11_user_kernel.bend` | Kernels work |
| F5 | A def/law/constructor spelled like a Base one is a hard error (`duplicate declaration`) | `lib/clash.bend`, `ctor.bend` | Names must be disjoint from Base's scheme |
| F6 | Base 2.0.27 names every function `Type.verb` and every bare name/constructor is Capitalized | grep `base.bend` | Our exports are lowercase + dot-free: disjoint from Base's *current* convention (nightly check guards the future) |
| F7 | Constructors of user modules are per-file namespaced (`A.node`, `B.node` coexist) | `both.bend` | Only Base collisions matter |
| F8 | Imported modules are fully re-checked on every check (2.0.32 locates the failure by the def's own name, `Location: s5`, not `bad10.s5`) | `usebad.bend` | Dependencies can't smuggle false lemmas; every dependent pays our check time |
| F9 | 1,600 repeated *simple* lemmas import in 0.45 s / 160 MB (not representative of heavy proofs) | `big*.bend` (generator inline in plan history) | Size isn't the constraint; proof shape is |
| F10 | A LAWS/PROOF split forces importers to import both files | `use_laws_only.bend` ✗, `use_both.bend` ✓ | Library modules state and prove inline |
| F11 | Lemmas generic over `a: Quant, -A: Kind(a)` check and instantiate at `&1` and `&2` | `glist.bend` | All List lemmas generic |
| F12 | Templates (`~A`, `~le`) check with no unsafe warning; Base `List.sort` uses them | `tmpl2.bend` | Comparators/operations are templates, never closures |
| F13 | Laws can take `for ~op`/`for ~assoc` hypotheses usable many times; abstract theorems instantiate across files | `lib/algebra.bend`, `use_alg.bend` | Algebraic layer feasible now |
| F14 | Reusing function-typed hypotheses in *live* code is unsupported; planned for Bend 2.1 (issue #848) | issue thread | Keep abstract theorems in `~` form; expect 2.1 idiom changes |
| F15 | `import 0x<hash>/f.bend` works (package cached under `~/.bend/lib/`; cache hits are not re-hashed; the whole package manifest is fetched even if one file is imported) | `hubuse.bend` (run on a warm cache) + source | Split packages when unrelated parts would bloat fetches/hashes |
| F16 | Alias `Nat` for our module works; Base spellings win | `alias_nat.bend` | Recommend `MNat`/`MList` aliases |
| F17 | `bend f.bend --check-only` checks without running | CLI | CI command |
| F18 | Unsafe/foreign reliance is reported by name (`All terms check, but N defs rely on…`, exit 0). **2.0.32:** a clean check prints exactly `ALL PROOFS CHECK` and `Use --verdict for mathematical validity.` (exit 0); reliance prints `SOME PROOFS FAIL` and `Error: N defs rely on unsafe or foreign code:` with the defs and exits 1; every other failure (TODOs, type errors) is `SOME PROOFS FAIL` plus the error, exit 1. `--verdict` also rechecks every def with the BendTT kernel, which needs Lean v4.34.0 | `main.ts cli_verdict` (2.0.32); `--help` | mathlib gate: `--check-only` output exactly those two lines; `--verdict` would need Lean in CI |
| F19 | Publish refuses open laws and reached holes | guide, `cli_publish` | Hub content is fully proved |
| F20 | Installer verifies sha256, installs to `~/.bend`; `bend version`; `BEND_NO_TELEMETRY=1` | `install.sh` | CI pins version + sha256 |
| F21 | A local `BEND_LIB` with `names/<name>@<ver>` → `0x<32 hex>` and `0x<hash>` → symlink to a working copy resolves `import <name>@<ver>/f.bend` locally and live | `devmode/` | Dev imports use the final import lines verbatim (§3.5) |
| F22 | A closed law instance proved by `{==}` passes iff both sides normalize equal; a false one fails with `expected/observed` and `Location: <law>` — 48 instances checked in 0.15 s | `lc` experiment (see §4.3) | lawcheck's universal evaluation engine = the checker itself |
| F23 | `bend2/bend.ts` imports under Bun and exposes `book_nil`, `book_load`, `term_show`, the `Book` (`tlds`, `ctrs`, spans); it loads hub packages and lists typed declarations | `docs_probe.ts` | Tools reuse the official parser instead of writing one |
| F24 | The installed binary ships only `base.bend` + effects, not `bend.ts` (2.0.30+ also ships the kernel source `bendtt.lean`); GitHub releases exist per version (v2.0.8+) | `~/.bend/bend2/`, releases | reader fetches `bend.ts` for the user's exact version (§2) |
| F25 | A `-> Type` predicate cannot be a `+` (reusable) hypothesis (`expected Data, observed Type`); the same body declared `-> Data` can; a plain equality hypothesis cannot be used twice | `review2/t2c` ✗, `t2d` ✓, `t2f` ✗, `t8` ✓ | Predicates return `Data`; `A & B` / `Or` sugar is `Sigma/Either<&1,&1,…>` = `Type` — Data predicates spell `Sigma<&2,&2,…>` / `Either<&2,&2,…>` |
| F26 | A statement-only binder must be erased (`for -y`) or a runtime caller loses its affine variable (`y consumed more than once`); a binder the proof matches on cannot be erased | `review2/t1a` ✓, `t1b` ✗, `t1c` ✗ | Erasure is a lint-enforced invariant, not a style choice |
| F27 | A count-based `perm` hypothesis (a function type) is single-use, even when erased | `review2/t5a` ✓, `t5b` ✗, `t5c` ✗ | `perm` design must weigh an inductive `Perm is Data` (reusable) — decided in the kernel design note |
| F28 | `map_map` with a composed closed template `~(x => g(f(x)))` checks; `Equal.sym(T, l, r, e)` twins check at generic quantity, and the reversed (`{r == l}`) form is the one that **simplifies** under `%` | `review2/t3_map_map`, `t6_twins` | Twins are the common rewrite direction (§3.1.6) |
| F29 | Bare `(a <= b)` without `: Nat` is a hard error since 2.0.16; `bend link <name>@<ver> 0x<hash>` names an already-published hash; `BEND_HUB` env overrides the hub URL; `names/` cache entries are never re-validated | `review2/t2a`; CLI help; binary strings | Docs show `(a <= b : Nat)`; release = anonymous publish → verify → `bend link`; dev caches start empty |
| F30 | `bun build --compile tools/lawcheck/cli.ts` gives a standalone binary that runs lawcheck, also from an empty `BENDLIB_CACHE` (it fetches and imports `bend.ts` at run time) | 2026-09-24, linux-x64, `correct.bend`/`buggy.bend` fixtures | lawcheck binary release is packaging work only |
| F31 | lawcheck's random `Nat` values (up to 30) make `Nat.pow` laws overflow the checker ("the machine stack overflowed"); the whole law then reports `!` instead of dropping that one instance | `research/candidates/mathlib-0.2/nat.bend`, laws `pow_succ`, `pow_add` | Overflowing instances are dropped per item (`toolarge`) and `--max-nat` bounds random Nats (bead `bend-23x.1`). |
| F32 | Every bend-mathlib 0.1 law is lawcheck-clean: 107 ✓, 12 skipped (template or function binders), 0 ✗; ≈25 s for the five modules here (nat.bend alone ≈9 s) | `bun tools/lawcheck/cli.ts packages/bend-mathlib/<m>.bend` | lawcheck can gate mathlib CI |
| F33 | Open bend issue #1001: one `@unsafe` law fill in an imported file makes `bend PROOF.bend` print a clean `All terms check.`. **Fixed in 2.0.28:** the verdict walks from every def, so the reliance fails the check (F18); seen on 2.0.32 with a file that imports an `@unsafe` law fill | github.com/bendlang/bend/issues/1001; 2.0.28 release notes | The docs' source cross-check for `@unsafe` is now redundant on the pinned compiler; mathlib's `check.ts` still scans source |
| F34 | 80 candidate 0.2 statements (Nat `sub`/`min`/`max`/`pow`/reflection/order, List `take`/`drop`/`length`, Bool) type-check and have no counterexample (78 ✓, 2 `!` from F31, 1 skipped); 7 template statements type-check (lawcheck skips them) | `research/candidates/mathlib-0.2/*.bend` | 0.2 lemma beads copy statements verbatim from there; the candidate files report 87 laws, 0 ✗, 0 `!` (1 ~). |
| F35 | `bend <m>.bend --verdict` (2.0.32) builds `$HOME/.bend/bendtt/7f6ef51c9f75d7de/bendtt.lean` with Lean v4.34.0 (≈29 s first run, then 0.2–1.0 s/module; 5.8 s for all 12). Clean prints exactly `ALL PROOFS CHECK` (exit 0); `?goal`/`?TODO` print `SOME PROOFS FAIL` + the goal/TODO (exit 1); `@unsafe` prints `Error: N defs rely on unsafe or foreign code:` (exit 1). But `algebra`, `order`, `sort` and `all` print `Sorry - this is a mismatch between the TypeScript implementation, and the formalized BendTT kernel.` (exit 1) when a proof calls a higher-order `~` parameter returning `{le(x, y) == True{} : Bool}` (reproducer `v_n`; declaring it unused, or returning a reflexive equality, passes); these are exactly the laws lawcheck already `--allow-skip`s (`foldl_op_eq_foldr_op`, `le_trans3`, `le_trans4`, `le_total_*`, `le_antisymm_eq`). Without Lean: `the kernel did not build (lean: Executable not found in $PATH)`. **2.0.34:** `bool.bend --verdict` prints `ALL PROOFS CHECK` (exit 0); `algebra.bend --verdict` still prints the TypeScript/BendTT mismatch (exit 1). The 2.0.34 release notes say conversion shares equal cells, but BendTT does not: its `--verdict` runs out of fuel on the depth-32 shared Merkle proof. This performance claim is from release notes, not a local reproduction. | `~/.bend/bin/bend <m> --verdict` on 2.0.32 with Lean v4.34.0; 2.0.34 `bool.bend` and `algebra.bend --verdict`; v2.0.34 release notes (#1071, #1151) | From 2.0.38 (F38) CI and `release.ts` require a clean `--verdict` on every bend-mathlib module |
| F36 | bend 2.0.33 removed Base's `.fin` helpers (`Nat.div.fin`, `Nat.mod.fin`, `String.eq.fin`); `Nat.div`/`Nat.mod`/`String.eq` now project with `Pair.fst`/`Pair.snd`. On 2.0.34 the published bend-mathlib 0.4.0.0 `nat.bend` and `string.bend` fail (`expected : a defined name / observed : Nat.div.fin`), while 0.3.0.0 and bendlib-kernel-list 1.0.0.0 still check | empty private `BEND_LIB`, `import bend-mathlib@0.4.0.0/nat.bend` (and by hash) on 2.0.34; nightly issue #24 | A proof that names a Base helper breaks when Base drops it: proofs name only Base defs a statement needs, and a Base removal is repaired by a new release (§8) |
| F37 | bend 2.0.35 keys a file's own names `ns:name` inside bend.ts (`parse_qual`; 2.0.34 used `ns.name`), and still prints them `ns.name` (`name_key`), so a name in printed text and the same name as a book key differ after the namespace | bend 2.0.35 `bend2/bend.ts` `parse_qual`/`name_key` (upstream #1156); reader goldens `hub_list.json` diff `0x…/list.append_nil2` → `0x…/list:append_nil2` | `@bendlib/reader` keeps `Decl.name` the book key and exports `inNamespace`/`localName`/`printedName`; lawcheck keys types, ctors, predicates and term decls by `printedName` because it matches them against printed text |
| F38 | `bend --verdict` (2.0.36, 2.0.37) fails a file when any def of a module it imports is out of BendTT's scope, even one it never uses (a file importing bend-mathlib 0.7.2.0 `sort.bend` and proving `{Nat.add(2n, 0n) == 2n : Nat}` fails; importing `list.bend` passes). A template lambda that captures a run-time value inside a type (`List.all(~&2, ~A, ~(y => le(lo, y)), xs)`) is out of scope ("a template argument that depends on a run-time value", upstream #1483), while a recursive Bool def over the same list is not. With that restated, every def `sort.bend` leaves out is "no model" for an abstract `~le_trans`/`~le_total` (upstream #1182); the Nat instances (`sort_by_sorted_nat` etc.) translate, and the #1263 branch checks every bend-mathlib module | issue #25; `bend sort.bend -o x.bendtt` before/after on 2.0.36; #1263 branch fb1577ed `--verdict` | bend-mathlib states predicates under `~` binders as recursions; CI allows blocked modules only "no model" reasons and kernel-checks the rest of them. Bend main after #1580 takes a `~` constant's model from a concrete call of its law: with a Nat call of each such law (twins.ts emits the `_sym` twins' calls) and sort's unused `internal_evens_sorted`/`internal_odds_sorted` removed, every module prints ALL PROOFS CHECK under `--verdict` at e5527d5 (2026-10-18). Resolved by 2.0.38: every module passes `--verdict` and CI checks them all with it |
| F39 | Base after 2.0.37 (upstream #1548, #1459) defines `List.all`/`any`/`find`/`contains` through a `.go` loop that matches the list before its flag, and `String.order` directly instead of through `String.cmp`, so `List.all(h <> t)` no longer unfolds to `Bool.and(f(h), List.all(t))`. A short-circuit over an erased tail (`List.all.go(t, False{})`) never reduces and an erased binder can't be matched, so 7 frozen list lemmas (`all_append`, `any_append`, `contains_append`, `mem_cons_self`, `mem_cons_of_mem`, `sorted_cons_cons_elim_le`, `sorted_cons_cons_elim_tail`) have no proof there (upstream #1616). Upstream reverted #1548 for that report (#1629, e5527d5), so on main only `String.order` differs and every module checks with String.order bridge proofs (now in `string.bend`). Bend 2.0.38 (2026-10-20) ships that String.order and a third shape: `List.all`/`any`/`find`/`contains` short-circuit through a thunk (`List.all.if(u => List.all(t), f(h))`, likewise `List.any.if`, `List.find.if`; `List.find.put` is gone), so `internal_find_put` is mathlib's own and the cons bridges are proved by cases on the head's test | bend main 234cb9b `--check-only` of bend-mathlib 0.7.3.0 with each failing def stubbed in turn: 21 list.bend defs, 3 string.bend, 3 sort.bend | proofs unfold those functions only in `internal_` lemmas (the cons bridges, plus the all/any map and reverse helpers), whose proofs are per-Base; the rest of the package goes through them |

---

## 2. Keystone: `@bendlib/reader` (TypeScript, Bun; built in `tools/reader`)

**Job:** give any tool a faithful, version-matched view of Bend source.

- **Version matching.** Run `bend version` → `2.0.x`. Fetch the `v2.0.x` release source tarball from
  GitHub once, verify it against the release (sha256 of the archive), cache under
  `~/.cache/bendlib/bend/<version>/`, and `import()` its `bend2/bend.ts` dynamically (F23, F24).
  Why: `bend.ts` changes several times a day; parsing with a mismatched version silently misreads
  code. A tool that parses exactly like the user's compiler cannot drift.
  Fallback: `--bend-src <dir>` to point at a local checkout (for compiler developers / offline).
- **API (small, stable):** `load`, `decls`, `show`, `blankImports` (`tools/reader/index.ts`).
  - `load(file, {bendLib?}) → Loaded` (runs `book_load` with an isolated `seen` map; honours `BEND_LIB`).
  - `decls(loaded, {scope?}) → Decl[]`, `scope: "own" | "all-non-base" | "all"`; `Decl` = `{name, namespace, kind: type|ctor|def|law|template|effect|unsafe, origin, file, line, column, doc, signature, statement?, binders?, proved?, …}`.
    `doc` = contiguous `#` comment lines directly above the declaration.
  - `show(bend, term, binders?) → string` — bend.ts's own `term_show`, so output matches the checker.
  - `blankImports(text) → string` — blanks import lines (same offsets) so a file parses standalone.
- **Isolation:** never touch the user's `~/.bend/lib` unless asked; tools pass a private `BEND_LIB`.
- **Tests:** golden decl dumps for 4 cases (`tools/reader/test/golden/`), one against a real hub
  package; re-run on each new compiler release (the tool's own compatibility check).

Risk: `bend.ts` is internal; exports can change. Mitigation: all access goes through this one
package; a version bump that breaks it breaks one adapter, not every tool.

---

## 3. `bend-mathlib` — architecture

### 3.1 Layering and the rules that make it a safe dependency

```
 domain packages / user projects
        │ import by name@version
 bendlib-* structures (bendlib-heap, bendlib-rbmap, …) ──┐
        │                                                 │ import by exact hash
 bend-mathlib  (lemmas + Base-only predicates + abstract  ├──► bendlib-kernel-* (frozen once at 1.0.0.0:
   theorems; released freely)  ───────────────────────────┘     count, perm/Perm, datatypes + invariants)
        │
 Base
```

1. **Encoding rule** (F4, F4b). Every definition in mathlib is one of:
   (a) a **lemma** (law + proof) — never needs to unify across versions;
   (b) a **Base-only predicate** — body is a single application of Base functions, returning `Data`:
   `def le(a: Nat, b: Nat) -> Data: {Nat.is_le(a, b) == True{} : Bool}`,
   `mem` via `List.contains(~A, ~eq, xs, x)`, `sorted_by` via
   `List.all(… List.zip(xs, List.tail(xs)))` (`review2/t13a`, `sv1/s.bend`) — version-stable;
   (c) an **import from a kernel** for anything that must `match` or be a `type`.
   `tools/mathlib/lint.ts` rejects a mathlib predicate that matches or calls a non-Base def.
   Trade-off, stated: Base-only encodings follow Base churn (if HOC changes `List.contains`, published
   statements change meaning/break); kernel definitions are immune to Base churn but nominal.
1b. **Kernels** (`bendlib-kernel-list`, later `bendlib-kernel-rbtree`, …): a tiny package holding the
   definitions whose identity matters — `count`, `perm`/`Perm`, datatypes and their invariants —
   published **once** at `1.0.0.0`, LICENSE right the first time (it's part of the hash), never
   republished; a new definition means a new kernel package. Every mathlib/structure version imports
   the kernel **by exact hash** (`import 0x…/list.bend as KList`, name in a comment), so dependents on
   different versions still interoperate (F4b). Kernel 1.0.0.0 is published before the mathlib
   release that first uses it.
1c. **Kinds.** Predicates return `Data` (F25) so hypotheses can be `+h`; never use `A & B`/`Or`
   sugar inside them (that forces `Type`); spell `Sigma<&2, &2, A, _ => B>` / `Either<&2, &2, A, B>`.
   `le_total : Or(le(a,b), le(b,a))` exists for convenience plus `le_total_d : Either<&2, &2, …>`
   as the reusable form.
2. **Append-only public API.** Once published, a module path, public name, law statement or
   predicate body never changes or disappears under this package name — no version number
   authorizes it (a changed statement is a different proposition regardless of version). Fixes get
   a new descriptive name (`perm_by_count`, not `perm2`); the old one stays, documented as
   superseded; a bridge theorem is added when provable.
   Enforced by **`PUBLIC_API.lock`** (per package: module paths, public names, normalized statement /
   predicate-body text + sha256). CI fails on any change or removal; additions are fine.
   *Consumer:* CI publish gate. *Defect class:* a changed published statement breaks every dependent
   permanently (hub content is immutable, F1/F3). *Retire:* never while the package exists.
3. **Public vs internal.** Bend has no visibility; every def is importable. Proof helpers are named
   `internal_*` and excluded from the lock and docs.
4. **Naming.** lowercase `snake_case`, no dots (F5/F6). Mathlib-standard names so humans and models
   can guess them: `add_zero` (x+0=x) and `zero_add` (0+x=x) both exist even if one is definitional;
   `add_comm`, `add_assoc`, `mul_add`, `append_nil`, `append_assoc`, `length_append`,
   `reverse_reverse`, `le_refl`, `le_trans`, `lt_irrefl`. Modules are namespaces named after Base
   types (`MNat.add_comm`, `MList.append_assoc`, `MString.append_assoc`); names are unique per
   module. Comparator-dependent predicates say so: `sorted_by`. Ship `ge`/`gt` next to
   `le`/`lt` with flip lemmas (Base's own lemmas use `Nat.is_ge`; `is_ge(a,b)` and `is_le(b,a)` are
   not definitionally equal).
5. **Genericity and erasure.** Generic in `a: Quant, -A: Kind(a)` wherever the proof allows (F11);
   a `+xs` at generic quantity is illegal (only `&2` is `Data`), so a `&2`-specialized variant is
   allowed with a `_data` suffix and a stated reason. **Every binder the proof does not `match` on is
   erased** (`for -y`); a matched binder cannot be (F26) — `tools/mathlib/lint.ts` compares binders with the
   proof's scrutinees. Operations/comparators are templates (`~op`, `~le`) with template hypotheses
   (`for ~le_trans: …`) (F12, F13); template arguments must be closed, so the library ships instances
   for `Nat`, `Bool` and `List<&2, Nat>`. `List.map` is a template over affine lists only
   (`List.map(~A: Type, ~B: Type, ~f, xs: List<A>)`), so map lemmas are `&1`-only; `map_map` works
   with a composed closed template (F28).
6. **Orientation and `_sym` twins.** `%e : P` replaces the equation's right side with its left side,
   so the Mathlib-style statement (big side left) *expands*, and its reversed form *simplifies* — the
   direction most rewrite steps want (F28). Therefore every public equational lemma `name` gets a
   generated twin `name_sym : {r == l}` (proof `Equal.sym(T, l, r, name(..))`), in a generated
   trailing section of the **same module** (`# --- generated: _sym twins, do not edit ---`),
   regenerated and diffed in CI. Docs state the rule in one line: "`name` expands, `name_sym`
   simplifies". Claims are one line each (lint) so `tools/twins` is a small text splitter.
7. **Module layout.** Few, guessable modules named after Base types (`equal`, `bool`, `nat` incl.
   order, `list` incl. mem/count, `maybe`, `string`, `order`, `algebra`) + `all.bend` (imports every
   module; the publish root). Users import single modules (`…@v/list.bend`); modules import each
   other directly.

### 3.2 Contents

Base facts that shape proofs (verified): `Nat.add`, `Nat.mul(a, +b)` recurse on the first argument;
`Nat.sub` matches both; `Nat.pow(+a, b)` recurses on `b`; `List.reverse` = `List.reverse.go(xs, Nil{})`
(accumulator); `List.take/drop` match the list first; `List.foldr/foldl` are quantity-generic templates;
`Maybe.map/bind` take closures; `Equal.sym(-A, -a, -b, e)`, `Equal.cong(-A, -B, -f, -a, -b, e)`.

**0.1.0.0 — 25–40 high-confidence lemmas, no custom `perm`/`sorted` yet:**
- `equal.bend`: `cong2`, `subst`, `trans3`, `cong_succ`.
- `bool.bend`: `not_not`, `and_comm`, `or_comm`, `and_assoc`, `or_assoc`, `and_true`, `true_and`,
  `and_false`, `or_false`, `de_morgan_and`, `de_morgan_or`, `true_ne_false`.
- `nat.bend`: `add_zero`, `zero_add`, `add_succ`, `succ_add`, `add_comm`, `add_assoc`, `add_left_comm`,
  `add_right_comm`, `add_add_add_comm` (four-way; re-proved 12× upstream), `add_left_cancel`, `succ_inj`,
  `zero_ne_succ`, `mul_zero`, `zero_mul`, `mul_one`, `mul_succ`, `mul_comm`, `mul_assoc`, `mul_add`, `add_mul`;
  order (same module): `le`, `lt`, `ge`, `gt` (Base-only `Data` predicates), `le_refl`, `le_trans`,
  `le_antisymm`, `le_total` + `le_total_d`, `le_succ`, `le_add_right`, `lt_irrefl`, `lt_trans`,
  `le_of_lt`, `zero_le`, `le_of_ge`/`ge_of_le` flips.
- `list.bend`: `append_nil`, `append_assoc`, `length_append`, `reverse_go_spec`, `reverse_append`,
  `reverse_reverse`, `length_reverse`, `foldr_append`, `take_append_drop`, `length_map`, `map_append`.

**0.2 / 0.3:** `maybe.bend` (monad laws — after an experiment fixes the closure quantification),
`list.bend` additions: `mem` (Base-only via `List.contains`) and `sorted_by` (Base-only via
`List.all/zip/tail`) with their lemmas; `count`/`perm` from `bendlib-kernel-list` with lemmas
(`perm_refl/sym/trans`, `perm_cons`, `perm_append_comm`, `perm_length`, `sorted_by` inversion);
`order.bend` and `algebra.bend` (abstract theorems over `~le` / `~op` with instances `Nat.add`,
`Nat.mul`, `Bool.and`, `Bool.or`, `List.append`); `string.bend` (`SCon`/`SNil` versions of the list
facts); `map_map`.
**Stretch (0.4+, never on the critical path):** `base_sort.bend` — Base `List.sort` returns a
`sorted_by` permutation. `List.sort` is fuel-driven (`List.sort.go(fuel = n)`,
`List.merge.go(fuel, (acc, xs, ys))` with fallback branches that are not sorted), and merge steps match
on computed Bools, so it needs `bool_cases` detours and fuel-sufficiency lemmas: budget ~2 weeks.
The launch-era headline is instead a structural merge sort proved sorted + permutation.

### 3.3 Frozen definitions: how we pick them
Base-only predicates (rule 1b) and kernel definitions (rule 1b) are permanent. Before one is
published: write the candidates in `research/candidates/predicates/`, prove the intended headline theorems with
each, add negative fixtures (e.g. with an equality template that always answers `False`, `perm` must
not make `[x]` a permutation of `[]` — semantic theorems carry equality soundness/completeness
hypotheses), then the owner picks. For `perm` specifically (F27): count-based
`@x -> {count(x,xs) == count(x,ys)}` gives one-line refl/sym/trans but is a single-use closure;
an inductive `type Perm … is Data` gives reusable hypotheses and free `trans/cons/swap` at the cost of
derivation induction for `perm_count`/`perm_length`. Write `perm_merge` both ways, then choose —
possibly ship both in the kernel with a `perm_iff_Perm` bridge in mathlib. Count-based needs `A: Data`.

### 3.4 Structure packages over kernels (backlog; recorded now because it constrains mathlib)
Datatypes for structures live in kernels (rule 1b), byte-sealed: `LICENSE` + declarations + the
invariant predicates, nothing that might need editing (any change alters the hash, i.e. the type
identity, F3). Consumers import kernels by hash. Each structure ships as its own package
(`bendlib-heap`, `bendlib-rbmap`, …) so adding one never rehashes the others (F3, F15). Key/value
quantities are independent: `rbtree<ak, av, -K: Kind(ak), -V: Kind(av)> is Kind(ak <&> av)`.

### 3.5 Dev-mode imports (F21) and release
- Sources always contain final import lines (`import bend-mathlib@0.3.0.0/list.bend as MList`).
- The dev-mode helper `tools/mathlib/devlib.ts` rebuilds repo-local `.devlib/` (git-ignored) from empty
  on every run (`names/` entries are never re-validated, F29): `0x<hash>` → symlink to the working
  package, where `<hash>` is its real publish hash. A source can then `import 0x…/file.bend` from a
  local package before it is published; `--check` fails when such a pin names a local package whose
  content has since changed.
- CI: fails on any `../` import leaving a package (it would bundle the other package, F2, and reaching
  one file under two namespaces is a hard `one namespace per file` error).
- Release (a `release` bead or the owner; names are tied to the owner's login, F1, §9 D-release):
  1. `bun tools/mathlib/release.ts <pkgdir> <name> <version>`: fresh isolated `BEND_LIB`, every imported `name@version` resolves
     on the hub, computes the real publish hash locally (`cli_publish` algorithm: sorted paths,
     `"0x" + sha256(Σ sha256(content) + " " + path + "\n")[0:32]`), prints the commands.
  2. `release.ts --publish` runs `bend packages/<pkg>/all.bend --publish` (anonymous; prints `0x…`, must equal step 1).
  3. Tool re-checks `import 0x…/all.bend` from an empty `BEND_LIB` (real hub fetch + hash verify).
  4. `bend link <pkg>@<ver> 0x…` — the name is attached only to verified content.
  5. Tool appends `{name, version, hash, compiler}` to `RELEASES.md`; README shows the named import and
     the hash import (content survives even if a name is lost); git tag.
- Versioning: dependents pin exact versions; nothing resolves ranges, so a fix release repairs nobody
  automatically — a version matrix mapping mathlib versions to Bend versions is planned but not built.

### 3.6 mathlib CI (the only gates)
1. Pinned compiler from `toolchain.json` (download release archive, verify sha256).
2. Every module: `bend <m> --check-only` prints exactly `ALL PROOFS CHECK` and `Use --verdict for mathematical validity.` (F18); no `@unsafe`, no `def f?(`,
   no holes (lexer-aware scan); wall-time ceiling per module (generous, e.g. 10 s).
3. Naming lint (§3.1.4) incl. collision check against `bend base` of the pinned compiler.
4. `PUBLIC_API.lock` append-only check.
5. Nightly: same on the latest Bend release; on failure open an issue. (Our own early warning — not a
   product.)

---

## 4. `lawcheck` — architecture

### 4.1 User experience
```
$ lawcheck LAWS.bend
✗ ins_sorted   counterexample (shrunk):  x = 0n, xs = [1n]
               lhs  B.ins(0n, [1n]) = [1n, 0n]
               rhs  [0n, 1n]
✓ ins_length   212 instances, 0 failures (sizes ≤ 4)
~ merge_perm   premise satisfied in 0/212 instances — law untested (vacuous in this space)
$ lawcheck mutate LAWS.bend --impl main.bend
ins: 9/12 mutants killed · survivors: [swap arms of `match xs`] [replace `x` with `h` in line 12] …
     → your laws do not pin `ins` (a body ignoring `x` still satisfies them)
```
`--json` for agents; exit 0 all pass / 1 counterexample or weak laws / 2 usage.

### 4.2 Pipeline
1. **Load** the file with `@bendlib/reader`; collect `law` declarations (open or proved) via `decls`
   (each carries its binders, `where` premises and claim).
2. **Instantiate types.** Type parameters: `-A: Kind(a)` → default `U32` then `Nat`; `a: Quant` → `&2`
   (and `&1` when the claim allows). Template hypotheses (`for ~f`, `for ~le_trans`) → v1 skips the law
   with a clear message; v2 draws from a small catalog of closed functions per type.
3. **Generate values** per binder type:
   - Exhaustive small-scope first (SmallCheck style: all values up to depth/size *n*), then seeded
     random for larger sizes.
   - Built-ins: `Nat` (0..k, never above ~256 as literal — the checker expands big Nat literals),
     `Bool`, `U32` (0, 1, max, powers of two, random), `Char`, `String`, `List<a, A>`, `Maybe`, pairs,
     `Cmp`, `Result`.
   - User datatypes: enumerate constructors from the elaborated `Book` (`book.tlds[ADT].c`), recursive
     fields bounded by depth.
4. **Evaluate (engine C — the checker, F22).** For each instance σ emit
   `law lc_<i>: {lhs[σ] == rhs[σ] : T}` + `def lc_<i>(): {==}` into batch files that import the user
   module; run `bend <batch> --check-only` in parallel workers (one process per batch, N = cores).
   The checker stops at the first failure: parse `Location: lc_<i>` and the `expected/observed` pair,
   drop that instance, re-run the rest of the batch (or bisect). Semantics are *exactly* the
   checker's definitional equality — the same judge the proof will face — and it works for every type.
   - Predicate claims (`le(a, b)`, any `Type`-valued claim): emit the instance as the claim type and
     try `{==}` — a decidable predicate built on Base `Bool`s normalizes; if the goal doesn't reduce to
     a closed equality, report "not decidable by evaluation" for that law.
   - Premises (`for y: B where P(y)`, implications): evaluate the premise instance first; skip σ when
     it fails; report the satisfied fraction (vacuity warning at 0%).
5. **Shrink** each failing σ: standard shrinkers (Nat toward 0, lists by removing/shrinking elements,
   ADTs to subterms), re-evaluate, keep the smallest failing instance.
6. **Engine N (native, v2):** for laws whose type has a Base equality (`Nat.is_eq`, `U32.is_eq`, lists of
   those), compile one harness `main` with all instances (`bend h.bend -o h`), run natively for large
   random sizes. Bonus: compare engine N vs engine C results — a disagreement is a compiler/runtime bug
   (valuable to upstream).

### 4.3 Mutation mode (law strength)
- Mutants of the implementation defs via source splicing (span splicing in `tools/lawcheck/src/mutate.ts`): swap match arms,
  replace a case body with another case's body, swap same-typed arguments, `0n↔1n`, drop a cons,
  replace a subterm with a same-typed parameter; **projection sweep**: replace the whole body with each
  parameter / a constant (the `gavel` lesson: a law pins a function only if no argument-ignoring body
  satisfies it).
- A mutant is **killed** if lawcheck finds a counterexample (fast) — optionally confirm with
  `bend PROOF.bend` (slow, exact). Report survivors with the mutated line. Mutants that fail to
  type-check are discarded (not counted as kills).

### 4.4 Packaging
- Lives in the monorepo `tools/lawcheck`; runs with `bun`; single binary via `bun build --compile`
  attached to GitHub releases (same approach Bend itself uses). No npm dependency required.
- First customer: mathlib — every new lemma statement is lawchecked before its proof is attempted.

### 4.5 Known limits (stated in the README)
Evaluation-by-checker can be slow for large inputs (keep sizes small; engine N later); laws over
functions need templates (v2); `exs` witness laws are skipped in v1; lawcheck finds counterexamples,
it never proves anything.

---

## 5. Bend docs — architecture

### 5.1 What it shows
- **Package page** (per name@version and per hash): description, license, files, import lines,
  dependencies and **reverse dependencies**, versions, and **status on the current compiler**:
  `checks` / `N defs rely on unsafe or foreign code` / `fails: <first error>` / `open laws`.
- **Module page:** every declaration with kind badge (type, constructor, def, law, template, effect,
  `@unsafe`), rendered signature / law statement, doc comment, source with line anchors.
- **Search:** names, doc text, and **laws by statement shape** (`List.append(_, Nil{})` finds every
  lemma mentioning that pattern) — lemma search for all of the hub, not just mathlib.
- **API diff** between versions of a named package (added / removed / changed statements).

### 5.2 Pipeline (static, incremental)
1. Fetch `hub/index.json` and `hub/names.json`.
2. For each **new hash** (content never changes → cache forever): fetch manifest and files into a
   private `BEND_LIB`.
3. Extract with `@bendlib/reader` (current compiler version): declarations, docs, imports
   (hash → package edges). Parse failures are recorded as a status, not a crash.
4. Verify: `bend <entry> --check-only` per package in a sandbox (bubblewrap/firejail; network off; 180 s
   timeout; 3 GB resident per check, watched, since the checker engine reserves GBs of address space it never touches and one hub file needs 9.6 GB) — checking never runs `main`, but the checker can loop or blow memory on
   hostile input. Re-verify all packages when a new compiler version appears (status is per compiler
   version).
5. Render static HTML (bun script, no framework) + a JSON search index; client-side search.
6. Deploy to GitHub Pages (or Cloudflare Pages); rebuild on a schedule (GitHub runs it every few
   hours) from GitHub Actions or the owner's machine.
7. `bend-docs build <dir>`: the same renderer for local packages, so authors preview their docs
   (and mathlib's own docs come from it).

### 5.3 Name and relationship to existing catalogs
- Name: open decision D2 (suggested: "Bend Docs" at `docs.bendlib.dev`, or under the org's Pages).
- Offer the extracted data (JSON) to other catalogs and lists in the ecosystem.

---

## 6. Repository layout
```
bendlib/                     GitHub: bendlib/bendlib (monorepo)
├── PLAN.md  README.md  LICENSE  AGENTS.md  RELEASES.md  toolchain.json
├── packages/bend-mathlib/   LICENSE all.bend *.bend PUBLIC_API.lock
├── packages/bendlib-kernel-list/   list.bend LICENSE README.md (published 1.0.0.0, imported by hash)
├── tools/
│   ├── comments.ts          comment lint
│   ├── install-bend.ts      installs the pinned compiler
│   ├── reader/              @bendlib/reader (TS, §2)
│   ├── lawcheck/            lawcheck CLI (TS)
│   ├── docs/                docs generator + site templates (TS)
│   └── mathlib/             check.ts lint.ts twins.ts lock.ts index.ts hash.ts release.ts
│                            devlib.ts lib.ts (+ fixtures, tools.test.ts)
├── examples/demo/           launch demo (before.bend, after.bend, demo.gif, demo.mp4, demo.sh)
├── research/experiments/    evidence for §1;  research/candidates/ (mathlib-0.2/, mathlib-0.4/, predicates/,
│                            perm/)
├── .claude-plugin/  plugins/bend-mathlib/   Claude Code marketplace and the bend-mathlib agent skill
└── .github/workflows/       ci.yml (mathlib gates, tool tests, nightly latest-compiler job)
                             docs.yml  lawcheck-release.yml (tag-triggered binaries)
```
Monorepo because a compiler change usually touches mathlib, reader and tools together.

**Language split.** Everything users import is Bend. Tool *shells* are TypeScript on Bun because
(1) the official parser/checker is `bend.ts` — reusing it is the only way to read code exactly like
the user's compiler; (2) Bun is already required by Bend, so it adds no dependency; (3) the shells need
process spawning, JSON, HTTP, fast strings and HTML, which Base lacks. Pure algorithmic cores move to
Bend *with laws* once they stabilize — first lawcheck's generators, shrinkers and mutation operators
(laws such as "every shrink candidate is smaller than its input"), called from the shell through
Bend's JS interop (`bend x.bend -o x.js` runs under Bun; the guide documents importing `.bend`
modules from JS). Dogfooding where laws add value; TypeScript for plumbing.

---

## 7. Build order

### 7.1 Shipped
Pinned toolchain and CI; `@bendlib/reader` (§2); bend-mathlib on the hub (RELEASES.md) with
check/lint/twins/lock/index/release tools and `devlib` (§3.5); a CI job holding mathlib to
`bend --verdict`, the proven kernel (F35); lawcheck 0.3 (engine C, shrinking, premises, datatypes,
template catalog, `mutate`, `--json`, `--native`, tag-triggered binaries, `install.sh`); Bend Docs
at https://bendlib.github.io/bendlib/, with per-package checker status and a pointer from every law
another package restates to its bend-mathlib lemma; an agent skill, shipped as a Claude Code plugin (`plugins/bend-mathlib`).

### 7.2 Next — the work items are beads (`br ready`); this says why the order
Lemma work first (each lemma removes a re-proof everywhere; the checker judges it), then lawcheck
(mutation mode answers the weak-laws criticism), then docs (compounds on both).

## 8. Risks that change the design

| Risk | Design response |
|---|---|
| `bend.ts` internals change daily | Single adapter (`@bendlib/reader`), version-matched fetch, golden tests per release |
| Base adds a name we use | Lowercase dot-free names (F6) + nightly collision check; ask HOC to treat lowercase dot-free as a community convention |
| A frozen predicate is wrong | §3.3 selection before publish; append-only fixes with new names + bridge theorems |
| Version skew across dependents | Encoding rule: Base-only predicates in mathlib (F4); nominal definitions only in byte-sealed kernels imported by hash (§3.1.1b) |
| Bend 2.1 changes affinity (F14) | `~`-form abstract theorems; the lock shows exactly what a migration changes |
| HOC builds official docs/lemmas | Make ours easy to adopt/merge; being upstreamed is a win |
| Hub outage/takedown (the GitHub repo was taken down once, 09-21) | Everything mirrored in git; docs site caches content by hash |
| Checker loops/blows memory on hostile packages (docs) | Sandbox, timeouts, memory caps; per-package failure is a status |
| Single publisher (bus factor) | Keep hub login recoverable (GitHub 2FA recovery codes); document the release steps in the repo; README always carries hash imports too |
| Base absorbs the basics (a Base `Nat.add_comm` needs no import) | Naming prevents errors, not irrelevance: value moves to perm/sorted/algebra/kernels and the tools; upstreaming basics ourselves is a credit win |
| Base definitions churn (argument order, fuel) | Published statements are Base terms and immutable; nightly detects, new versions repair (a version matrix is planned); kernel encodings are immune |
| Checker conversion rules change | `research/experiments/run.sh` asserts the observed outcome of every assertable F-fact (56 checks; `--self-test` proves it can fail on a perturbation), run by the scheduled `F-fact regression` step added to the `latest-compiler` job (`ci.yml`, `schedule`, `continue-on-error`). Facts without a definable assertion are explicit non-goals recorded in the script. A conversion-rule change is now caught the day the newest compiler ships. |

---

## 9. Open decisions

- **D1 — flagship name: DECIDED `bend-mathlib`** (owner, 2026-09-24).
Decided 2026-09-25 (planning pass; the owner asked for the best decisions without owner gates;
evidence in `research/candidates/predicates/evidence/` and `research/candidates/perm/generic/`):

- **D2 — docs domain: DECIDED none for now.** `https://bendlib.github.io/bendlib/` is the canonical
  URL; a domain costs money and moves no user. Revisit when traffic justifies it (`bendlib.dev`).
- **D-pred — `mem` / `sorted_by`: DECIDED** the candidate bodies verbatim
  (`research/candidates/predicates/README.md`): `mem(~A, ~eq, +x, xs)` (order `x, xs`, like `count`
  and the standard `x ∈ xs`), `sorted_by` with the `Pair.fst/snd` closure. Destructuring once is
  impossible on 2.0.27 in Base-only form (`evidence/lamdestr.bend`, `foldr0.bend`); the Bool is
  proof-only and bound erased (F26). The lint lets a predicate call its own `~` template parameters.
- **D3 — `perm`: DECIDED** the step-list kernel generic over `A: Data`, frozen as package
  `bendlib-kernel-list` 1.0.0.0: `swap_head`, `swap_at`, `apply`, `perm_steps` (was `Perm`) and the
  existential `perm`. Proved sufficient end to end (`perm/generic/msort_perm.bend`: merge sort and
  insertion sort are permutations; `perm_length`). Base-only alternatives rejected: sort equality is
  wrong for preorders, count-by-zip is stuck at variables. The kernel is published only after mathlib's
  perm lemmas and the sort theorems check against its exact final hash via `devlib`.
- **D-release — agents publish.** This machine holds the owner's hub login (`~/.bend/bendai.json`; `bender.json` before bend 2.0.36);
  release beads (label `release`) run `release.ts --publish`, tags and GitHub releases once every gate
  is green. Outreach to people stays with the owner.
- **D-invite — no personal outreach by agents;** contributors come through "good first lemma" GitHub
  issues and the README section.
