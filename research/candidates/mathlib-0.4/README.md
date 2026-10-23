# Candidate statements for 0.4: `algebra.bend`, `order.bend`, `maybe.bend`

Statements for the 0.4 modules (PLAN §3.2). Written and type-checked as candidates; **nothing here
is proved into `packages/`** and nothing is published. The model is the 0.2 candidates
(`research/candidates/mathlib-0.2/`): a batch bead copies each statement **verbatim** into the target
module and proves it there (F34).

Gates used (recorded below):
- proved files: `~/.bend/bin/bend <file> --check-only` → exactly `All terms check.`
- every file: `bun tools/lawcheck/cli.ts <file> --jobs 4 --max-instances 100` → `0 ✗`
- `*_open.bend` files hold statements whose proofs are not attempted; they intentionally fail
  `--check-only` with one `TODO` per open law (an open `law` is a hole) and are gated by lawcheck only.

## Gate results

| file | laws | `bend --check-only` | lawcheck (jobs 4, ≤100) |
|---|---|---|---|
| `algebra.bend` | 5 | `All terms check.` | `5 laws: 0 ✓ · 0 ✗ · 5 ~ · 0 !` |
| `algebra_instances.bend` | 11 | `All terms check.` | `11 laws: 11 ✓ · 0 ✗ · 0 ~ · 0 !` |
| `algebra_open.bend` | 2 | `Error: 2 TODOs found.` (open by design) | `2 laws: 0 ✓ · 0 ✗ · 2 ~ · 0 !` |
| `order.bend` | 5 | `All terms check.` | `5 laws: 0 ✓ · 0 ✗ · 5 ~ · 0 !` |
| `order_open.bend` | 6 | `Error: 6 TODOs found.` (open by design) | `6 laws: 0 ✓ · 0 ✗ · 6 ~ · 0 !` |
| `maybe.bend` | 5 | `All terms check.` | `5 laws: 1 ✓ · 0 ✗ · 4 ~ · 0 !` |

34 statements total. **The only laws lawcheck actually decides are the 11 concrete instances in
`algebra_instances.bend` plus `maybe_bind_pure`; every `~` is a template/closure/function binder
lawcheck v0.2 cannot generate, so it proves nothing there.** A `~` is not evidence of truth.

## `algebra.bend` — abstract theorems over `~A: Data` / `~op: A -> A -> A` (all proved)

Template hypotheses are declared as `for ~assoc: @x: A -> ...` (F13) and are usable many times.
Abstract laws carry no instances here, so lawcheck skips all five.

| law | instance used for | lawcheck |
|---|---|---|
| `op_assoc4` | four-way reassociation from associativity alone (instances: `List.append`) | `~` |
| `op_left_comm` | `a∘(b∘c) = b∘(a∘c)` from assoc + comm | `~` |
| `op_right_comm` | `(a∘b)∘c = (a∘c)∘b` from assoc + comm | `~` |
| `op_four` | `(a∘b)∘(c∘d) = (a∘c)∘(b∘d)` from assoc + comm | `~` |
| `op_comm3` | `(a∘b)∘c = c∘(b∘a)` from comm alone | `~` |

## `algebra_instances.bend` — abstract theorems instantiated with mathlib 0.2 lemmas (all proved)

Imports the live package by relative path (`../../../packages/bend-mathlib/*.bend`). The instance
`def`s call the abstract theorem; hypotheses are passed as local `internal_*` wrappers, because the
abstract hypothesis type is `@x -> @y -> ...` (reusable) while mathlib erases some binders
(`MNat.add_assoc(a, -b, -c)`) and Base `Nat.mul(a, +b)` marks its second argument reusable; both are
rejected where `@` is expected. The wrappers re-expose the hypothesis with plain binders.

| law | instantiated at | proof term | lawcheck |
|---|---|---|---|
| `nat_add_left_comm` | `Nat.add` | `Alg.op_left_comm` | `✓` |
| `nat_add_right_comm` | `Nat.add` | `Alg.op_right_comm` | `✓` |
| `nat_add_four` | `Nat.add` | `Alg.op_four` | `✓` |
| `nat_mul_left_comm` | `Nat.mul` | `Alg.op_left_comm` | `✓` |
| `nat_mul_right_comm` | `Nat.mul` | `Alg.op_right_comm` | `✓` |
| `nat_mul_four` | `Nat.mul` | `Alg.op_four` | `✓` |
| `bool_and_left_comm` | `Bool.and` | `Alg.op_left_comm` | `✓` |
| `bool_and_right_comm` | `Bool.and` | `Alg.op_right_comm` | `✓` |
| `bool_or_left_comm` | `Bool.or` | `Alg.op_left_comm` | `✓` |
| `bool_or_right_comm` | `Bool.or` | `Alg.op_right_comm` | `✓` |
| `list_nat_append_assoc4` | `List.append` at `List<&2, Nat>` | `Alg.op_assoc4` | `✓` |

At least one instance per required operation (`Nat.add`, `Nat.mul`, `Bool.and`, `Bool.or`,
`List.append`). `List.append` is not commutative, so only `op_assoc4` applies to it.

## `algebra_open.bend` — fold lemmas (statements only, proofs deferred)

| law | note | lawcheck |
|---|---|---|
| `foldr_op_append` | specialization of the existing `MList.foldr_append`; stated with the bead's assoc + right-identity hypotheses, which the proof does **not** need | `~` |
| `foldl_op_eq_foldr_op` | left fold = right fold for a commutative, associative operation with left identity; a genuine new fact (uses assoc + comm + identity) | `~` |

## `order.bend` — abstract preorder/total-order facts over `~le` (all proved)

Base has neither `max_by` nor `min_by`; per the bead the fallback is relation facts over a template
comparator. All five are lawcheck-skipped because `~le_trans` / `~le_antisymm` / `~le_total` have no
catalog functions.

| law | hypotheses | lawcheck |
|---|---|---|
| `le_trans3` | `~le_trans` | `~` |
| `le_trans4` | `~le_trans` | `~` |
| `le_antisymm_eq` | `~le_antisymm` | `~` |
| `le_total_true` | `~le_total` | `~` |
| `le_total_of_not_le` | `~le_total` (`le(a,b)=False` → `le(b,a)=True`) | `~` |

## `order_open.bend` — `sorted_by` facts (proved in `list.bend` since 0.7.5.0)

Imports the predicates candidate `../predicates/list_preds.bend` (`mem`, `sorted_by`), since frozen
in `packages/bend-mathlib/list.bend`, where all six laws are now proved. All six are statements that need only
transitivity (plus, for `sorted_append`, a cross-bound hypothesis). Against `list.bend`, lawcheck finds
no counterexample to five of them (✓) and skips `sorted_append`, whose `bnd` hypothesis is a function it
cannot generate.

| law | statement | lawcheck |
|---|---|---|
| `sorted_take` | `take` of a sorted list is sorted | `~` |
| `sorted_drop` | `drop` of a sorted list is sorted | `~` |
| `sorted_filter` | `filter` of a sorted list is sorted | `~` |
| `sorted_head_le_mem` | `sorted_by(x<>xs)`, `mem(y,xs)` → `le(x,y)` | `~` |
| `sorted_le_of_mem` | `sorted_by(x<>xs)`, `mem(y,x<>xs)` → `le(x,y)` | `~` |
| `sorted_append` | `sorted_by(xs)`, `sorted_by(ys)`, every `xs` element ≤ every `ys` element → `sorted_by(xs++ys)` | `~` |

## `maybe.bend` — Maybe monad laws (all proved) — experiment answer

The experiment PLAN §3.2 asked for: can monad laws for `Maybe.map`/`bind` (closures) be **stated and
proved at all** on 2.0.27? **Yes.** With `~A: Data` type templates and closures as ordinary binders
(`for f: A -> Maybe<&2, B>`, `x => ...` at use sites) all five laws type-check and their proofs close
by computation on `Some`/`None` (`bend --check-only` → `All terms check.`). lawcheck cannot evaluate
four of them because it cannot generate function-typed binders (v0.2); `maybe_bind_pure` is `✓`.

| law | statement | lawcheck |
|---|---|---|
| `maybe_pure_bind` | left identity: `bind(pure(x), f) = f(x)` | `~` |
| `maybe_bind_pure` | right identity: `bind(m, pure) = m` | `✓` |
| `maybe_bind_assoc` | associativity: `bind(bind(m,f),g) = bind(m, x=>bind(f(x),g))` | `~` |
| `maybe_map_pure` | `map(f, pure(x)) = pure(f(x))` | `~` |
| `maybe_map_compose` | `map(g, map(f, m)) = map(x=>g(f(x)), m)` | `~` |

Proposed F-fact line for the owner to record on close:

> **F35 (proposed) — Maybe monad laws are statable and provable on 2.0.27.** `pure`/`bind` left and
> right identity, `bind` associativity, and `map` identity/composition all check over `&2` with
> `~A: Data` type templates and closures as ordinary binders; `bend maybe.bend --check-only` prints
> `All terms check.`, lawcheck `1 ✓ · 0 ✗ · 4 ~`. Evidence: `research/candidates/mathlib-0.4/maybe.bend`.

## Caveats / what is not verified

- Template-binder laws (`~op`, `~le`, `~assoc`, `~z`, ...) are **not** lawchecked; lawcheck prints
  `skipped`, not evidence. Only `algebra_instances.bend` (11 ✓) and `maybe_bind_pure` are decided.
- `algebra_instances.bend` proves the *statements* by instantiating abstract theorems with the
  current package's lemmas; it does not re-verify the mathlib lemmas.
- `order_open.bend`'s six laws are proved in `list.bend` (0.7.5.0).
- `op_comm3` deliberately needs only commutativity (no associativity); it is labelled that way.
- `foldr_op_append`'s assoc + identity hypotheses are unused by its intended proof; it is recorded
  as the bead specified but is subsumed by `MList.foldr_append`.

## Proposed follow-up batches (this session has no `br` write access)

Three batches, each ≤15 statements, statements copied verbatim, same gates as the 0.2 batches:

1. **`algebra.bend`** — the 5 abstract laws + the 10 Nat/Bool instances (15) — depends on nothing
   new.
2. **`algebra` tail + order** — `list_nat_append_assoc4` + `algebra_open.bend` (2) + `order.bend`
   (5) = 8; `order_open.bend` (6) lands only after the `mem`/`sorted_by` freeze.
3. **`maybe.bend`** — 5 laws.

## Reproduction

```sh
~/.bend/bin/bend research/candidates/mathlib-0.4/algebra.bend --check-only
~/.bend/bin/bend research/candidates/mathlib-0.4/algebra_instances.bend --check-only
~/.bend/bin/bend research/candidates/mathlib-0.4/order.bend --check-only
~/.bend/bin/bend research/candidates/mathlib-0.4/maybe.bend --check-only
for f in algebra algebra_instances algebra_open order order_open maybe; do
  bun tools/lawcheck/cli.ts research/candidates/mathlib-0.4/$f.bend --jobs 4 --max-instances 100
done
```
