---
name: bend-mathlib
description: Use when writing or proving Bend 2 laws (a `law` and its proof `def`) that need basic facts about Nat, Bool, List, String, Maybe or equality. Imports proved lemmas from the bend-mathlib hub package instead of re-proving them, finds the right lemma, rewrites with it, and checks a statement with lawcheck before proving it.
---

# bend-mathlib

bend-mathlib is a BendHub package of machine-checked lemmas for Bend 2: 445 lemmas about `Nat`,
`Bool`, `List`, `String`, `Maybe`, equality, abstract orders and associative/commutative
operations, plus permutation and sorting theorems. Every statement is locked, so a newer version
never changes one you use. Before you prove a basic fact (`add_comm`, `append_assoc`,
`reverse_reverse`, `le_trans`, `take_append_drop` …), import it.

## Import

```python
import bend-mathlib@0.7.4.0/nat.bend as MNat
import bend-mathlib@0.7.4.0/list.bend as MList
```

Modules: `nat`, `bool`, `list`, `string`, `maybe`, `equal`, `order`, `algebra` (laws), `perm`
(permutations, `insert_by`/`isort_by`/`merge_by`/`sort_by`) and `sort` (those sorts return sorted
lists).
Every module passes `bend --verdict` on Bend 2.0.38, so a project that checks with it can import
any of them (on 2.0.37 and earlier, `algebra`, `order`, `sort` and `all` were out of the kernel's
scope, bendlang/bend#1182).
Pin by content hash if you want bytes that can never change:
`import 0xcdaf59a0332a2e0cdb289bf7a32fba62/nat.bend as MNat`.

## Find a lemma

- Every law with its statement, one per line as `module<TAB>name<TAB>statement` (grep it):
  `curl -s https://bendlib.github.io/bendlib/lemmas.txt | grep '^bend-mathlib' | grep 'Nat.add'`
- The `perm` and `sort` theorems are typed defs, not laws, so that list omits them; read their
  signatures in the source: https://github.com/bendlib/bendlib/tree/main/packages/bend-mathlib
- Browse or search by shape (`Nat.add(_, 0n)`): https://bendlib.github.io/bendlib/search.html
- Names follow Lean's mathlib (`add_comm`, `mul_add`, `append_assoc`, `le_trans`, `take_append_drop`).
- Each equation has a generated `_sym` twin with the sides swapped: `add_zero` states
  `Nat.add(x, 0n) == x`, `add_zero_sym` states `x == Nat.add(x, 0n)`.

## Call a lemma

A lemma is a def; pass its arguments in the order of its `for` binders, erased ones (`-x`) too.
List and other generic lemmas take the quantity and element type first. Template parameters
(`~A`, `~le`) are passed with a `~`. (`MPerm` and `MSort` are `perm.bend` and `sort.bend`,
imported like the two above.)

```python
MNat.add_comm(a, b)                       # {Nat.add(a, b) == Nat.add(b, a) : Nat}
MList.reverse_reverse(&2, U32, xs)        # {List.reverse(&2, U32, List.reverse(&2, U32, xs)) == xs : List<&2, U32>}
MNat.le_trans(a, b, c, h_ab, h_bc)        # premises are proofs: h_ab : MNat.le(a, b), which is {Nat.is_le(a, b) == True{} : Bool}
MSort.sort_by_sorted_nat(xs)              # MList.sorted_by(~Nat, ~Nat.is_le, MPerm.sort_by(~Nat, ~Nat.is_le, xs))
```

## Rewrite with a lemma

`%e : P` rewrites with the equation `e` inside the goal `P`: it replaces the right side of `e` with
its left side, at the spot marked `_`. Use the `_sym` twin to rewrite the other way. A worked proof
(checks on bend 2.0.38):

```python
import Base
import bend-mathlib@0.7.4.0/nat.bend as MNat
import bend-mathlib@0.7.4.0/list.bend as MList

law rev_len:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.reverse(&2, U32, List.append(&2, U32, xs, ys))) == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}

def rev_len(xs, ys):
  %MList.length_reverse_sym(&2, U32, List.append(&2, U32, xs, ys)) : {_ == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}
  %MList.length_append_sym(&2, U32, xs, ys) : {_ == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}
  %MList.length_append_sym(&2, U32, ys, xs) : {Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) == _ : Nat}
  MNat.add_comm(List.length(&2, U32, xs), List.length(&2, U32, ys))
```

`Equal.sym(T, l, r, e)` flips an equation; `Equal.trans` chains two.

## Check a statement before proving it

A false law wastes the whole proof attempt. lawcheck evaluates the law on many small inputs with
the bend checker and prints a shrunk counterexample if one exists
(https://github.com/bendlib/bendlib/tree/main/tools/lawcheck). Install it once (Linux and macOS,
into `~/.local/bin`), then check:

```sh
curl -fsSL https://raw.githubusercontent.com/bendlib/bendlib/main/tools/lawcheck/install.sh | sh
lawcheck my_laws.bend --law rev_len   # ✗ = false: fix the statement; ✓ = no counterexample found
```

A ✓ is evidence, not a proof: the law still needs its proof `def`.

## When a lemma is missing

Prove it locally with `internal_` helpers, and open an issue or PR at
https://github.com/bendlib/bendlib (issues labelled "good first lemma" are open starting points).
Never use `@unsafe` to stand in for a lemma: a file that relies on unsafe code fails the check.
