# bend-mathlib/perm.bend: step-list permutations over bendlib-kernel-list, plus sort value defs and proofs.
# Resolves the published kernel bendlib-kernel-list@1.0.0.0 by its content hash; see packages/bendlib-kernel-list/README.md.
import Base
import 0xb5c8145e53a6a127d611f45f602666ec/list.bend as K

def internal_shift(+s: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +i <> rest:
      (1n+i) <> internal_shift(rest)

def internal_apply_app(-A: Data, +s1: List<&2, Nat>, +s2: List<&2, Nat>, +xs: List<&2, A>) -> {K.apply(A, List.append(&2, Nat, s1, s2), xs) == K.apply(A, s2, K.apply(A, s1, xs)) : List<&2, A>}:
  match s1:
    case Nil{}:
      {==}
    case +i <> rest:
      internal_apply_app(A, rest, s2, K.swap_at(A, i, xs))

def internal_apply_shift(-A: Data, +s: List<&2, Nat>, +x: A, +xs: List<&2, A>) -> {K.apply(A, internal_shift(s), x <> xs) == x <> K.apply(A, s, xs) : List<&2, A>}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      internal_apply_shift(A, rest, x, K.swap_at(A, i, xs))

# Permutation is reflexive.
def perm_refl(-A: Data, -xs: List<&2, A>) -> K.perm(A, xs, xs):
  (Nil{}, {==})

# The empty list is a permutation of itself.
def perm_nil(-A: Data) -> K.perm(A, Nil{}, Nil{}):
  (Nil{}, {==})

# Swapping the two leading elements is a permutation.
def perm_swap(-A: Data, -x: A, -y: A, -t: List<&2, A>) -> K.perm(A, x <> y <> t, y <> x <> t):
  (0n <> Nil{}, {==})

def internal_trans_eq(-A: Data, +s1: List<&2, Nat>, +s2: List<&2, Nat>, +xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>, e1: K.perm_steps(A, s1, xs, ys), e2: K.perm_steps(A, s2, ys, zs)) -> K.perm_steps(A, List.append(&2, Nat, s1, s2), xs, zs):
  %Equal.sym(List<&2, A>, K.apply(A, List.append(&2, Nat, s1, s2), xs), K.apply(A, s2, K.apply(A, s1, xs)), internal_apply_app(A, s1, s2, xs)) : {_ == zs : List<&2, A>}
  %Equal.sym(List<&2, A>, K.apply(A, s1, xs), ys, e1) : {K.apply(A, s2, _) == zs : List<&2, A>}
  e2

# Permutation is transitive.
def perm_trans(-A: Data, +xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>, h1: K.perm(A, xs, ys), h2: K.perm(A, ys, zs)) -> K.perm(A, xs, zs):
  (s1, e1) = h1
  (s2, e2) = h2
  +s1 = s1
  +s2 = s2
  (List.append(&2, Nat, s1, s2), internal_trans_eq(A, s1, s2, xs, ys, zs, e1, e2))

def internal_cons_eq(-A: Data, +s: List<&2, Nat>, +x: A, +xs: List<&2, A>, -ys: List<&2, A>, e: K.perm_steps(A, s, xs, ys)) -> K.perm_steps(A, internal_shift(s), x <> xs, x <> ys):
  %Equal.sym(List<&2, A>, K.apply(A, internal_shift(s), x <> xs), x <> K.apply(A, s, xs), internal_apply_shift(A, s, x, xs)) : {_ == x <> ys : List<&2, A>}
  %Equal.sym(List<&2, A>, K.apply(A, s, xs), ys, e) : {x <> _ == x <> ys : List<&2, A>}
  {==}

# Prepending the same element preserves permutation.
def perm_cons(-A: Data, +x: A, +xs: List<&2, A>, -ys: List<&2, A>, h: K.perm(A, xs, ys)) -> K.perm(A, x <> xs, x <> ys):
  (s, e) = h
  +s = s
  (internal_shift(s), internal_cons_eq(A, s, x, xs, ys, e))

# A Perm hypothesis in existential form is reusable.
def perm_dup(-A: Data, -xs: List<&2, A>, -ys: List<&2, A>, +h: K.perm(A, xs, ys)) -> K.perm(A, xs, ys) & K.perm(A, xs, ys):
  (h, h)

# Insertion into a list, generic comparator (structural, Base-only branching via Bool.pick).
def insert_by(~A: Data, ~le: A -> A -> Bool, +x: A, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      x <> Nil{}
    case +y <> +t:
      Bool.pick(List<&2, A>, le(x, y), x <> y <> t, y <> insert_by(~A, ~le, x, t))

# Insertion sort by the comparator le.
def isort_by(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      insert_by(~A, ~le, x, isort_by(~A, ~le, t))

def internal_ins_pick(-A: Data, b: Bool, +x: A, +y: A, +t: List<&2, A>, -r: List<&2, A>, ih: K.perm(A, x <> t, r)) -> K.perm(A, x <> y <> t, Bool.pick(List<&2, A>, b, x <> y <> t, y <> r)):
  match b:
    case True{}:
      perm_refl(A, x <> y <> t)
    case False{}:
      perm_trans(A, x <> y <> t, y <> x <> t, y <> r, perm_swap(A, x, y, t), perm_cons(A, y, x <> t, r, ih))

# Inserting x into xs permutes x <> xs.
def insert_by_perm(~A: Data, ~le: A -> A -> Bool, +x: A, +xs: List<&2, A>) -> K.perm(A, x <> xs, insert_by(~A, ~le, x, xs)):
  match xs:
    case Nil{}:
      perm_refl(A, x <> Nil{})
    case +y <> t:
      internal_ins_pick(A, le(x, y), x, y, t, insert_by(~A, ~le, x, t), insert_by_perm(~A, ~le, x, t))

# Insertion sort permutes its input.
def isort_by_perm(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> K.perm(A, xs, isort_by(~A, ~le, xs)):
  match xs:
    case Nil{}:
      perm_refl(A, Nil{})
    case +x <> t:
      perm_trans(A, x <> t, x <> isort_by(~A, ~le, t), isort_by(~A, ~le, x <> t), perm_cons(A, x, t, isort_by(~A, ~le, t), isort_by_perm(~A, ~le, t)), insert_by_perm(~A, ~le, x, isort_by(~A, ~le, t)))

# Insertion sort permutes a Nat list.
def isort_by_perm_nat(+xs: List<&2, Nat>) -> K.perm(Nat, xs, isort_by(~Nat, ~Nat.is_le, xs)):
  isort_by_perm(~Nat, ~Nat.is_le, xs)

def internal_append_nil(-A: Data, +ys: List<&2, A>) -> {List.append(&2, A, ys, Nil{}) == ys : List<&2, A>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> t:
      %Equal.sym(List<&2, A>, List.append(&2, A, t, Nil{}), t, internal_append_nil(A, t)) : {y <> _ == y <> t : List<&2, A>}
      {==}

# Appending Nil is a permutation, by the empty step list.
def perm_append_nil(-A: Data, +xs: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, Nil{}), xs):
  (Nil{}, internal_append_nil(A, xs))

# Moving an element from the middle to the front is a permutation.
def perm_move(-A: Data, +xs: List<&2, A>, +y: A, +t: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, y <> t), y <> List.append(&2, A, xs, t)):
  match xs:
    case Nil{}:
      perm_refl(A, y <> t)
    case +x <> r:
      perm_trans(A, x <> List.append(&2, A, r, y <> t), x <> y <> List.append(&2, A, r, t), y <> x <> List.append(&2, A, r, t), perm_cons(A, x, List.append(&2, A, r, y <> t), y <> List.append(&2, A, r, t), perm_move(A, r, y, t)), perm_swap(A, x, y, List.append(&2, A, r, t)))

# Merges two lists, taking the head of xs first whenever le(x, y) holds.
def merge_by(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs ys:
    case Nil{} _:
      ys
    case +x <> +xt Nil{}:
      x <> xt
    case +x <> +xt +y <> +yt:
      Bool.pick(List<&2, A>, le(x, y), x <> merge_by(~A, ~le, xt, y <> yt), y <> merge_by(~A, ~le, x <> xt, yt))

def internal_merge_pick(-A: Data, b: Bool, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, -m1: List<&2, A>, -m2: List<&2, A>, ih1: K.perm(A, List.append(&2, A, xt, y <> yt), m1), ih2: K.perm(A, x <> List.append(&2, A, xt, yt), m2)) -> K.perm(A, x <> List.append(&2, A, xt, y <> yt), Bool.pick(List<&2, A>, b, x <> m1, y <> m2)):
  match b:
    case True{}:
      perm_cons(A, x, List.append(&2, A, xt, y <> yt), m1, ih1)
    case False{}:
      perm_trans(A, x <> List.append(&2, A, xt, y <> yt), y <> x <> List.append(&2, A, xt, yt), y <> m2, perm_move(A, x <> xt, y, yt), perm_cons(A, y, x <> List.append(&2, A, xt, yt), m2, ih2))

# Merging permutes the concatenation.
def merge_by_perm(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, ys), merge_by(~A, ~le, xs, ys)):
  match xs ys:
    case Nil{} _:
      perm_refl(A, ys)
    case +x <> +xt Nil{}:
      perm_cons(A, x, List.append(&2, A, xt, Nil{}), xt, perm_append_nil(A, xt))
    case +x <> +xt +y <> +yt:
      internal_merge_pick(A, le(x, y), x, xt, y, yt, merge_by(~A, ~le, xt, y <> yt), merge_by(~A, ~le, x <> xt, yt), merge_by_perm(~A, ~le, xt, y <> yt), merge_by_perm(~A, ~le, x <> xt, yt))

# Merging two Nat lists permutes their concatenation.
def merge_by_perm_nat(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> K.perm(Nat, List.append(&2, Nat, xs, ys), merge_by(~Nat, ~Nat.is_le, xs, ys)):
  merge_by_perm(~Nat, ~Nat.is_le, xs, ys)

# Moving the front element into the middle is a permutation.
def perm_move_rev(-A: Data, +xs: List<&2, A>, +y: A, +t: List<&2, A>) -> K.perm(A, y <> List.append(&2, A, xs, t), List.append(&2, A, xs, y <> t)):
  match xs:
    case Nil{}:
      perm_refl(A, y <> t)
    case +x <> r:
      perm_trans(A, y <> x <> List.append(&2, A, r, t), x <> y <> List.append(&2, A, r, t), x <> List.append(&2, A, r, y <> t), perm_swap(A, y, x, List.append(&2, A, r, t)), perm_cons(A, x, y <> List.append(&2, A, r, t), List.append(&2, A, r, y <> t), perm_move_rev(A, r, y, t)))

# Appending commutes up to permutation (derived without symmetry).
def perm_append_comm(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, ys), List.append(&2, A, ys, xs)):
  match xs:
    case Nil{}:
      (Nil{}, Equal.sym(List<&2, A>, List.append(&2, A, ys, Nil{}), ys, internal_append_nil(A, ys)))
    case +x <> r:
      perm_trans(A, x <> List.append(&2, A, r, ys), x <> List.append(&2, A, ys, r), List.append(&2, A, ys, x <> r), perm_cons(A, x, List.append(&2, A, r, ys), List.append(&2, A, ys, r), perm_append_comm(A, r, ys)), perm_move_rev(A, ys, x, r))

# Permuting the right operand of an append gives a permutation of the append.
def perm_append_right(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, -zs: List<&2, A>, h: K.perm(A, ys, zs)) -> K.perm(A, List.append(&2, A, xs, ys), List.append(&2, A, xs, zs)):
  match xs:
    case Nil{}:
      h
    case +x <> r:
      perm_cons(A, x, List.append(&2, A, r, ys), List.append(&2, A, r, zs), perm_append_right(A, r, ys, zs, h))

# Permuting both operands of an append gives a permutation of the append.
def perm_append(-A: Data, +xs: List<&2, A>, +xs2: List<&2, A>, +ys: List<&2, A>, -ys2: List<&2, A>, p: K.perm(A, xs, xs2), q: K.perm(A, ys, ys2)) -> K.perm(A, List.append(&2, A, xs, ys), List.append(&2, A, xs2, ys2)):
  perm_trans(A, List.append(&2, A, xs, ys), List.append(&2, A, ys, xs), List.append(&2, A, xs2, ys2), perm_append_comm(A, xs, ys), perm_trans(A, List.append(&2, A, ys, xs), List.append(&2, A, ys, xs2), List.append(&2, A, xs2, ys2), perm_append_right(A, ys, xs, xs2, p), perm_trans(A, List.append(&2, A, ys, xs2), List.append(&2, A, xs2, ys), List.append(&2, A, xs2, ys2), perm_append_comm(A, ys, xs2), perm_append_right(A, xs2, ys, ys2, q))))

# The elements of a list at even positions (0, 2, 4, ...).
def evens(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> r:
      match r:
        case Nil{}:
          x <> Nil{}
        case +y <> t:
          x <> evens(A, t)

# The elements of a list at odd positions (1, 3, 5, ...).
def odds(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> r:
      match r:
        case Nil{}:
          Nil{}
        case +y <> t:
          y <> odds(A, t)

# Splitting into evens and odds is a permutation.
def split_perm(-A: Data, +xs: List<&2, A>) -> K.perm(A, xs, List.append(&2, A, evens(A, xs), odds(A, xs))):
  match xs:
    case Nil{}:
      perm_refl(A, Nil{})
    case +x <> r:
      match r:
        case Nil{}:
          perm_refl(A, x <> Nil{})
        case +y <> t:
          perm_cons(A, x, y <> t, List.append(&2, A, evens(A, t), y <> odds(A, t)), perm_trans(A, y <> t, y <> List.append(&2, A, evens(A, t), odds(A, t)), List.append(&2, A, evens(A, t), y <> odds(A, t)), perm_cons(A, y, t, List.append(&2, A, evens(A, t), odds(A, t)), split_perm(A, t)), perm_move_rev(A, evens(A, t), y, odds(A, t))))

# Merge sort with fuel (the fuel only bounds recursion; it never affects the permutation).
def msort_by(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +xs: List<&2, A>) -> List<&2, A>:
  match fuel:
    case 0n:
      xs
    case 1n++f:
      merge_by(~A, ~le, msort_by(~A, ~le, f, evens(A, xs)), msort_by(~A, ~le, f, odds(A, xs)))

# Merge sort permutes its input, for any fuel.
def msort_by_perm(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +xs: List<&2, A>) -> K.perm(A, xs, msort_by(~A, ~le, fuel, xs)):
  match fuel:
    case 0n:
      perm_refl(A, xs)
    case 1n++f:
      perm_trans(A, xs, List.append(&2, A, evens(A, xs), odds(A, xs)), msort_by(~A, ~le, 1n+f, xs), split_perm(A, xs), perm_trans(A, List.append(&2, A, evens(A, xs), odds(A, xs)), List.append(&2, A, msort_by(~A, ~le, f, evens(A, xs)), msort_by(~A, ~le, f, odds(A, xs))), msort_by(~A, ~le, 1n+f, xs), perm_append(A, evens(A, xs), msort_by(~A, ~le, f, evens(A, xs)), odds(A, xs), msort_by(~A, ~le, f, odds(A, xs)), msort_by_perm(~A, ~le, f, evens(A, xs)), msort_by_perm(~A, ~le, f, odds(A, xs))), merge_by_perm(~A, ~le, msort_by(~A, ~le, f, evens(A, xs)), msort_by(~A, ~le, f, odds(A, xs)))))

# Merge sort by the comparator le.
def sort_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> List<&2, A>:
  msort_by(~A, ~le, List.length(&2, A, xs), xs)

# The sort permutes its input.
def sort_by_perm(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> K.perm(A, xs, sort_by(~A, ~le, xs)):
  msort_by_perm(~A, ~le, List.length(&2, A, xs), xs)

# Merge sort permutes a Nat list.
def sort_by_perm_nat(+xs: List<&2, Nat>) -> K.perm(Nat, xs, sort_by(~Nat, ~Nat.is_le, xs)):
  sort_by_perm(~Nat, ~Nat.is_le, xs)

def internal_sort_nat_test() -> {sort_by(~Nat, ~Nat.is_le, [5n, 1n, 4n, 2n, 3n, 1n]) == [1n, 1n, 2n, 3n, 4n, 5n] : List<&2, Nat>}:
  {==}

def internal_swap_head_invol(-A: Data, xs: List<&2, A>) -> {K.swap_head(A, K.swap_head(A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          {==}
        case +y <> u:
          {==}

def internal_swap_at_invol(-A: Data, +i: Nat, +xs: List<&2, A>) -> {K.swap_at(A, i, K.swap_at(A, i, xs)) == xs : List<&2, A>}:
  match i:
    case 0n:
      internal_swap_head_invol(A, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case +x <> t:
          %Equal.sym(List<&2, A>, K.swap_at(A, p, K.swap_at(A, p, t)), t, internal_swap_at_invol(A, p, t)) : {x <> _ == x <> t : List<&2, A>}
          {==}

def internal_invert(+s: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +i <> rest:
      List.append(&2, Nat, internal_invert(rest), i <> Nil{})

def internal_apply_invert(-A: Data, +s: List<&2, Nat>, +xs: List<&2, A>) -> {K.apply(A, internal_invert(s), K.apply(A, s, xs)) == xs : List<&2, A>}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      %Equal.sym(List<&2, A>, K.apply(A, List.append(&2, Nat, internal_invert(rest), i <> Nil{}), K.apply(A, rest, K.swap_at(A, i, xs))), K.apply(A, i <> Nil{}, K.apply(A, internal_invert(rest), K.apply(A, rest, K.swap_at(A, i, xs)))), internal_apply_app(A, internal_invert(rest), i <> Nil{}, K.apply(A, rest, K.swap_at(A, i, xs)))) : {_ == xs : List<&2, A>}
      %Equal.sym(List<&2, A>, K.apply(A, internal_invert(rest), K.apply(A, rest, K.swap_at(A, i, xs))), K.swap_at(A, i, xs), internal_apply_invert(A, rest, K.swap_at(A, i, xs))) : {K.apply(A, i <> Nil{}, _) == xs : List<&2, A>}
      internal_swap_at_invol(A, i, xs)

def internal_sym_eq(-A: Data, +s: List<&2, Nat>, +xs: List<&2, A>, -ys: List<&2, A>, e: K.perm_steps(A, s, xs, ys)) -> K.perm_steps(A, internal_invert(s), ys, xs):
  %e : {K.apply(A, internal_invert(s), _) == xs : List<&2, A>}
  internal_apply_invert(A, s, xs)

# Permutation is symmetric.
def perm_sym(-A: Data, +xs: List<&2, A>, -ys: List<&2, A>, h: K.perm(A, xs, ys)) -> K.perm(A, ys, xs):
  (s, e) = h
  +s = s
  (internal_invert(s), internal_sym_eq(A, s, xs, ys, e))

def internal_swap_head_length(-A: Data, xs: List<&2, A>) -> {List.length(&2, A, K.swap_head(A, xs)) == List.length(&2, A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          {==}
        case +y <> u:
          {==}

def internal_swap_at_length(-A: Data, +i: Nat, +xs: List<&2, A>) -> {List.length(&2, A, K.swap_at(A, i, xs)) == List.length(&2, A, xs) : Nat}:
  match i:
    case 0n:
      internal_swap_head_length(A, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case +x <> t:
          %Equal.sym(Nat, List.length(&2, A, K.swap_at(A, p, t)), List.length(&2, A, t), internal_swap_at_length(A, p, t)) : {1n+_ == 1n+List.length(&2, A, t) : Nat}
          {==}

def internal_apply_length(-A: Data, +s: List<&2, Nat>, +xs: List<&2, A>) -> {List.length(&2, A, K.apply(A, s, xs)) == List.length(&2, A, xs) : Nat}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      Equal.trans(Nat, List.length(&2, A, K.apply(A, rest, K.swap_at(A, i, xs))), List.length(&2, A, K.swap_at(A, i, xs)), List.length(&2, A, xs), internal_apply_length(A, rest, K.swap_at(A, i, xs)), internal_swap_at_length(A, i, xs))

def internal_length_eq(-A: Data, +s: List<&2, Nat>, +xs: List<&2, A>, -ys: List<&2, A>, e: K.perm_steps(A, s, xs, ys)) -> {List.length(&2, A, ys) == List.length(&2, A, xs) : Nat}:
  %e : {List.length(&2, A, _) == List.length(&2, A, xs) : Nat}
  internal_apply_length(A, s, xs)

# Permutation preserves length.
def perm_length(-A: Data, +xs: List<&2, A>, -ys: List<&2, A>, h: K.perm(A, xs, ys)) -> {List.length(&2, A, ys) == List.length(&2, A, xs) : Nat}:
  (s, e) = h
  internal_length_eq(A, s, xs, ys, e)
