# bend-mathlib/list.bend: List lemmas (append, reverse, length, take, drop, map, fold, filter).
import Base
import ./nat.bend as MNat
import ./bool.bend as MBool

# The empty list is a right identity for append: xs ++ [] = xs.
law append_nil:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

def append_nil(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

# The empty list is a left identity for append: [] ++ xs = xs.
law nil_append:
  for -a: Quant
  for -A: Kind(a)
  for -xs: List<a, A>
  {List.append(a, A, Nil{}, xs) == xs : List<a, A>}

def nil_append(a, A, xs):
  {==}

# Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
law append_assoc:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -zs: List<a, A>
  {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}

def append_assoc(a, A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(a, A, t, ys, zs) : {h <> List.append(a, A, List.append(a, A, t, ys), zs) == h <> _ : List<a, A>}
      {==}

# The length of an append is the sum of the lengths.
law length_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

def length_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(a, A, t, ys) : {1n+List.length(a, A, List.append(a, A, t, ys)) == 1n+_ : Nat}
      {==}

def internal_reverse_go_append(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -acc: List<a, A>) -> {List.reverse.go(a, A, xs, List.append(a, A, ys, acc)) == List.append(a, A, List.reverse.go(a, A, xs, ys), acc) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_go_append(a, A, t, h <> ys, acc)

# The reverse accumulator loop appends the reversed list to the accumulator.
law reverse_go_spec:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -acc: List<a, A>
  {List.reverse.go(a, A, xs, acc) == List.append(a, A, List.reverse(a, A, xs), acc) : List<a, A>}

def reverse_go_spec(a, A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_go_append(a, A, t, h <> Nil{}, acc)

def internal_reverse_append_go(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -acc: List<a, A>) -> {List.reverse.go(a, A, List.append(a, A, xs, ys), acc) == List.reverse.go(a, A, ys, List.reverse.go(a, A, xs, acc)) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_append_go(a, A, t, ys, h <> acc)

# Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs.
law reverse_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.reverse(a, A, List.append(a, A, xs, ys)) == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}

def reverse_append(a, A, xs, ys):
  Equal.trans(List<a, A>, List.reverse(a, A, List.append(a, A, xs, ys)), List.reverse.go(a, A, ys, List.reverse(a, A, xs)), List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)), internal_reverse_append_go(a, A, xs, ys, Nil{}), reverse_go_spec(a, A, ys, List.reverse(a, A, xs)))

def internal_reverse_go_go(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>) -> {List.reverse.go(a, A, List.reverse.go(a, A, xs, acc), Nil{}) == List.reverse.go(a, A, acc, xs) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_go_go(a, A, t, h <> acc)

# Reversing twice gives the list back.
law reverse_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.reverse(a, A, List.reverse(a, A, xs)) == xs : List<a, A>}

def reverse_reverse(a, A, xs):
  internal_reverse_go_go(a, A, xs, Nil{})

def internal_length_reverse_go(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>, +n: Nat, e: {List.length(a, A, acc) == n : Nat}) -> {List.length(a, A, List.reverse.go(a, A, xs, acc)) == Nat.add(n, List.length(a, A, xs)) : Nat}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(n, 0n), n, MNat.add_zero(n)) : {List.length(a, A, acc) == _ : Nat}
      e
    case h <> t:
      %Equal.sym(Nat, Nat.add(n, 1n+List.length(a, A, t)), 1n+Nat.add(n, List.length(a, A, t)), MNat.add_succ(n, List.length(a, A, t))) : {List.length(a, A, List.reverse.go(a, A, t, h <> acc)) == _ : Nat}
      internal_length_reverse_go(a, A, t, h <> acc, 1n+n, Equal.cong(Nat, Nat, k => 1n+k, List.length(a, A, acc), n, e))

# Reversing preserves the length.
law length_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.length(a, A, List.reverse(a, A, xs)) == List.length(a, A, xs) : Nat}

def length_reverse(a, A, xs):
  internal_length_reverse_go(a, A, xs, Nil{}, 0n, {==})

# A right fold over an append folds the first part onto the fold of the second.
law foldr_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: A -> B -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) : B}

def foldr_append(a, A, B, f, xs, ys, z):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %foldr_append(~a, ~A, ~B, ~f, t, ys, z) : {f(h, List.foldr(~a, ~A, ~B, ~f, List.append(a, A, t, ys), z)) == f(h, _) : B}
      {==}

# Taking n elements and appending the rest after dropping n gives the list back.
law take_append_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) == xs : List<a, A>}

def take_append_drop(a, A, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %take_append_drop(a, A, t, p) : {h <> List.append(a, A, List.take(a, A, t, p), List.drop(a, A, t, p)) == h <> _ : List<a, A>}
      {==}

# Mapping preserves the length.
law length_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.length(&1, B, List.map(~A, ~B, ~f, xs)) == List.length(&1, A, xs) : Nat}

def length_map(A, B, f, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_map(~A, ~B, ~f, t) : {1n+List.length(&1, B, List.map(~A, ~B, ~f, t)) == 1n+_ : Nat}
      {==}

# Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys.
law map_append:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for -ys: List<A>
  {List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) == List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) : List<B>}

def map_append(A, B, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %map_append(~A, ~B, ~f, t, ys) : {f(h) <> List.map(~A, ~B, ~f, List.append(&1, A, t, ys)) == f(h) <> _ : List<B>}
      {==}

# Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs.
law map_map:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C
  for xs: List<A>
  {List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~C, ~(x => g(f(x))), xs) : List<C>}

def map_map(A, B, C, f, g, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %map_map(~A, ~B, ~C, ~f, ~g, t) : {g(f(h)) <> List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, t)) == g(f(h)) <> _ : List<C>}
      {==}

# Taking zero elements gives the empty list.
law take_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.take(a, A, xs, 0n) == Nil{} : List<a, A>}

def take_zero(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# Dropping zero elements gives the list back.
law drop_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.drop(a, A, xs, 0n) == xs : List<a, A>}

def drop_zero(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# Taking from the empty list gives the empty list.
law take_nil:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {List.take(a, A, Nil{}, n) == Nil{} : List<a, A>}

def take_nil(a, A, n):
  {==}

# Dropping from the empty list gives the empty list.
law drop_nil:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {List.drop(a, A, Nil{}, n) == Nil{} : List<a, A>}

def drop_nil(a, A, n):
  {==}

# Taking n elements leaves min(n, length) of them.
law length_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.take(a, A, xs, n)) == Nat.min(n, List.length(a, A, xs)) : Nat}

def length_take(a, A, xs, n):
  match xs n:
    case Nil{} _:
      Equal.sym(Nat, Nat.min(n, 0n), 0n, MNat.min_zero(n))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %length_take(a, A, t, p) : {1n+List.length(a, A, List.take(a, A, t, p)) == 1n+_ : Nat}
      {==}

# Dropping n elements leaves length - n of them.
law length_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.drop(a, A, xs, n)) == Nat.sub(List.length(a, A, xs), n) : Nat}

def length_drop(a, A, xs, n):
  match xs n:
    case Nil{} _:
      Equal.sym(Nat, Nat.sub(0n, n), 0n, MNat.zero_sub(n))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      length_drop(a, A, t, p)

# Taking as many elements as the list has gives the list back.
law take_length:
  for -A: Data
  for +xs: List<&2, A>
  {List.take(&2, A, xs, List.length(&2, A, xs)) == xs : List<&2, A>}

def take_length(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %take_length(A, t) : {h <> List.take(&2, A, t, List.length(&2, A, t)) == h <> _ : List<&2, A>}
      {==}

# Dropping as many elements as the list has gives the empty list.
law drop_length:
  for -A: Data
  for +xs: List<&2, A>
  {List.drop(&2, A, xs, List.length(&2, A, xs)) == Nil{} : List<&2, A>}

def drop_length(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      drop_length(A, t)

# Taking m from the first n is taking min(n, m).
law take_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for m: Nat
  {List.take(a, A, List.take(a, A, xs, n), m) == List.take(a, A, xs, Nat.min(n, m)) : List<a, A>}

def take_take(a, A, xs, n, m):
  match xs n m:
    case Nil{} _ _:
      {==}
    case h <> t 0n _:
      {==}
    case h <> t 1n+p 0n:
      {==}
    case h <> t 1n+p 1n+q:
      %take_take(a, A, t, p, q) : {h <> List.take(a, A, List.take(a, A, t, p), q) == h <> _ : List<a, A>}
      {==}

# Dropping m after dropping n is dropping n + m.
law drop_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -m: Nat
  {List.drop(a, A, List.drop(a, A, xs, n), m) == List.drop(a, A, xs, Nat.add(n, m)) : List<a, A>}

def drop_drop(a, A, xs, n, m):
  match xs n m:
    case Nil{} _ _:
      {==}
    case h <> t 0n _:
      {==}
    case h <> t 1n+p _:
      drop_drop(a, A, t, p, m)

# Reversing the empty list gives the empty list.
law reverse_nil:
  for -a: Quant
  for -A: Kind(a)
  {List.reverse(a, A, Nil{}) == Nil{} : List<a, A>}

def reverse_nil(a, A):
  {==}

# Reversing a one-element list gives it back.
law reverse_singleton:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  {List.reverse(a, A, [x]) == [x] : List<a, A>}

def reverse_singleton(a, A, x):
  {==}

# Replicating x n times gives a list of length n.
law length_replicate:
  for -A: Data
  for n: Nat
  for -x: A
  {List.length(&2, A, List.replicate(A, n, x)) == n : Nat}

def length_replicate(A, n, x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %length_replicate(A, p, x) : {1n+List.length(&2, A, List.replicate(A, p, x)) == 1n+_ : Nat}
      {==}

def internal_length_range_go(+n: Nat, acc: List<&2, Nat>) -> {List.length(&2, Nat, List.range.go(n, acc)) == Nat.add(n, List.length(&2, Nat, acc)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %MNat.add_succ(p, List.length(&2, Nat, acc)) : {List.length(&2, Nat, List.range.go(p, p <> acc)) == _ : Nat}
      internal_length_range_go(p, p <> acc)

# Range(n) has length n.
law length_range:
  for n: Nat
  {List.length(&2, Nat, List.range(n)) == n : Nat}

def length_range(n):
  +n = n
  %Equal.sym(Nat, List.length(&2, Nat, List.range.go(n, Nil{})), Nat.add(n, 0n), internal_length_range_go(n, Nil{})) : {_ == n : Nat}
  MNat.add_zero(n)

# Zipping two lists gives the length of the shorter one.
law length_zip:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) == Nat.min(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

def length_zip(a, A, xs, ys):
  match xs ys:
    case Nil{} _:
      {==}
    case h <> t Nil{}:
      {==}
    case h <> t y <> yt:
      %length_zip(a, A, t, yt) : {1n+List.length(&1, A & A, List.zip(a, A, a, A, t, yt)) == 1n+_ : Nat}
      {==}

# Appending after a cons: (x :: xs) ++ ys = x :: (xs ++ ys).
law append_cons:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -ys: List<a, A>
  {List.append(a, A, x <> xs, ys) == x <> List.append(a, A, xs, ys) : List<a, A>}

def append_cons(a, A, x, xs, ys):
  {==}

# The empty list has length zero.
law length_nil:
  for -a: Quant
  for -A: Kind(a)
  {List.length(a, A, Nil{}) == 0n : Nat}

def length_nil(a, A):
  {==}

# A cons is one longer than its tail.
law length_cons:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {List.length(a, A, x <> xs) == 1n+List.length(a, A, xs) : Nat}

def length_cons(a, A, x, xs):
  {==}

# Concatenating an append concatenates each part: concat (xss ++ yss) = concat xss ++ concat yss.
law concat_append:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for -yss: List<a, List<a, A>>
  {List.concat(a, A, List.append(a, List<a, A>, xss, yss)) == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}

def concat_append(a, A, xss, yss):
  match xss:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<a, A>, List.concat(a, A, List.append(a, List<a, A>, t, yss)), List.append(a, A, List.concat(a, A, t), List.concat(a, A, yss)), concat_append(a, A, t, yss)) : {List.append(a, A, h, _) == List.append(a, A, List.append(a, A, h, List.concat(a, A, t)), List.concat(a, A, yss)) : List<a, A>}
      Equal.sym(List<a, A>, List.append(a, A, List.append(a, A, h, List.concat(a, A, t)), List.concat(a, A, yss)), List.append(a, A, h, List.append(a, A, List.concat(a, A, t), List.concat(a, A, yss))), append_assoc(a, A, h, List.concat(a, A, t), List.concat(a, A, yss)))

# A left fold over an append folds the second part from the fold of the first.
law foldl_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) : B}

def foldl_append(a, A, B, f, xs, ys, z):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      foldl_append(~a, ~A, ~B, ~f, t, ys, f(z, h))

def internal_map_reverse_go(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>, acc: List<A>) -> {List.map(~A, ~B, ~f, List.reverse.go(&1, A, xs, acc)) == List.reverse.go(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, acc)) : List<B>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_map_reverse_go(~A, ~B, ~f, t, h <> acc)

# Mapping commutes with reversing: map f (reverse xs) = reverse (map f xs).
law map_reverse:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) == List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) : List<B>}

def map_reverse(A, B, f, xs):
  internal_map_reverse_go(~A, ~B, ~f, xs, Nil{})

# Proofs about all, any and find unfold their cons case only through these (PLAN F39).
def internal_all_cons(~a: Quant, ~A: Kind(a), ~f: A -> Bool, h: A, t: List<a, A>) -> {Bool.and(f(h), List.all(~a, ~A, ~f, t)) == List.all(~a, ~A, ~f, h <> t) : Bool}:
  {==}

def internal_any_cons(~a: Quant, ~A: Kind(a), ~f: A -> Bool, h: A, t: List<a, A>) -> {Bool.or(f(h), List.any(~a, ~A, ~f, t)) == List.any(~a, ~A, ~f, h <> t) : Bool}:
  {==}

def internal_find_cons(~A: Data, ~f: A -> Bool, +h: A, t: List<&2, A>) -> {List.find.put(A, h, List.find(~A, ~f, t), f(h)) == List.find(~A, ~f, h <> t) : Maybe<&2, A>}:
  {==}

def internal_contains_cons(~A: Data, ~eq: A -> A -> Bool, h: A, t: List<&2, A>, +x: A) -> {Bool.or(eq(h, x), List.contains(~A, ~eq, t, x)) == List.contains(~A, ~eq, h <> t, x) : Bool}:
  {==}

# All over an append is all over each part, joined by and.
law all_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) : Bool}

def all_append(a, A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.all(~a, ~A, ~f, List.append(a, A, t, ys)), Bool.and(List.all(~a, ~A, ~f, t), List.all(~a, ~A, ~f, ys)), all_append(~a, ~A, ~f, t, ys)) : {Bool.and(f(h), _) == Bool.and(Bool.and(f(h), List.all(~a, ~A, ~f, t)), List.all(~a, ~A, ~f, ys)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(f(h), List.all(~a, ~A, ~f, t)), List.all(~a, ~A, ~f, ys)), Bool.and(f(h), Bool.and(List.all(~a, ~A, ~f, t), List.all(~a, ~A, ~f, ys))), MBool.and_assoc(f(h), List.all(~a, ~A, ~f, t), List.all(~a, ~A, ~f, ys)))

# Any over an append is any over each part, joined by or.
law any_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) : Bool}

def any_append(a, A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.any(~a, ~A, ~f, List.append(a, A, t, ys)), Bool.or(List.any(~a, ~A, ~f, t), List.any(~a, ~A, ~f, ys)), any_append(~a, ~A, ~f, t, ys)) : {Bool.or(f(h), _) == Bool.or(Bool.or(f(h), List.any(~a, ~A, ~f, t)), List.any(~a, ~A, ~f, ys)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(f(h), List.any(~a, ~A, ~f, t)), List.any(~a, ~A, ~f, ys)), Bool.or(f(h), Bool.or(List.any(~a, ~A, ~f, t), List.any(~a, ~A, ~f, ys))), MBool.or_assoc(f(h), List.any(~a, ~A, ~f, t), List.any(~a, ~A, ~f, ys)))

def internal_filter_put_append(-A: Data, h: A, r: List<&2, A>, s: List<&2, A>, b: Bool) -> {List.append(&2, A, List.filter.put(A, h, r, b), s) == List.filter.put(A, h, List.append(&2, A, r, s), b) : List<&2, A>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# Filtering an append filters each part.
law filter_append:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.filter(~A, ~f, List.append(&2, A, xs, ys)) == List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) : List<&2, A>}

def filter_append(A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +ys = ys
      +t = t
      %Equal.sym(List<&2, A>, List.filter(~A, ~f, List.append(&2, A, t, ys)), List.append(&2, A, List.filter(~A, ~f, t), List.filter(~A, ~f, ys)), filter_append(~A, ~f, t, ys)) : {List.filter.put(A, h, _, f(h)) == List.append(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h)), List.filter(~A, ~f, ys)) : List<&2, A>}
      Equal.sym(List<&2, A>, List.append(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h)), List.filter(~A, ~f, ys)), List.filter.put(A, h, List.append(&2, A, List.filter(~A, ~f, t), List.filter(~A, ~f, ys)), f(h)), internal_filter_put_append(A, h, List.filter(~A, ~f, t), List.filter(~A, ~f, ys), f(h)))

# An append contains x iff either part does.
law contains_append:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for -ys: List<&2, A>
  for +x: A
  {List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) == Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) : Bool}

def contains_append(A, eq, xs, ys, x):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.contains(~A, ~eq, List.append(&2, A, t, ys), x), Bool.or(List.contains(~A, ~eq, t, x), List.contains(~A, ~eq, ys, x)), contains_append(~A, ~eq, t, ys, x)) : {Bool.or(eq(h, x), _) == Bool.or(Bool.or(eq(h, x), List.contains(~A, ~eq, t, x)), List.contains(~A, ~eq, ys, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(eq(h, x), List.contains(~A, ~eq, t, x)), List.contains(~A, ~eq, ys, x)), Bool.or(eq(h, x), Bool.or(List.contains(~A, ~eq, t, x), List.contains(~A, ~eq, ys, x))), MBool.or_assoc(eq(h, x), List.contains(~A, ~eq, t, x), List.contains(~A, ~eq, ys, x)))

def internal_length_filter_put_le(-A: Data, h: A, r: List<&2, A>, b: Bool) -> {Nat.is_le(List.length(&2, A, List.filter.put(A, h, r, b)), 1n+List.length(&2, A, r)) == True{} : Bool}:
  match b:
    case False{}:
      MNat.le_succ(List.length(&2, A, r))
    case True{}:
      MNat.le_refl(1n+List.length(&2, A, r))

# Filtering never makes a list longer.
law length_filter_le:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) == True{} : Bool}

def length_filter_le(A, f, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +t = t
      MNat.le_trans(List.length(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h))), 1n+List.length(&2, A, List.filter(~A, ~f, t)), 1n+List.length(&2, A, t), internal_length_filter_put_le(A, h, List.filter(~A, ~f, t), f(h)), MNat.succ_le_succ(List.length(&2, A, List.filter(~A, ~f, t)), List.length(&2, A, t), length_filter_le(~A, ~f, t)))

# Membership in a list, as a reusable proposition.
def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}

# A list is sorted by a comparator when every adjacent pair is in order.
def sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}

def internal_or_of_right(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      hb
    case True{}:
      {==}

def internal_or_of_or(a: Bool, -b: Bool, -c: Bool, h: {Bool.or(a, b) == True{} : Bool}, k: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case False{}:
      k(h)
    case True{}:
      {==}

def internal_and_left(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MNat.internal_false_ne_true(h))
    case True{}:
      {==}

def internal_and_right(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, MNat.internal_false_ne_true(h))
    case True{}:
      h

def internal_mem_append_left(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +x: Nat, h: {List.contains(~Nat, ~Nat.is_eq, xs, x) == True{} : Bool}) -> {List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({List.contains(~Nat, ~Nat.is_eq, ys, x) == True{} : Bool}, MNat.internal_false_ne_true(h))
    case hd <> tl:
      %internal_contains_cons(~Nat, ~Nat.is_eq, hd, List.append(&2, Nat, tl, ys), x) : {_ == True{} : Bool}
      internal_or_of_or(Nat.is_eq(hd, x), List.contains(~Nat, ~Nat.is_eq, tl, x), List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, tl, ys), x), Equal.trans(Bool, Bool.or(Nat.is_eq(hd, x), List.contains(~Nat, ~Nat.is_eq, tl, x)), List.contains(~Nat, ~Nat.is_eq, hd <> tl, x), True{}, internal_contains_cons(~Nat, ~Nat.is_eq, hd, tl, x), h), internal_mem_append_left(tl, ys, x))

def internal_mem_append_right(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +x: Nat, h: {List.contains(~Nat, ~Nat.is_eq, ys, x) == True{} : Bool}) -> {List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case hd <> tl:
      %internal_contains_cons(~Nat, ~Nat.is_eq, hd, List.append(&2, Nat, tl, ys), x) : {_ == True{} : Bool}
      internal_or_of_right(Nat.is_eq(hd, x), List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, tl, ys), x), internal_mem_append_right(tl, ys, x, h))

# The head of a Nat list is a member of it (membership by Nat.is_eq).
law mem_cons_self:
  for x: Nat
  for -xs: List<&2, Nat>
  mem(~Nat, ~Nat.is_eq, x, x <> xs)

def mem_cons_self(x, xs):
  %Equal.sym(Bool, Nat.is_eq(x, x), True{}, MNat.is_eq_refl(x)) : {Bool.or(_, List.contains(~Nat, ~Nat.is_eq, xs, x)) == True{} : Bool}
  {==}

# A member of a Nat list stays a member when a head is prepended.
law mem_cons_of_mem:
  for x: Nat
  for y: Nat
  for -xs: List<&2, Nat>
  for h: mem(~Nat, ~Nat.is_eq, x, xs)
  mem(~Nat, ~Nat.is_eq, x, y <> xs)

def mem_cons_of_mem(x, y, xs, h):
  +x = x
  internal_or_of_right(Nat.is_eq(y, x), List.contains(~Nat, ~Nat.is_eq, xs, x), h)

# No Nat is a member of the empty list.
law not_mem_nil:
  for -x: Nat
  mem(~Nat, ~Nat.is_eq, x, Nil{}) -> Empty

def not_mem_nil(x, h):
  MNat.internal_false_ne_true(h)

# A member of xs is a member of xs ++ ys (Nat lists).
law mem_append_left:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for x: Nat
  for h: mem(~Nat, ~Nat.is_eq, x, xs)
  mem(~Nat, ~Nat.is_eq, x, List.append(&2, Nat, xs, ys))

def mem_append_left(xs, ys, x, h):
  internal_mem_append_left(xs, ys, x, h)

# A member of ys is a member of xs ++ ys (Nat lists).
law mem_append_right:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for x: Nat
  for h: mem(~Nat, ~Nat.is_eq, x, ys)
  mem(~Nat, ~Nat.is_eq, x, List.append(&2, Nat, xs, ys))

def mem_append_right(xs, ys, x, h):
  internal_mem_append_right(xs, ys, x, h)

# The empty Nat list is sorted by Nat.is_le.
law sorted_nil:
  sorted_by(~Nat, ~Nat.is_le, Nil{})

def sorted_nil():
  {==}

# A one-element Nat list is sorted by Nat.is_le.
law sorted_single:
  for -x: Nat
  sorted_by(~Nat, ~Nat.is_le, [x])

def sorted_single(x):
  {==}

# The step of sorted_by, with a literal pair head so the kernel reduces the predicate (PLAN F39).
def internal_sorted_cons_true(~A: Data, ~le: A -> A -> Bool, -x: A, -y: A, -z: List<&1, A & A>, e: {le(x, y) == True{} : Bool}) -> {List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), z) == List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), (x, y) <> z) : Bool}:
  %Equal.sym(Bool, le(x, y), True{}, e) : {List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), z) == Bool.and(_, List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), z)) : Bool}
  {==}

def internal_sorted_cons_false(~A: Data, ~le: A -> A -> Bool, -x: A, -y: A, z: List<&1, A & A>, e: {le(x, y) == False{} : Bool}) -> {False{} == List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), (x, y) <> z) : Bool}:
  %Equal.sym(Bool, le(x, y), False{}, e) : {False{} == Bool.and(_, List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), z)) : Bool}
  {==}

# A Nat list sorted by Nat.is_le stays sorted under a head that is <= the next element.
law sorted_cons_cons_intro:
  for -x: Nat
  for -y: Nat
  for -t: List<&2, Nat>
  for hxy: MNat.le(x, y)
  for hyt: sorted_by(~Nat, ~Nat.is_le, y <> t)
  sorted_by(~Nat, ~Nat.is_le, x <> y <> t)

def sorted_cons_cons_intro(x, y, t, hxy, hyt):
  %internal_sorted_cons_true(~Nat, ~Nat.is_le, x, y, List.zip(&2, Nat, &2, Nat, y <> t, t), hxy) : {_ == True{} : Bool}
  hyt

def internal_sorted_tail_step(-x: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, e: {Nat.is_le(x, y) == b : Bool}, h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t)) -> sorted_by(~Nat, ~Nat.is_le, y <> t):
  match b:
    case True{}:
      Equal.trans(Bool, List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t)), List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), (x, y) <> List.zip(&2, Nat, &2, Nat, y <> t, t)), True{}, internal_sorted_cons_true(~Nat, ~Nat.is_le, x, y, List.zip(&2, Nat, &2, Nat, y <> t, t), e), h)
    case False{}:
      Empty.absurd(sorted_by(~Nat, ~Nat.is_le, y <> t), MNat.internal_false_ne_true(Equal.trans(Bool, False{}, List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), (x, y) <> List.zip(&2, Nat, &2, Nat, y <> t, t)), True{}, internal_sorted_cons_false(~Nat, ~Nat.is_le, x, y, List.zip(&2, Nat, &2, Nat, y <> t, t), e), h)))

# The first two elements of a Nat list sorted by Nat.is_le are in order.
law sorted_cons_cons_elim_le:
  for x: Nat
  for y: Nat
  for -t: List<&2, Nat>
  for h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t)
  MNat.le(x, y)

def sorted_cons_cons_elim_le(x, y, t, h):
  internal_and_left(Nat.is_le(x, y), List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t)), h)

# The tail of a Nat list of two or more elements sorted by Nat.is_le is sorted.
law sorted_cons_cons_elim_tail:
  for x: Nat
  for y: Nat
  for -t: List<&2, Nat>
  for h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t)
  sorted_by(~Nat, ~Nat.is_le, y <> t)

def sorted_cons_cons_elim_tail(x, y, t, h):
  internal_and_right(Nat.is_le(x, y), List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t)), h)

# The tail of a nonempty Nat list sorted by Nat.is_le is sorted.
law sorted_tail:
  for x: Nat
  for xs: List<&2, Nat>
  for h: sorted_by(~Nat, ~Nat.is_le, x <> xs)
  sorted_by(~Nat, ~Nat.is_le, xs)

def sorted_tail(x, xs, h):
  match xs:
    case Nil{}:
      {==}
    case +y <> t:
      +x = x
      internal_sorted_tail_step(x, y, t, Nat.is_le(x, y), {==}, h)

# Taking the length of the first part of an append gives the first part back.
law take_left:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.take(a, A, List.append(a, A, xs, ys), List.length(a, A, xs)) == xs : List<a, A>}

def take_left(a, A, xs, ys):
  match xs:
    case Nil{}:
      take_zero(a, A, ys)
    case h <> t:
      %take_left(a, A, t, ys) : {h <> List.take(a, A, List.append(a, A, t, ys), List.length(a, A, t)) == h <> _ : List<a, A>}
      {==}

# Dropping the length of the first part of an append gives the second part.
law drop_left:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.drop(a, A, List.append(a, A, xs, ys), List.length(a, A, xs)) == ys : List<a, A>}

def drop_left(a, A, xs, ys):
  match xs:
    case Nil{}:
      drop_zero(a, A, ys)
    case h <> t:
      drop_left(a, A, t, ys)

# Taking past the first part of an append keeps it and takes the rest from the second part.
law take_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -n: Nat
  {List.take(a, A, List.append(a, A, xs, ys), Nat.add(List.length(a, A, xs), n)) == List.append(a, A, xs, List.take(a, A, ys, n)) : List<a, A>}

def take_append(a, A, xs, ys, n):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %take_append(a, A, t, ys, n) : {h <> List.take(a, A, List.append(a, A, t, ys), Nat.add(List.length(a, A, t), n)) == h <> _ : List<a, A>}
      {==}

# Dropping past the first part of an append drops the rest from the second part.
law drop_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -n: Nat
  {List.drop(a, A, List.append(a, A, xs, ys), Nat.add(List.length(a, A, xs), n)) == List.drop(a, A, ys, n) : List<a, A>}

def drop_append(a, A, xs, ys, n):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      drop_append(a, A, t, ys, n)

# Taking at most the length of the first part of an append only sees the first part.
law take_append_of_le_length:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  for n: Nat
  for h: MNat.le(n, List.length(a, A, xs))
  {List.take(a, A, List.append(a, A, xs, ys), n) == List.take(a, A, xs, n) : List<a, A>}

def take_append_of_le_length(a, A, xs, ys, n, h):
  match xs n:
    case Nil{} 0n:
      take_zero(a, A, ys)
    case Nil{} 1n+p:
      Empty.absurd({List.take(a, A, ys, 1n+p) == Nil{} : List<a, A>}, MNat.internal_false_ne_true(h))
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      %take_append_of_le_length(a, A, t, ys, p, h) : {x <> List.take(a, A, List.append(a, A, t, ys), p) == x <> _ : List<a, A>}
      {==}

# Dropping at most the length of the first part of an append drops only from the first part.
law drop_append_of_le_length:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  for n: Nat
  for h: MNat.le(n, List.length(a, A, xs))
  {List.drop(a, A, List.append(a, A, xs, ys), n) == List.append(a, A, List.drop(a, A, xs, n), ys) : List<a, A>}

def drop_append_of_le_length(a, A, xs, ys, n, h):
  match xs n:
    case Nil{} 0n:
      drop_zero(a, A, ys)
    case Nil{} 1n+p:
      Empty.absurd({List.drop(a, A, ys, 1n+p) == ys : List<a, A>}, MNat.internal_false_ne_true(h))
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      drop_append_of_le_length(a, A, t, ys, p, h)

# Mapping commutes with taking: map f (take n xs) = take n (map f xs).
law map_take:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for n: Nat
  {List.map(~A, ~B, ~f, List.take(&1, A, xs, n)) == List.take(&1, B, List.map(~A, ~B, ~f, xs), n) : List<B>}

def map_take(A, B, f, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %map_take(~A, ~B, ~f, t, p) : {f(h) <> List.map(~A, ~B, ~f, List.take(&1, A, t, p)) == f(h) <> _ : List<B>}
      {==}

# Mapping commutes with dropping: map f (drop n xs) = drop n (map f xs).
law map_drop:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for n: Nat
  {List.map(~A, ~B, ~f, List.drop(&1, A, xs, n)) == List.drop(&1, B, List.map(~A, ~B, ~f, xs), n) : List<B>}

def map_drop(A, B, f, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      map_drop(~A, ~B, ~f, t, p)

# Taking m from n copies of x gives min(m, n) copies of x.
law take_replicate:
  for -A: Data
  for n: Nat
  for m: Nat
  for -x: A
  {List.take(&2, A, List.replicate(A, n, x), m) == List.replicate(A, Nat.min(m, n), x) : List<&2, A>}

def take_replicate(A, n, m, x):
  match n m:
    case 0n _:
      %MNat.min_zero_sym(m) : {Nil{} == List.replicate(A, _, x) : List<&2, A>}
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %take_replicate(A, p, q, x) : {x <> List.take(&2, A, List.replicate(A, p, x), q) == x <> _ : List<&2, A>}
      {==}

# Dropping m from n copies of x gives n - m copies of x.
law drop_replicate:
  for -A: Data
  for n: Nat
  for m: Nat
  for -x: A
  {List.drop(&2, A, List.replicate(A, n, x), m) == List.replicate(A, Nat.sub(n, m), x) : List<&2, A>}

def drop_replicate(A, n, m, x):
  match n m:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      drop_replicate(A, p, q, x)

# Taking n elements gives at most n of them.
law length_take_le:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  MNat.le(List.length(a, A, List.take(a, A, xs, n)), n)

def length_take_le(a, A, xs, n):
  match xs n:
    case Nil{} _:
      MNat.zero_le(n)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      MNat.succ_le_succ(List.length(a, A, List.take(a, A, t, p)), p, length_take_le(a, A, t, p))

# The tail is one shorter than the list, or empty: length (tail xs) = length xs - 1.
law length_tail:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.length(a, A, List.tail(a, A, xs)) == Nat.sub(List.length(a, A, xs), 1n) : Nat}

def length_tail(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      MNat.sub_zero_sym(List.length(a, A, t))

# Mapping the identity gives the list back.
law map_id:
  for ~A: Type
  for xs: List<A>
  {List.map(~A, ~A, ~(x => x), xs) == xs : List<A>}

def map_id(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %map_id(~A, t) : {h <> List.map(~A, ~A, ~(x => x), t) == h <> _ : List<A>}
      {==}

# A right fold over a map folds with the mapped function: foldr g z (map f xs) = foldr (g . f) z xs.
law foldr_map:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C -> C
  for xs: List<A>
  for -z: C
  {List.foldr(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, xs), z) == List.foldr(~&1, ~A, ~C, ~(x => y => g(f(x), y)), xs, z) : C}

def foldr_map(A, B, C, f, g, xs, z):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %foldr_map(~A, ~B, ~C, ~f, ~g, t, z) : {g(f(h), List.foldr(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, t), z)) == g(f(h), _) : C}
      {==}

# A left fold over a map folds with the mapped function: foldl g z (map f xs) = foldl (fun acc x => g acc (f x)) z xs.
law foldl_map:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: C -> B -> C
  for xs: List<A>
  for -z: C
  {List.foldl(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, xs), z) == List.foldl(~&1, ~A, ~C, ~(x => y => g(x, f(y))), xs, z) : C}

def foldl_map(A, B, C, f, g, xs, z):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      foldl_map(~A, ~B, ~C, ~f, ~g, t, g(z, f(h)))

# Replicating m + n times appends m copies to n copies.
law replicate_add:
  for -A: Data
  for m: Nat
  for -n: Nat
  for -x: A
  {List.replicate(A, Nat.add(m, n), x) == List.append(&2, A, List.replicate(A, m, x), List.replicate(A, n, x)) : List<&2, A>}

def replicate_add(A, m, n, x):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %replicate_add(A, p, n, x) : {x <> List.replicate(A, Nat.add(p, n), x) == x <> _ : List<&2, A>}
      {==}

def internal_replicate_append_nil(-A: Data, n: Nat, -x: A) -> {List.append(&2, A, List.replicate(A, n, x), Nil{}) == List.replicate(A, n, x) : List<&2, A>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %internal_replicate_append_nil(A, p, x) : {x <> List.append(&2, A, List.replicate(A, p, x), Nil{}) == x <> _ : List<&2, A>}
      {==}

def internal_replicate_append_cons(-A: Data, n: Nat, -x: A, -acc: List<&2, A>) -> {List.append(&2, A, List.replicate(A, n, x), x <> acc) == x <> List.append(&2, A, List.replicate(A, n, x), acc) : List<&2, A>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %internal_replicate_append_cons(A, p, x, acc) : {x <> List.append(&2, A, List.replicate(A, p, x), x <> acc) == x <> _ : List<&2, A>}
      {==}

def internal_reverse_go_replicate(-A: Data, n: Nat, -x: A, -acc: List<&2, A>) -> {List.reverse.go(&2, A, List.replicate(A, n, x), acc) == List.append(&2, A, List.replicate(A, n, x), acc) : List<&2, A>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +p = p
      Equal.trans(List<&2, A>, List.reverse.go(&2, A, List.replicate(A, p, x), x <> acc), List.append(&2, A, List.replicate(A, p, x), x <> acc), x <> List.append(&2, A, List.replicate(A, p, x), acc), internal_reverse_go_replicate(A, p, x, x <> acc), internal_replicate_append_cons(A, p, x, acc))

# Reversing n copies of x gives them back.
law reverse_replicate:
  for -A: Data
  for n: Nat
  for -x: A
  {List.reverse(&2, A, List.replicate(A, n, x)) == List.replicate(A, n, x) : List<&2, A>}

def reverse_replicate(A, n, x):
  +n = n
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.replicate(A, n, x)), List.append(&2, A, List.replicate(A, n, x), Nil{}), List.replicate(A, n, x), internal_reverse_go_replicate(A, n, x, Nil{}), internal_replicate_append_nil(A, n, x))

# Filtering with an always-true predicate gives the list back.
law filter_true:
  for ~A: Data
  for xs: List<&2, A>
  {List.filter(~A, ~(x => True{}), xs) == xs : List<&2, A>}

def filter_true(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %filter_true(~A, t) : {h <> List.filter(~A, ~(x => True{}), t) == h <> _ : List<&2, A>}
      {==}

# Filtering with an always-false predicate gives the empty list.
law filter_false:
  for ~A: Data
  for xs: List<&2, A>
  {List.filter(~A, ~(x => False{}), xs) == Nil{} : List<&2, A>}

def filter_false(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      filter_false(~A, t)

def internal_filter_put_filter(~A: Data, ~p: A -> Bool, +h: A, r: List<&2, A>, b: Bool) -> {List.filter(~A, ~p, List.filter.put(A, h, r, b)) == List.filter.put(A, h, List.filter(~A, ~p, r), Bool.and(p(h), b)) : List<&2, A>}:
  match b:
    case False{}:
      %MBool.and_false_sym(p(h)) : {List.filter(~A, ~p, r) == List.filter.put(A, h, List.filter(~A, ~p, r), _) : List<&2, A>}
      {==}
    case True{}:
      %MBool.and_true_sym(p(h)) : {List.filter(~A, ~p, h <> r) == List.filter.put(A, h, List.filter(~A, ~p, r), _) : List<&2, A>}
      {==}

# Filtering twice is filtering by both predicates: filter p (filter q xs) = filter (p and q) xs.
law filter_filter:
  for ~A: Data
  for ~p: A -> Bool
  for ~q: A -> Bool
  for xs: List<&2, A>
  {List.filter(~A, ~p, List.filter(~A, ~q, xs)) == List.filter(~A, ~(+x => Bool.and(p(x), q(x))), xs) : List<&2, A>}

def filter_filter(A, p, q, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +t = t
      %filter_filter(~A, ~p, ~q, t) : {List.filter(~A, ~p, List.filter.put(A, h, List.filter(~A, ~q, t), q(h))) == List.filter.put(A, h, _, Bool.and(p(h), q(h))) : List<&2, A>}
      internal_filter_put_filter(~A, ~p, h, List.filter(~A, ~q, t), q(h))

def internal_all_filter_put(~A: Data, ~q: A -> Bool, +h: A, r: List<&2, A>, b: Bool) -> {List.all(~&2, ~A, ~q, List.filter.put(A, h, r, b)) == Bool.and(Bool.or(Bool.not(b), q(h)), List.all(~&2, ~A, ~q, r)) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.sym(Bool, Bool.and(q(h), List.all(~&2, ~A, ~q, r)), List.all(~&2, ~A, ~q, h <> r), internal_all_cons(~&2, ~A, ~q, h, r))

# All over a filter checks q only where p holds: all q (filter p xs) = all (not p or q) xs.
law all_filter:
  for ~A: Data
  for ~p: A -> Bool
  for ~q: A -> Bool
  for xs: List<&2, A>
  {List.all(~&2, ~A, ~q, List.filter(~A, ~p, xs)) == List.all(~&2, ~A, ~(+x => Bool.or(Bool.not(p(x)), q(x))), xs) : Bool}

def all_filter(A, p, q, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +t = t
      %internal_all_cons(~&2, ~A, ~(+x => Bool.or(Bool.not(p(x)), q(x))), h, t) : {List.all(~&2, ~A, ~q, List.filter.put(A, h, List.filter(~A, ~p, t), p(h))) == _ : Bool}
      %all_filter(~A, ~p, ~q, t) : {List.all(~&2, ~A, ~q, List.filter.put(A, h, List.filter(~A, ~p, t), p(h))) == Bool.and(Bool.or(Bool.not(p(h)), q(h)), _) : Bool}
      internal_all_filter_put(~A, ~q, h, List.filter(~A, ~p, t), p(h))

def internal_any_filter_put(~A: Data, ~q: A -> Bool, +h: A, r: List<&2, A>, b: Bool) -> {List.any(~&2, ~A, ~q, List.filter.put(A, h, r, b)) == Bool.or(Bool.and(b, q(h)), List.any(~&2, ~A, ~q, r)) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.sym(Bool, Bool.or(q(h), List.any(~&2, ~A, ~q, r)), List.any(~&2, ~A, ~q, h <> r), internal_any_cons(~&2, ~A, ~q, h, r))

# Any over a filter looks for q only where p holds: any q (filter p xs) = any (p and q) xs.
law any_filter:
  for ~A: Data
  for ~p: A -> Bool
  for ~q: A -> Bool
  for xs: List<&2, A>
  {List.any(~&2, ~A, ~q, List.filter(~A, ~p, xs)) == List.any(~&2, ~A, ~(+x => Bool.and(p(x), q(x))), xs) : Bool}

def any_filter(A, p, q, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +t = t
      %internal_any_cons(~&2, ~A, ~(+x => Bool.and(p(x), q(x))), h, t) : {List.any(~&2, ~A, ~q, List.filter.put(A, h, List.filter(~A, ~p, t), p(h))) == _ : Bool}
      %any_filter(~A, ~p, ~q, t) : {List.any(~&2, ~A, ~q, List.filter.put(A, h, List.filter(~A, ~p, t), p(h))) == Bool.or(Bool.and(p(h), q(h)), _) : Bool}
      internal_any_filter_put(~A, ~q, h, List.filter(~A, ~p, t), p(h))

# The proof of all_map unfolds List.all, so it lives here with the other unfolding lemmas (PLAN F39).
def internal_all_map(~A: Type, ~B: Type, ~f: A -> B, ~p: B -> Bool, xs: List<A>) -> {List.all(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) == List.all(~&1, ~A, ~(x => p(f(x))), xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %internal_all_map(~A, ~B, ~f, ~p, t) : {Bool.and(p(f(h)), List.all(~&1, ~B, ~p, List.map(~A, ~B, ~f, t))) == Bool.and(p(f(h)), _) : Bool}
      {==}

def internal_any_map(~A: Type, ~B: Type, ~f: A -> B, ~p: B -> Bool, xs: List<A>) -> {List.any(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) == List.any(~&1, ~A, ~(x => p(f(x))), xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %internal_any_map(~A, ~B, ~f, ~p, t) : {Bool.or(p(f(h)), List.any(~&1, ~B, ~p, List.map(~A, ~B, ~f, t))) == Bool.or(p(f(h)), _) : Bool}
      {==}

# All over a map checks the composed predicate: all p (map f xs) = all (p . f) xs.
law all_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for ~p: B -> Bool
  for xs: List<A>
  {List.all(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) == List.all(~&1, ~A, ~(x => p(f(x))), xs) : Bool}

def all_map(A, B, f, p, xs):
  internal_all_map(~A, ~B, ~f, ~p, xs)

# Any over a map checks the composed predicate: any p (map f xs) = any (p . f) xs.
law any_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for ~p: B -> Bool
  for xs: List<A>
  {List.any(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) == List.any(~&1, ~A, ~(x => p(f(x))), xs) : Bool}

def any_map(A, B, f, p, xs):
  internal_any_map(~A, ~B, ~f, ~p, xs)

def internal_all_reverse_go(~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>, -acc: List<a, A>, c: Bool, e: {List.all(~a, ~A, ~f, acc) == c : Bool}) -> {List.all(~a, ~A, ~f, List.reverse.go(a, A, xs, acc)) == Bool.and(c, List.all(~a, ~A, ~f, xs)) : Bool}:
  match xs c:
    case Nil{} True{}:
      e
    case Nil{} False{}:
      e
    case h <> t True{}:
      +v = f(h)
      internal_all_reverse_go(~a, ~A, ~f, t, h <> acc, v, Equal.trans(Bool, Bool.and(v, List.all(~a, ~A, ~f, acc)), Bool.and(v, True{}), v, Equal.cong(Bool, Bool, k => Bool.and(v, k), List.all(~a, ~A, ~f, acc), True{}, e), MBool.and_true(v)))
    case h <> t False{}:
      internal_all_reverse_go(~a, ~A, ~f, t, h <> acc, False{}, Equal.trans(Bool, Bool.and(f(h), List.all(~a, ~A, ~f, acc)), Bool.and(f(h), False{}), False{}, Equal.cong(Bool, Bool, k => Bool.and(f(h), k), List.all(~a, ~A, ~f, acc), False{}, e), MBool.and_false(f(h))))

# Reversing does not change whether all elements satisfy a predicate.
law all_reverse:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {List.all(~a, ~A, ~f, List.reverse(a, A, xs)) == List.all(~a, ~A, ~f, xs) : Bool}

def all_reverse(a, A, f, xs):
  internal_all_reverse_go(~a, ~A, ~f, xs, Nil{}, True{}, {==})

def internal_any_reverse_go(~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>, -acc: List<a, A>, c: Bool, e: {List.any(~a, ~A, ~f, acc) == c : Bool}) -> {List.any(~a, ~A, ~f, List.reverse.go(a, A, xs, acc)) == Bool.or(c, List.any(~a, ~A, ~f, xs)) : Bool}:
  match xs c:
    case Nil{} True{}:
      e
    case Nil{} False{}:
      e
    case h <> t True{}:
      internal_any_reverse_go(~a, ~A, ~f, t, h <> acc, True{}, Equal.trans(Bool, Bool.or(f(h), List.any(~a, ~A, ~f, acc)), Bool.or(f(h), True{}), True{}, Equal.cong(Bool, Bool, k => Bool.or(f(h), k), List.any(~a, ~A, ~f, acc), True{}, e), MBool.or_true(f(h))))
    case h <> t False{}:
      +v = f(h)
      internal_any_reverse_go(~a, ~A, ~f, t, h <> acc, v, Equal.trans(Bool, Bool.or(v, List.any(~a, ~A, ~f, acc)), Bool.or(v, False{}), v, Equal.cong(Bool, Bool, k => Bool.or(v, k), List.any(~a, ~A, ~f, acc), False{}, e), MBool.or_false(v)))

# Reversing does not change whether some element satisfies a predicate.
law any_reverse:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {List.any(~a, ~A, ~f, List.reverse(a, A, xs)) == List.any(~a, ~A, ~f, xs) : Bool}

def any_reverse(a, A, f, xs):
  internal_any_reverse_go(~a, ~A, ~f, xs, Nil{}, False{}, {==})

def internal_contains_reverse_go(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +acc: List<&2, A>, +x: A, c: Bool, e: {List.contains(~A, ~eq, acc, x) == c : Bool}) -> {List.contains(~A, ~eq, List.reverse.go(&2, A, xs, acc), x) == Bool.or(c, List.contains(~A, ~eq, xs, x)) : Bool}:
  match xs c:
    case Nil{} True{}:
      e
    case Nil{} False{}:
      e
    case +h <> t True{}:
      internal_contains_reverse_go(~A, ~eq, t, h <> acc, x, True{}, Equal.trans(Bool, List.contains(~A, ~eq, h <> acc, x), Bool.or(eq(h, x), List.contains(~A, ~eq, acc, x)), True{}, Equal.sym(Bool, Bool.or(eq(h, x), List.contains(~A, ~eq, acc, x)), List.contains(~A, ~eq, h <> acc, x), internal_contains_cons(~A, ~eq, h, acc, x)), Equal.trans(Bool, Bool.or(eq(h, x), List.contains(~A, ~eq, acc, x)), Bool.or(eq(h, x), True{}), True{}, Equal.cong(Bool, Bool, k => Bool.or(eq(h, x), k), List.contains(~A, ~eq, acc, x), True{}, e), MBool.or_true(eq(h, x)))))
    case +h <> +t False{}:
      +v = eq(h, x)
      %internal_contains_cons(~A, ~eq, h, t, x) : {List.contains(~A, ~eq, List.reverse.go(&2, A, t, h <> acc), x) == _ : Bool}
      internal_contains_reverse_go(~A, ~eq, t, h <> acc, x, v, Equal.trans(Bool, List.contains(~A, ~eq, h <> acc, x), Bool.or(v, List.contains(~A, ~eq, acc, x)), v, Equal.sym(Bool, Bool.or(eq(h, x), List.contains(~A, ~eq, acc, x)), List.contains(~A, ~eq, h <> acc, x), internal_contains_cons(~A, ~eq, h, acc, x)), Equal.trans(Bool, Bool.or(v, List.contains(~A, ~eq, acc, x)), Bool.or(v, False{}), v, Equal.cong(Bool, Bool, k => Bool.or(v, k), List.contains(~A, ~eq, acc, x), False{}, e), MBool.or_false(v))))

# Reversing does not change whether a list contains x.
law contains_reverse:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for +x: A
  {List.contains(~A, ~eq, List.reverse(&2, A, xs), x) == List.contains(~A, ~eq, xs, x) : Bool}

def contains_reverse(A, eq, xs, x):
  internal_contains_reverse_go(~A, ~eq, xs, Nil{}, x, False{}, {==})

# Zipping the empty list with anything gives the empty list.
law zip_nil_left:
  for -a: Quant
  for -A: Kind(a)
  for -b: Quant
  for -B: Kind(b)
  for -ys: List<b, B>
  {List.zip(a, A, b, B, Nil{}, ys) == Nil{} : List<&1, A & B>}

def zip_nil_left(a, A, b, B, ys):
  {==}

# Zipping anything with the empty list gives the empty list.
law zip_nil_right:
  for -a: Quant
  for -A: Kind(a)
  for -b: Quant
  for -B: Kind(b)
  for xs: List<a, A>
  {List.zip(a, A, b, B, xs, Nil{}) == Nil{} : List<&1, A & B>}

def zip_nil_right(a, A, b, B, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# The head of a cons is its first element.
law head_cons:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {List.head(a, A, x <> xs) == Some{x} : Maybe<a, A>}

def head_cons(a, A, x, xs):
  {==}

# The head of an append is the head of the first part, or else of the second.
law head_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.head(a, A, List.append(a, A, xs, ys)) == Maybe.or(a, A, List.head(a, A, xs), List.head(a, A, ys)) : Maybe<a, A>}

def head_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# The head of a map is the mapped head.
law head_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.head(&1, B, List.map(~A, ~B, ~f, xs)) == Maybe.map(&1, A, B, f, List.head(&1, A, xs)) : Maybe<&1, B>}

def head_map(A, B, f, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# The tail of a map is the map of the tail.
law tail_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.tail(&1, B, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~B, ~f, List.tail(&1, A, xs)) : List<B>}

def tail_map(A, B, f, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# The element at index zero of a cons is its head.
law get_cons_zero:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {List.get(a, A, x <> xs, 0n) == Some{x} : Maybe<a, A>}

def get_cons_zero(a, A, x, xs):
  {==}

# The element at index n + 1 of a cons is the element at index n of its tail.
law get_cons_succ:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -n: Nat
  {List.get(a, A, x <> xs, 1n+n) == List.get(a, A, xs, n) : Maybe<a, A>}

def get_cons_succ(a, A, x, xs, n):
  {==}

# Indexing a map is mapping the indexed element.
law get_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for n: Nat
  {List.get(&1, B, List.map(~A, ~B, ~f, xs), n) == Maybe.map(&1, A, B, f, List.get(&1, A, xs, n)) : Maybe<&1, B>}

def get_map(A, B, f, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      get_map(~A, ~B, ~f, t, p)

# Setting an element does not change the length.
law length_set:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -x: A
  {List.length(a, A, List.set(a, A, xs, n, x)) == List.length(a, A, xs) : Nat}

def length_set(a, A, xs, n, x):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %length_set(a, A, t, p, x) : {1n+List.length(a, A, List.set(a, A, t, p, x)) == 1n+_ : Nat}
      {==}

# Reading the index just set gives the new value wherever the index is in range.
law get_set_self:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -x: A
  {List.get(a, A, List.set(a, A, xs, n, x), n) == Maybe.map(a, A, A, y => x, List.get(a, A, xs, n)) : Maybe<a, A>}

def get_set_self(a, A, xs, n, x):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      get_set_self(a, A, t, p, x)

def internal_last_go_append_singleton(a, -A: Kind(a), ys: List<a, A>, -h: A, -x: A) -> {List.last.go(a, A, List.append(a, A, ys, [x]), h) == x : A}:
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      internal_last_go_append_singleton(a, A, t, y, x)

# The last element of xs ++ [x] is x.
law last_append_singleton:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -x: A
  {List.last(a, A, List.append(a, A, xs, [x])) == Some{x} : Maybe<a, A>}

def last_append_singleton(a, A, xs, x):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %internal_last_go_append_singleton(a, A, t, h, x) : {Some{List.last.go(a, A, List.append(a, A, t, [x]), h)} == Some{_} : Maybe<a, A>}
      {==}

def internal_head_reverse_go(a, -A: Kind(a), xs: List<a, A>, -h: A, -acc: List<a, A>) -> {List.head(a, A, List.reverse.go(a, A, xs, h <> acc)) == Some{List.last.go(a, A, xs, h)} : Maybe<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case y <> t:
      internal_head_reverse_go(a, A, t, y, h <> acc)

# The head of the reverse is the last element.
law head_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.head(a, A, List.reverse(a, A, xs)) == List.last(a, A, xs) : Maybe<a, A>}

def head_reverse(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_head_reverse_go(a, A, t, h, Nil{})

def internal_last_reverse_go(a, -A: Kind(a), xs: List<a, A>, -h: A, -acc: List<a, A>) -> {List.last(a, A, List.reverse.go(a, A, xs, h <> acc)) == Some{List.last.go(a, A, acc, h)} : Maybe<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case y <> t:
      internal_last_reverse_go(a, A, t, y, h <> acc)

# The last element of the reverse is the head.
law last_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.last(a, A, List.reverse(a, A, xs)) == List.head(a, A, xs) : Maybe<a, A>}

def last_reverse(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_last_reverse_go(a, A, t, h, Nil{})

# A list is empty exactly when its length is zero.
law is_empty_iff_length_eq_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.is_empty(a, A, xs) == Nat.is_eq(List.length(a, A, xs), 0n) : Bool}

def is_empty_iff_length_eq_zero(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# An append is empty exactly when both parts are.
law is_empty_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.is_empty(a, A, List.append(a, A, xs, ys)) == Bool.and(List.is_empty(a, A, xs), List.is_empty(a, A, ys)) : Bool}

def is_empty_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def internal_is_empty_reverse_go(a, -A: Kind(a), xs: List<a, A>, -h: A, -acc: List<a, A>) -> {List.is_empty(a, A, List.reverse.go(a, A, xs, h <> acc)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> t:
      internal_is_empty_reverse_go(a, A, t, y, h <> acc)

# The reverse is empty exactly when the list is.
law is_empty_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.is_empty(a, A, List.reverse(a, A, xs)) == List.is_empty(a, A, xs) : Bool}

def is_empty_reverse(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_is_empty_reverse_go(a, A, t, h, Nil{})

# A map is empty exactly when the list is.
law is_empty_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.is_empty(&1, B, List.map(~A, ~B, ~f, xs)) == List.is_empty(&1, A, xs) : Bool}

def is_empty_map(A, B, f, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def internal_reverse_filter_put(-A: Data, -h: A, r: List<&2, A>, b: Bool) -> {List.append(&2, A, List.reverse(&2, A, r), List.filter.put(A, h, Nil{}, b)) == List.reverse(&2, A, List.filter.put(A, h, r, b)) : List<&2, A>}:
  match b:
    case False{}:
      append_nil(&2, A, List.reverse(&2, A, r))
    case True{}:
      Equal.sym(List<&2, A>, List.reverse.go(&2, A, r, [h]), List.append(&2, A, List.reverse(&2, A, r), [h]), reverse_go_spec(&2, A, r, [h]))

# Filtering commutes with reversing: filter p (reverse xs) = reverse (filter p xs).
law filter_reverse:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {List.filter(~A, ~f, List.reverse(&2, A, xs)) == List.reverse(&2, A, List.filter(~A, ~f, xs)) : List<&2, A>}

def filter_reverse(A, f, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +t = t
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, t, [h]), List.append(&2, A, List.reverse(&2, A, t), [h]), reverse_go_spec(&2, A, t, [h])) : {List.filter(~A, ~f, _) == List.reverse(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h))) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.filter(~A, ~f, List.append(&2, A, List.reverse(&2, A, t), [h])), List.append(&2, A, List.filter(~A, ~f, List.reverse(&2, A, t)), List.filter(~A, ~f, [h])), filter_append(~A, ~f, List.reverse(&2, A, t), [h])) : {_ == List.reverse(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h))) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.filter(~A, ~f, List.reverse(&2, A, t)), List.reverse(&2, A, List.filter(~A, ~f, t)), filter_reverse(~A, ~f, t)) : {List.append(&2, A, _, List.filter(~A, ~f, [h])) == List.reverse(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h))) : List<&2, A>}
      internal_reverse_filter_put(A, h, List.filter(~A, ~f, t), f(h))

# Folding cons from the right, starting from the empty list, rebuilds the list.
law foldr_cons_nil:
  for ~a: Quant
  for ~A: Kind(a)
  for xs: List<a, A>
  {List.foldr(~a, ~A, ~List<a, A>, ~(x => acc => x <> acc), xs, Nil{}) == xs : List<a, A>}

def foldr_cons_nil(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %foldr_cons_nil(~a, ~A, t) : {h <> List.foldr(~a, ~A, ~List<a, A>, ~(x => acc => x <> acc), t, Nil{}) == h <> _ : List<a, A>}
      {==}

def internal_foldl_reverse_go(~a: Quant, ~A: Kind(a), ~B: Type, ~f: B -> A -> B, xs: List<a, A>, -acc: List<a, A>, -z: B) -> {List.foldl(~a, ~A, ~B, ~f, List.reverse.go(a, A, xs, acc), z) == List.foldl(~a, ~A, ~B, ~f, acc, List.foldr(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z)) : B}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_foldl_reverse_go(~a, ~A, ~B, ~f, t, h <> acc, z)

# A left fold over the reverse is a right fold with the arguments flipped.
law foldl_reverse:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for -z: B
  {List.foldl(~a, ~A, ~B, ~f, List.reverse(a, A, xs), z) == List.foldr(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z) : B}

def foldl_reverse(a, A, B, f, xs, z):
  internal_foldl_reverse_go(~a, ~A, ~B, ~f, xs, Nil{}, z)

def internal_foldr_reverse_go(~a: Quant, ~A: Kind(a), ~B: Type, ~f: A -> B -> B, xs: List<a, A>, -acc: List<a, A>, -z: B) -> {List.foldr(~a, ~A, ~B, ~f, List.reverse.go(a, A, xs, acc), z) == List.foldl(~a, ~A, ~B, ~(x => y => f(y, x)), xs, List.foldr(~a, ~A, ~B, ~f, acc, z)) : B}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_foldr_reverse_go(~a, ~A, ~B, ~f, t, h <> acc, z)

# A right fold over the reverse is a left fold with the arguments flipped.
law foldr_reverse:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: A -> B -> B
  for xs: List<a, A>
  for -z: B
  {List.foldr(~a, ~A, ~B, ~f, List.reverse(a, A, xs), z) == List.foldl(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z) : B}

def foldr_reverse(a, A, B, f, xs, z):
  internal_foldr_reverse_go(~a, ~A, ~B, ~f, xs, Nil{}, z)

def internal_range_go_append(+n: Nat, -ys: List<&2, Nat>, -acc: List<&2, Nat>) -> {List.range.go(n, List.append(&2, Nat, ys, acc)) == List.append(&2, Nat, List.range.go(n, ys), acc) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      internal_range_go_append(p, p <> ys, acc)

# Range(n + 1) is range(n) followed by n.
law range_succ:
  for n: Nat
  {List.range(1n+n) == List.append(&2, Nat, List.range(n), [n]) : List<&2, Nat>}

def range_succ(n):
  +n = n
  internal_range_go_append(n, Nil{}, [n])

def internal_find_put_or(-A: Data, h: A, r: Maybe<&2, A>, -s: Maybe<&2, A>, b: Bool) -> {Maybe.or(&2, A, List.find.put(A, h, r, b), s) == List.find.put(A, h, Maybe.or(&2, A, r, s), b) : Maybe<&2, A>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# Finding in an append finds in the first part, or else in the second.
law find_append:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.find(~A, ~f, List.append(&2, A, xs, ys)) == Maybe.or(&2, A, List.find(~A, ~f, xs), List.find(~A, ~f, ys)) : Maybe<&2, A>}

def find_append(A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +ys = ys
      +t = t
      %internal_find_cons(~A, ~f, h, List.append(&2, A, t, ys)) : {_ == Maybe.or(&2, A, List.find(~A, ~f, h <> t), List.find(~A, ~f, ys)) : Maybe<&2, A>}
      %internal_find_cons(~A, ~f, h, t) : {List.find.put(A, h, List.find(~A, ~f, List.append(&2, A, t, ys)), f(h)) == Maybe.or(&2, A, _, List.find(~A, ~f, ys)) : Maybe<&2, A>}
      %Equal.sym(Maybe<&2, A>, List.find(~A, ~f, List.append(&2, A, t, ys)), Maybe.or(&2, A, List.find(~A, ~f, t), List.find(~A, ~f, ys)), find_append(~A, ~f, t, ys)) : {List.find.put(A, h, _, f(h)) == Maybe.or(&2, A, List.find.put(A, h, List.find(~A, ~f, t), f(h)), List.find(~A, ~f, ys)) : Maybe<&2, A>}
      Equal.sym(Maybe<&2, A>, Maybe.or(&2, A, List.find.put(A, h, List.find(~A, ~f, t), f(h)), List.find(~A, ~f, ys)), List.find.put(A, h, Maybe.or(&2, A, List.find(~A, ~f, t), List.find(~A, ~f, ys)), f(h)), internal_find_put_or(A, h, List.find(~A, ~f, t), List.find(~A, ~f, ys), f(h)))

def internal_and_not_eq_not_or_not(b: Bool, -s: Bool) -> {Bool.and(b, Bool.not(s)) == Bool.not(Bool.or(Bool.not(b), s)) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_all_eq_not_any_not(~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>) -> {List.all(~a, ~A, ~f, xs) == Bool.not(List.any(~a, ~A, ~(x => Bool.not(f(x))), xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.all(~a, ~A, ~f, t), Bool.not(List.any(~a, ~A, ~(x => Bool.not(f(x))), t)), internal_all_eq_not_any_not(~a, ~A, ~f, t)) : {Bool.and(f(h), _) == Bool.not(Bool.or(Bool.not(f(h)), List.any(~a, ~A, ~(x => Bool.not(f(x))), t))) : Bool}
      internal_and_not_eq_not_or_not(f(h), List.any(~a, ~A, ~(x => Bool.not(f(x))), t))

# All elements satisfy f exactly when no element fails it.
law all_eq_not_any_not:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {List.all(~a, ~A, ~f, xs) == Bool.not(List.any(~a, ~A, ~(x => Bool.not(f(x))), xs)) : Bool}

def all_eq_not_any_not(a, A, f, xs):
  internal_all_eq_not_any_not(~a, ~A, ~f, xs)

def internal_or_not_eq_not_and_not(b: Bool, -s: Bool) -> {Bool.or(b, Bool.not(s)) == Bool.not(Bool.and(Bool.not(b), s)) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_any_eq_not_all_not(~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>) -> {List.any(~a, ~A, ~f, xs) == Bool.not(List.all(~a, ~A, ~(x => Bool.not(f(x))), xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.any(~a, ~A, ~f, t), Bool.not(List.all(~a, ~A, ~(x => Bool.not(f(x))), t)), internal_any_eq_not_all_not(~a, ~A, ~f, t)) : {Bool.or(f(h), _) == Bool.not(Bool.and(Bool.not(f(h)), List.all(~a, ~A, ~(x => Bool.not(f(x))), t))) : Bool}
      internal_or_not_eq_not_and_not(f(h), List.all(~a, ~A, ~(x => Bool.not(f(x))), t))

# Some element satisfies f exactly when not all elements fail it.
law any_eq_not_all_not:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {List.any(~a, ~A, ~f, xs) == Bool.not(List.all(~a, ~A, ~(x => Bool.not(f(x))), xs)) : Bool}

def any_eq_not_all_not(a, A, f, xs):
  internal_any_eq_not_all_not(~a, ~A, ~f, xs)

# A one-element list has length one.
law length_singleton:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  {List.length(a, A, [x]) == 1n : Nat}

def length_singleton(a, A, x):
  {==}

# Reversing a cons puts its head last: reverse (x :: xs) = reverse xs ++ [x].
law reverse_cons:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for xs: List<a, A>
  {List.reverse(a, A, x <> xs) == List.append(a, A, List.reverse(a, A, xs), [x]) : List<a, A>}

def reverse_cons(a, A, x, xs):
  reverse_go_spec(a, A, xs, [x])

# Taking n + 1 elements of a cons keeps its head and takes n from its tail.
law take_succ:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -n: Nat
  {List.take(a, A, x <> xs, 1n+n) == x <> List.take(a, A, xs, n) : List<a, A>}

def take_succ(a, A, x, xs, n):
  {==}

# Dropping n + 1 elements of a cons drops its head and n from its tail.
law drop_succ:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -n: Nat
  {List.drop(a, A, x <> xs, 1n+n) == List.drop(a, A, xs, n) : List<a, A>}

def drop_succ(a, A, x, xs, n):
  {==}

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# The empty list is a right identity for append: xs ++ [] = xs, reversed to rewrite toward the simple side.
law append_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.append(a, A, xs, Nil{}) : List<a, A>}

def append_nil_sym(a, A, xs):
  Equal.sym(List<a, A>, List.append(a, A, xs, Nil{}), xs, append_nil(a, A, xs))

# The empty list is a left identity for append: [] ++ xs = xs, reversed to rewrite toward the simple side.
law nil_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for -xs: List<a, A>
  {xs == List.append(a, A, Nil{}, xs) : List<a, A>}

def nil_append_sym(a, A, xs):
  Equal.sym(List<a, A>, List.append(a, A, Nil{}, xs), xs, nil_append(a, A, xs))

# Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs), reversed to rewrite toward the simple side.
law append_assoc_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -zs: List<a, A>
  {List.append(a, A, xs, List.append(a, A, ys, zs)) == List.append(a, A, List.append(a, A, xs, ys), zs) : List<a, A>}

def append_assoc_sym(a, A, xs, ys, zs):
  Equal.sym(List<a, A>, List.append(a, A, List.append(a, A, xs, ys), zs), List.append(a, A, xs, List.append(a, A, ys, zs)), append_assoc(a, A, xs, ys, zs))

# The length of an append is the sum of the lengths, reversed to rewrite toward the simple side.
law length_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {Nat.add(List.length(a, A, xs), List.length(a, A, ys)) == List.length(a, A, List.append(a, A, xs, ys)) : Nat}

def length_append_sym(a, A, xs, ys):
  Equal.sym(Nat, List.length(a, A, List.append(a, A, xs, ys)), Nat.add(List.length(a, A, xs), List.length(a, A, ys)), length_append(a, A, xs, ys))

# The reverse accumulator loop appends the reversed list to the accumulator, reversed to rewrite toward the simple side.
law reverse_go_spec_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -acc: List<a, A>
  {List.append(a, A, List.reverse(a, A, xs), acc) == List.reverse.go(a, A, xs, acc) : List<a, A>}

def reverse_go_spec_sym(a, A, xs, acc):
  Equal.sym(List<a, A>, List.reverse.go(a, A, xs, acc), List.append(a, A, List.reverse(a, A, xs), acc), reverse_go_spec(a, A, xs, acc))

# Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs, reversed to rewrite toward the simple side.
law reverse_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) == List.reverse(a, A, List.append(a, A, xs, ys)) : List<a, A>}

def reverse_append_sym(a, A, xs, ys):
  Equal.sym(List<a, A>, List.reverse(a, A, List.append(a, A, xs, ys)), List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)), reverse_append(a, A, xs, ys))

# Reversing twice gives the list back, reversed to rewrite toward the simple side.
law reverse_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.reverse(a, A, List.reverse(a, A, xs)) : List<a, A>}

def reverse_reverse_sym(a, A, xs):
  Equal.sym(List<a, A>, List.reverse(a, A, List.reverse(a, A, xs)), xs, reverse_reverse(a, A, xs))

# Reversing preserves the length, reversed to rewrite toward the simple side.
law length_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.length(a, A, xs) == List.length(a, A, List.reverse(a, A, xs)) : Nat}

def length_reverse_sym(a, A, xs):
  Equal.sym(Nat, List.length(a, A, List.reverse(a, A, xs)), List.length(a, A, xs), length_reverse(a, A, xs))

# A right fold over an append folds the first part onto the fold of the second, reversed to rewrite toward the simple side.
law foldr_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: A -> B -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) == List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}

def foldr_append_sym(a, A, B, f, xs, ys, z):
  Equal.sym(B, List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z), List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)), foldr_append(~a, ~A, ~B, ~f, xs, ys, z))

# Taking n elements and appending the rest after dropping n gives the list back, reversed to rewrite toward the simple side.
law take_append_drop_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {xs == List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) : List<a, A>}

def take_append_drop_sym(a, A, xs, n):
  Equal.sym(List<a, A>, List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)), xs, take_append_drop(a, A, xs, n))

# Mapping preserves the length, reversed to rewrite toward the simple side.
law length_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.length(&1, A, xs) == List.length(&1, B, List.map(~A, ~B, ~f, xs)) : Nat}

def length_map_sym(A, B, f, xs):
  Equal.sym(Nat, List.length(&1, B, List.map(~A, ~B, ~f, xs)), List.length(&1, A, xs), length_map(~A, ~B, ~f, xs))

# Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys, reversed to rewrite toward the simple side.
law map_append_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for -ys: List<A>
  {List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) == List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) : List<B>}

def map_append_sym(A, B, f, xs, ys):
  Equal.sym(List<B>, List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)), List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)), map_append(~A, ~B, ~f, xs, ys))

# Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs, reversed to rewrite toward the simple side.
law map_map_sym:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C
  for xs: List<A>
  {List.map(~A, ~C, ~(x => g(f(x))), xs) == List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) : List<C>}

def map_map_sym(A, B, C, f, g, xs):
  Equal.sym(List<C>, List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)), List.map(~A, ~C, ~(x => g(f(x))), xs), map_map(~A, ~B, ~C, ~f, ~g, xs))

# Taking zero elements gives the empty list, reversed to rewrite toward the simple side.
law take_zero_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {Nil{} == List.take(a, A, xs, 0n) : List<a, A>}

def take_zero_sym(a, A, xs):
  Equal.sym(List<a, A>, List.take(a, A, xs, 0n), Nil{}, take_zero(a, A, xs))

# Dropping zero elements gives the list back, reversed to rewrite toward the simple side.
law drop_zero_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.drop(a, A, xs, 0n) : List<a, A>}

def drop_zero_sym(a, A, xs):
  Equal.sym(List<a, A>, List.drop(a, A, xs, 0n), xs, drop_zero(a, A, xs))

# Taking from the empty list gives the empty list, reversed to rewrite toward the simple side.
law take_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {Nil{} == List.take(a, A, Nil{}, n) : List<a, A>}

def take_nil_sym(a, A, n):
  Equal.sym(List<a, A>, List.take(a, A, Nil{}, n), Nil{}, take_nil(a, A, n))

# Dropping from the empty list gives the empty list, reversed to rewrite toward the simple side.
law drop_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {Nil{} == List.drop(a, A, Nil{}, n) : List<a, A>}

def drop_nil_sym(a, A, n):
  Equal.sym(List<a, A>, List.drop(a, A, Nil{}, n), Nil{}, drop_nil(a, A, n))

# Taking n elements leaves min(n, length) of them, reversed to rewrite toward the simple side.
law length_take_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {Nat.min(n, List.length(a, A, xs)) == List.length(a, A, List.take(a, A, xs, n)) : Nat}

def length_take_sym(a, A, xs, n):
  Equal.sym(Nat, List.length(a, A, List.take(a, A, xs, n)), Nat.min(n, List.length(a, A, xs)), length_take(a, A, xs, n))

# Dropping n elements leaves length - n of them, reversed to rewrite toward the simple side.
law length_drop_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {Nat.sub(List.length(a, A, xs), n) == List.length(a, A, List.drop(a, A, xs, n)) : Nat}

def length_drop_sym(a, A, xs, n):
  Equal.sym(Nat, List.length(a, A, List.drop(a, A, xs, n)), Nat.sub(List.length(a, A, xs), n), length_drop(a, A, xs, n))

# Taking as many elements as the list has gives the list back, reversed to rewrite toward the simple side.
law take_length_sym:
  for -A: Data
  for +xs: List<&2, A>
  {xs == List.take(&2, A, xs, List.length(&2, A, xs)) : List<&2, A>}

def take_length_sym(A, xs):
  Equal.sym(List<&2, A>, List.take(&2, A, xs, List.length(&2, A, xs)), xs, take_length(A, xs))

# Dropping as many elements as the list has gives the empty list, reversed to rewrite toward the simple side.
law drop_length_sym:
  for -A: Data
  for +xs: List<&2, A>
  {Nil{} == List.drop(&2, A, xs, List.length(&2, A, xs)) : List<&2, A>}

def drop_length_sym(A, xs):
  Equal.sym(List<&2, A>, List.drop(&2, A, xs, List.length(&2, A, xs)), Nil{}, drop_length(A, xs))

# Taking m from the first n is taking min(n, m), reversed to rewrite toward the simple side.
law take_take_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for m: Nat
  {List.take(a, A, xs, Nat.min(n, m)) == List.take(a, A, List.take(a, A, xs, n), m) : List<a, A>}

def take_take_sym(a, A, xs, n, m):
  Equal.sym(List<a, A>, List.take(a, A, List.take(a, A, xs, n), m), List.take(a, A, xs, Nat.min(n, m)), take_take(a, A, xs, n, m))

# Dropping m after dropping n is dropping n + m, reversed to rewrite toward the simple side.
law drop_drop_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -m: Nat
  {List.drop(a, A, xs, Nat.add(n, m)) == List.drop(a, A, List.drop(a, A, xs, n), m) : List<a, A>}

def drop_drop_sym(a, A, xs, n, m):
  Equal.sym(List<a, A>, List.drop(a, A, List.drop(a, A, xs, n), m), List.drop(a, A, xs, Nat.add(n, m)), drop_drop(a, A, xs, n, m))

# Reversing the empty list gives the empty list, reversed to rewrite toward the simple side.
law reverse_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  {Nil{} == List.reverse(a, A, Nil{}) : List<a, A>}

def reverse_nil_sym(a, A):
  Equal.sym(List<a, A>, List.reverse(a, A, Nil{}), Nil{}, reverse_nil(a, A))

# Reversing a one-element list gives it back, reversed to rewrite toward the simple side.
law reverse_singleton_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  {[x] == List.reverse(a, A, [x]) : List<a, A>}

def reverse_singleton_sym(a, A, x):
  Equal.sym(List<a, A>, List.reverse(a, A, [x]), [x], reverse_singleton(a, A, x))

# Replicating x n times gives a list of length n, reversed to rewrite toward the simple side.
law length_replicate_sym:
  for -A: Data
  for n: Nat
  for -x: A
  {n == List.length(&2, A, List.replicate(A, n, x)) : Nat}

def length_replicate_sym(A, n, x):
  Equal.sym(Nat, List.length(&2, A, List.replicate(A, n, x)), n, length_replicate(A, n, x))

# Range(n) has length n, reversed to rewrite toward the simple side.
law length_range_sym:
  for n: Nat
  {n == List.length(&2, Nat, List.range(n)) : Nat}

def length_range_sym(n):
  Equal.sym(Nat, List.length(&2, Nat, List.range(n)), n, length_range(n))

# Zipping two lists gives the length of the shorter one, reversed to rewrite toward the simple side.
law length_zip_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {Nat.min(List.length(a, A, xs), List.length(a, A, ys)) == List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) : Nat}

def length_zip_sym(a, A, xs, ys):
  Equal.sym(Nat, List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)), Nat.min(List.length(a, A, xs), List.length(a, A, ys)), length_zip(a, A, xs, ys))

# Appending after a cons: (x :: xs) ++ ys = x :: (xs ++ ys), reversed to rewrite toward the simple side.
law append_cons_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -ys: List<a, A>
  {x <> List.append(a, A, xs, ys) == List.append(a, A, x <> xs, ys) : List<a, A>}

def append_cons_sym(a, A, x, xs, ys):
  Equal.sym(List<a, A>, List.append(a, A, x <> xs, ys), x <> List.append(a, A, xs, ys), append_cons(a, A, x, xs, ys))

# The empty list has length zero, reversed to rewrite toward the simple side.
law length_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  {0n == List.length(a, A, Nil{}) : Nat}

def length_nil_sym(a, A):
  Equal.sym(Nat, List.length(a, A, Nil{}), 0n, length_nil(a, A))

# A cons is one longer than its tail, reversed to rewrite toward the simple side.
law length_cons_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {1n+List.length(a, A, xs) == List.length(a, A, x <> xs) : Nat}

def length_cons_sym(a, A, x, xs):
  Equal.sym(Nat, List.length(a, A, x <> xs), 1n+List.length(a, A, xs), length_cons(a, A, x, xs))

# Concatenating an append concatenates each part: concat (xss ++ yss) = concat xss ++ concat yss, reversed to rewrite toward the simple side.
law concat_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for -yss: List<a, List<a, A>>
  {List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) == List.concat(a, A, List.append(a, List<a, A>, xss, yss)) : List<a, A>}

def concat_append_sym(a, A, xss, yss):
  Equal.sym(List<a, A>, List.concat(a, A, List.append(a, List<a, A>, xss, yss)), List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)), concat_append(a, A, xss, yss))

# A left fold over an append folds the second part from the fold of the first, reversed to rewrite toward the simple side.
law foldl_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) == List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}

def foldl_append_sym(a, A, B, f, xs, ys, z):
  Equal.sym(B, List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z), List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)), foldl_append(~a, ~A, ~B, ~f, xs, ys, z))

# Mapping commutes with reversing: map f (reverse xs) = reverse (map f xs), reversed to rewrite toward the simple side.
law map_reverse_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) : List<B>}

def map_reverse_sym(A, B, f, xs):
  Equal.sym(List<B>, List.map(~A, ~B, ~f, List.reverse(&1, A, xs)), List.reverse(&1, B, List.map(~A, ~B, ~f, xs)), map_reverse(~A, ~B, ~f, xs))

# All over an append is all over each part, joined by and, reversed to rewrite toward the simple side.
law all_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) == List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) : Bool}

def all_append_sym(a, A, f, xs, ys):
  Equal.sym(Bool, List.all(~a, ~A, ~f, List.append(a, A, xs, ys)), Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)), all_append(~a, ~A, ~f, xs, ys))

# Any over an append is any over each part, joined by or, reversed to rewrite toward the simple side.
law any_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) == List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) : Bool}

def any_append_sym(a, A, f, xs, ys):
  Equal.sym(Bool, List.any(~a, ~A, ~f, List.append(a, A, xs, ys)), Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)), any_append(~a, ~A, ~f, xs, ys))

# Filtering an append filters each part, reversed to rewrite toward the simple side.
law filter_append_sym:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) == List.filter(~A, ~f, List.append(&2, A, xs, ys)) : List<&2, A>}

def filter_append_sym(A, f, xs, ys):
  Equal.sym(List<&2, A>, List.filter(~A, ~f, List.append(&2, A, xs, ys)), List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)), filter_append(~A, ~f, xs, ys))

# An append contains x iff either part does, reversed to rewrite toward the simple side.
law contains_append_sym:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for -ys: List<&2, A>
  for +x: A
  {Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) == List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) : Bool}

def contains_append_sym(A, eq, xs, ys, x):
  Equal.sym(Bool, List.contains(~A, ~eq, List.append(&2, A, xs, ys), x), Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)), contains_append(~A, ~eq, xs, ys, x))

# Filtering never makes a list longer, reversed to rewrite toward the simple side.
law length_filter_le_sym:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {True{} == Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) : Bool}

def length_filter_le_sym(A, f, xs):
  Equal.sym(Bool, Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)), True{}, length_filter_le(~A, ~f, xs))

# Taking the length of the first part of an append gives the first part back, reversed to rewrite toward the simple side.
law take_left_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {xs == List.take(a, A, List.append(a, A, xs, ys), List.length(a, A, xs)) : List<a, A>}

def take_left_sym(a, A, xs, ys):
  Equal.sym(List<a, A>, List.take(a, A, List.append(a, A, xs, ys), List.length(a, A, xs)), xs, take_left(a, A, xs, ys))

# Dropping the length of the first part of an append gives the second part, reversed to rewrite toward the simple side.
law drop_left_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {ys == List.drop(a, A, List.append(a, A, xs, ys), List.length(a, A, xs)) : List<a, A>}

def drop_left_sym(a, A, xs, ys):
  Equal.sym(List<a, A>, List.drop(a, A, List.append(a, A, xs, ys), List.length(a, A, xs)), ys, drop_left(a, A, xs, ys))

# Taking past the first part of an append keeps it and takes the rest from the second part, reversed to rewrite toward the simple side.
law take_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -n: Nat
  {List.append(a, A, xs, List.take(a, A, ys, n)) == List.take(a, A, List.append(a, A, xs, ys), Nat.add(List.length(a, A, xs), n)) : List<a, A>}

def take_append_sym(a, A, xs, ys, n):
  Equal.sym(List<a, A>, List.take(a, A, List.append(a, A, xs, ys), Nat.add(List.length(a, A, xs), n)), List.append(a, A, xs, List.take(a, A, ys, n)), take_append(a, A, xs, ys, n))

# Dropping past the first part of an append drops the rest from the second part, reversed to rewrite toward the simple side.
law drop_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -n: Nat
  {List.drop(a, A, ys, n) == List.drop(a, A, List.append(a, A, xs, ys), Nat.add(List.length(a, A, xs), n)) : List<a, A>}

def drop_append_sym(a, A, xs, ys, n):
  Equal.sym(List<a, A>, List.drop(a, A, List.append(a, A, xs, ys), Nat.add(List.length(a, A, xs), n)), List.drop(a, A, ys, n), drop_append(a, A, xs, ys, n))

# Taking at most the length of the first part of an append only sees the first part, reversed to rewrite toward the simple side.
law take_append_of_le_length_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  for n: Nat
  for h: MNat.le(n, List.length(a, A, xs))
  {List.take(a, A, xs, n) == List.take(a, A, List.append(a, A, xs, ys), n) : List<a, A>}

def take_append_of_le_length_sym(a, A, xs, ys, n, h):
  Equal.sym(List<a, A>, List.take(a, A, List.append(a, A, xs, ys), n), List.take(a, A, xs, n), take_append_of_le_length(a, A, xs, ys, n, h))

# Dropping at most the length of the first part of an append drops only from the first part, reversed to rewrite toward the simple side.
law drop_append_of_le_length_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  for n: Nat
  for h: MNat.le(n, List.length(a, A, xs))
  {List.append(a, A, List.drop(a, A, xs, n), ys) == List.drop(a, A, List.append(a, A, xs, ys), n) : List<a, A>}

def drop_append_of_le_length_sym(a, A, xs, ys, n, h):
  Equal.sym(List<a, A>, List.drop(a, A, List.append(a, A, xs, ys), n), List.append(a, A, List.drop(a, A, xs, n), ys), drop_append_of_le_length(a, A, xs, ys, n, h))

# Mapping commutes with taking: map f (take n xs) = take n (map f xs), reversed to rewrite toward the simple side.
law map_take_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for n: Nat
  {List.take(&1, B, List.map(~A, ~B, ~f, xs), n) == List.map(~A, ~B, ~f, List.take(&1, A, xs, n)) : List<B>}

def map_take_sym(A, B, f, xs, n):
  Equal.sym(List<B>, List.map(~A, ~B, ~f, List.take(&1, A, xs, n)), List.take(&1, B, List.map(~A, ~B, ~f, xs), n), map_take(~A, ~B, ~f, xs, n))

# Mapping commutes with dropping: map f (drop n xs) = drop n (map f xs), reversed to rewrite toward the simple side.
law map_drop_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for n: Nat
  {List.drop(&1, B, List.map(~A, ~B, ~f, xs), n) == List.map(~A, ~B, ~f, List.drop(&1, A, xs, n)) : List<B>}

def map_drop_sym(A, B, f, xs, n):
  Equal.sym(List<B>, List.map(~A, ~B, ~f, List.drop(&1, A, xs, n)), List.drop(&1, B, List.map(~A, ~B, ~f, xs), n), map_drop(~A, ~B, ~f, xs, n))

# Taking m from n copies of x gives min(m, n) copies of x, reversed to rewrite toward the simple side.
law take_replicate_sym:
  for -A: Data
  for n: Nat
  for m: Nat
  for -x: A
  {List.replicate(A, Nat.min(m, n), x) == List.take(&2, A, List.replicate(A, n, x), m) : List<&2, A>}

def take_replicate_sym(A, n, m, x):
  Equal.sym(List<&2, A>, List.take(&2, A, List.replicate(A, n, x), m), List.replicate(A, Nat.min(m, n), x), take_replicate(A, n, m, x))

# Dropping m from n copies of x gives n - m copies of x, reversed to rewrite toward the simple side.
law drop_replicate_sym:
  for -A: Data
  for n: Nat
  for m: Nat
  for -x: A
  {List.replicate(A, Nat.sub(n, m), x) == List.drop(&2, A, List.replicate(A, n, x), m) : List<&2, A>}

def drop_replicate_sym(A, n, m, x):
  Equal.sym(List<&2, A>, List.drop(&2, A, List.replicate(A, n, x), m), List.replicate(A, Nat.sub(n, m), x), drop_replicate(A, n, m, x))

# The tail is one shorter than the list, or empty: length (tail xs) = length xs - 1, reversed to rewrite toward the simple side.
law length_tail_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {Nat.sub(List.length(a, A, xs), 1n) == List.length(a, A, List.tail(a, A, xs)) : Nat}

def length_tail_sym(a, A, xs):
  Equal.sym(Nat, List.length(a, A, List.tail(a, A, xs)), Nat.sub(List.length(a, A, xs), 1n), length_tail(a, A, xs))

# Mapping the identity gives the list back, reversed to rewrite toward the simple side.
law map_id_sym:
  for ~A: Type
  for xs: List<A>
  {xs == List.map(~A, ~A, ~(x => x), xs) : List<A>}

def map_id_sym(A, xs):
  Equal.sym(List<A>, List.map(~A, ~A, ~(x => x), xs), xs, map_id(~A, xs))

# A right fold over a map folds with the mapped function: foldr g z (map f xs) = foldr (g . f) z xs, reversed to rewrite toward the simple side.
law foldr_map_sym:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C -> C
  for xs: List<A>
  for -z: C
  {List.foldr(~&1, ~A, ~C, ~(x => y => g(f(x), y)), xs, z) == List.foldr(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, xs), z) : C}

def foldr_map_sym(A, B, C, f, g, xs, z):
  Equal.sym(C, List.foldr(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, xs), z), List.foldr(~&1, ~A, ~C, ~(x => y => g(f(x), y)), xs, z), foldr_map(~A, ~B, ~C, ~f, ~g, xs, z))

# A left fold over a map folds with the mapped function: foldl g z (map f xs) = foldl (fun acc x => g acc (f x)) z xs, reversed to rewrite toward the simple side.
law foldl_map_sym:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: C -> B -> C
  for xs: List<A>
  for -z: C
  {List.foldl(~&1, ~A, ~C, ~(x => y => g(x, f(y))), xs, z) == List.foldl(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, xs), z) : C}

def foldl_map_sym(A, B, C, f, g, xs, z):
  Equal.sym(C, List.foldl(~&1, ~B, ~C, ~g, List.map(~A, ~B, ~f, xs), z), List.foldl(~&1, ~A, ~C, ~(x => y => g(x, f(y))), xs, z), foldl_map(~A, ~B, ~C, ~f, ~g, xs, z))

# Replicating m + n times appends m copies to n copies, reversed to rewrite toward the simple side.
law replicate_add_sym:
  for -A: Data
  for m: Nat
  for -n: Nat
  for -x: A
  {List.append(&2, A, List.replicate(A, m, x), List.replicate(A, n, x)) == List.replicate(A, Nat.add(m, n), x) : List<&2, A>}

def replicate_add_sym(A, m, n, x):
  Equal.sym(List<&2, A>, List.replicate(A, Nat.add(m, n), x), List.append(&2, A, List.replicate(A, m, x), List.replicate(A, n, x)), replicate_add(A, m, n, x))

# Reversing n copies of x gives them back, reversed to rewrite toward the simple side.
law reverse_replicate_sym:
  for -A: Data
  for n: Nat
  for -x: A
  {List.replicate(A, n, x) == List.reverse(&2, A, List.replicate(A, n, x)) : List<&2, A>}

def reverse_replicate_sym(A, n, x):
  Equal.sym(List<&2, A>, List.reverse(&2, A, List.replicate(A, n, x)), List.replicate(A, n, x), reverse_replicate(A, n, x))

# Filtering with an always-true predicate gives the list back, reversed to rewrite toward the simple side.
law filter_true_sym:
  for ~A: Data
  for xs: List<&2, A>
  {xs == List.filter(~A, ~(x => True{}), xs) : List<&2, A>}

def filter_true_sym(A, xs):
  Equal.sym(List<&2, A>, List.filter(~A, ~(x => True{}), xs), xs, filter_true(~A, xs))

# Filtering with an always-false predicate gives the empty list, reversed to rewrite toward the simple side.
law filter_false_sym:
  for ~A: Data
  for xs: List<&2, A>
  {Nil{} == List.filter(~A, ~(x => False{}), xs) : List<&2, A>}

def filter_false_sym(A, xs):
  Equal.sym(List<&2, A>, List.filter(~A, ~(x => False{}), xs), Nil{}, filter_false(~A, xs))

# Filtering twice is filtering by both predicates: filter p (filter q xs) = filter (p and q) xs, reversed to rewrite toward the simple side.
law filter_filter_sym:
  for ~A: Data
  for ~p: A -> Bool
  for ~q: A -> Bool
  for xs: List<&2, A>
  {List.filter(~A, ~(+x => Bool.and(p(x), q(x))), xs) == List.filter(~A, ~p, List.filter(~A, ~q, xs)) : List<&2, A>}

def filter_filter_sym(A, p, q, xs):
  Equal.sym(List<&2, A>, List.filter(~A, ~p, List.filter(~A, ~q, xs)), List.filter(~A, ~(+x => Bool.and(p(x), q(x))), xs), filter_filter(~A, ~p, ~q, xs))

# All over a filter checks q only where p holds: all q (filter p xs) = all (not p or q) xs, reversed to rewrite toward the simple side.
law all_filter_sym:
  for ~A: Data
  for ~p: A -> Bool
  for ~q: A -> Bool
  for xs: List<&2, A>
  {List.all(~&2, ~A, ~(+x => Bool.or(Bool.not(p(x)), q(x))), xs) == List.all(~&2, ~A, ~q, List.filter(~A, ~p, xs)) : Bool}

def all_filter_sym(A, p, q, xs):
  Equal.sym(Bool, List.all(~&2, ~A, ~q, List.filter(~A, ~p, xs)), List.all(~&2, ~A, ~(+x => Bool.or(Bool.not(p(x)), q(x))), xs), all_filter(~A, ~p, ~q, xs))

# Any over a filter looks for q only where p holds: any q (filter p xs) = any (p and q) xs, reversed to rewrite toward the simple side.
law any_filter_sym:
  for ~A: Data
  for ~p: A -> Bool
  for ~q: A -> Bool
  for xs: List<&2, A>
  {List.any(~&2, ~A, ~(+x => Bool.and(p(x), q(x))), xs) == List.any(~&2, ~A, ~q, List.filter(~A, ~p, xs)) : Bool}

def any_filter_sym(A, p, q, xs):
  Equal.sym(Bool, List.any(~&2, ~A, ~q, List.filter(~A, ~p, xs)), List.any(~&2, ~A, ~(+x => Bool.and(p(x), q(x))), xs), any_filter(~A, ~p, ~q, xs))

# All over a map checks the composed predicate: all p (map f xs) = all (p . f) xs, reversed to rewrite toward the simple side.
law all_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for ~p: B -> Bool
  for xs: List<A>
  {List.all(~&1, ~A, ~(x => p(f(x))), xs) == List.all(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) : Bool}

def all_map_sym(A, B, f, p, xs):
  Equal.sym(Bool, List.all(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)), List.all(~&1, ~A, ~(x => p(f(x))), xs), all_map(~A, ~B, ~f, ~p, xs))

# Any over a map checks the composed predicate: any p (map f xs) = any (p . f) xs, reversed to rewrite toward the simple side.
law any_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for ~p: B -> Bool
  for xs: List<A>
  {List.any(~&1, ~A, ~(x => p(f(x))), xs) == List.any(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) : Bool}

def any_map_sym(A, B, f, p, xs):
  Equal.sym(Bool, List.any(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)), List.any(~&1, ~A, ~(x => p(f(x))), xs), any_map(~A, ~B, ~f, ~p, xs))

# Reversing does not change whether all elements satisfy a predicate, reversed to rewrite toward the simple side.
law all_reverse_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {List.all(~a, ~A, ~f, xs) == List.all(~a, ~A, ~f, List.reverse(a, A, xs)) : Bool}

def all_reverse_sym(a, A, f, xs):
  Equal.sym(Bool, List.all(~a, ~A, ~f, List.reverse(a, A, xs)), List.all(~a, ~A, ~f, xs), all_reverse(~a, ~A, ~f, xs))

# Reversing does not change whether some element satisfies a predicate, reversed to rewrite toward the simple side.
law any_reverse_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {List.any(~a, ~A, ~f, xs) == List.any(~a, ~A, ~f, List.reverse(a, A, xs)) : Bool}

def any_reverse_sym(a, A, f, xs):
  Equal.sym(Bool, List.any(~a, ~A, ~f, List.reverse(a, A, xs)), List.any(~a, ~A, ~f, xs), any_reverse(~a, ~A, ~f, xs))

# Reversing does not change whether a list contains x, reversed to rewrite toward the simple side.
law contains_reverse_sym:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for +x: A
  {List.contains(~A, ~eq, xs, x) == List.contains(~A, ~eq, List.reverse(&2, A, xs), x) : Bool}

def contains_reverse_sym(A, eq, xs, x):
  Equal.sym(Bool, List.contains(~A, ~eq, List.reverse(&2, A, xs), x), List.contains(~A, ~eq, xs, x), contains_reverse(~A, ~eq, xs, x))

# Zipping the empty list with anything gives the empty list, reversed to rewrite toward the simple side.
law zip_nil_left_sym:
  for -a: Quant
  for -A: Kind(a)
  for -b: Quant
  for -B: Kind(b)
  for -ys: List<b, B>
  {Nil{} == List.zip(a, A, b, B, Nil{}, ys) : List<&1, A & B>}

def zip_nil_left_sym(a, A, b, B, ys):
  Equal.sym(List<&1, A & B>, List.zip(a, A, b, B, Nil{}, ys), Nil{}, zip_nil_left(a, A, b, B, ys))

# Zipping anything with the empty list gives the empty list, reversed to rewrite toward the simple side.
law zip_nil_right_sym:
  for -a: Quant
  for -A: Kind(a)
  for -b: Quant
  for -B: Kind(b)
  for xs: List<a, A>
  {Nil{} == List.zip(a, A, b, B, xs, Nil{}) : List<&1, A & B>}

def zip_nil_right_sym(a, A, b, B, xs):
  Equal.sym(List<&1, A & B>, List.zip(a, A, b, B, xs, Nil{}), Nil{}, zip_nil_right(a, A, b, B, xs))

# The head of a cons is its first element, reversed to rewrite toward the simple side.
law head_cons_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {Some{x} == List.head(a, A, x <> xs) : Maybe<a, A>}

def head_cons_sym(a, A, x, xs):
  Equal.sym(Maybe<a, A>, List.head(a, A, x <> xs), Some{x}, head_cons(a, A, x, xs))

# The head of an append is the head of the first part, or else of the second, reversed to rewrite toward the simple side.
law head_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {Maybe.or(a, A, List.head(a, A, xs), List.head(a, A, ys)) == List.head(a, A, List.append(a, A, xs, ys)) : Maybe<a, A>}

def head_append_sym(a, A, xs, ys):
  Equal.sym(Maybe<a, A>, List.head(a, A, List.append(a, A, xs, ys)), Maybe.or(a, A, List.head(a, A, xs), List.head(a, A, ys)), head_append(a, A, xs, ys))

# The head of a map is the mapped head, reversed to rewrite toward the simple side.
law head_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {Maybe.map(&1, A, B, f, List.head(&1, A, xs)) == List.head(&1, B, List.map(~A, ~B, ~f, xs)) : Maybe<&1, B>}

def head_map_sym(A, B, f, xs):
  Equal.sym(Maybe<&1, B>, List.head(&1, B, List.map(~A, ~B, ~f, xs)), Maybe.map(&1, A, B, f, List.head(&1, A, xs)), head_map(~A, ~B, ~f, xs))

# The tail of a map is the map of the tail, reversed to rewrite toward the simple side.
law tail_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.map(~A, ~B, ~f, List.tail(&1, A, xs)) == List.tail(&1, B, List.map(~A, ~B, ~f, xs)) : List<B>}

def tail_map_sym(A, B, f, xs):
  Equal.sym(List<B>, List.tail(&1, B, List.map(~A, ~B, ~f, xs)), List.map(~A, ~B, ~f, List.tail(&1, A, xs)), tail_map(~A, ~B, ~f, xs))

# The element at index zero of a cons is its head, reversed to rewrite toward the simple side.
law get_cons_zero_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {Some{x} == List.get(a, A, x <> xs, 0n) : Maybe<a, A>}

def get_cons_zero_sym(a, A, x, xs):
  Equal.sym(Maybe<a, A>, List.get(a, A, x <> xs, 0n), Some{x}, get_cons_zero(a, A, x, xs))

# The element at index n + 1 of a cons is the element at index n of its tail, reversed to rewrite toward the simple side.
law get_cons_succ_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -n: Nat
  {List.get(a, A, xs, n) == List.get(a, A, x <> xs, 1n+n) : Maybe<a, A>}

def get_cons_succ_sym(a, A, x, xs, n):
  Equal.sym(Maybe<a, A>, List.get(a, A, x <> xs, 1n+n), List.get(a, A, xs, n), get_cons_succ(a, A, x, xs, n))

# Indexing a map is mapping the indexed element, reversed to rewrite toward the simple side.
law get_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for n: Nat
  {Maybe.map(&1, A, B, f, List.get(&1, A, xs, n)) == List.get(&1, B, List.map(~A, ~B, ~f, xs), n) : Maybe<&1, B>}

def get_map_sym(A, B, f, xs, n):
  Equal.sym(Maybe<&1, B>, List.get(&1, B, List.map(~A, ~B, ~f, xs), n), Maybe.map(&1, A, B, f, List.get(&1, A, xs, n)), get_map(~A, ~B, ~f, xs, n))

# Setting an element does not change the length, reversed to rewrite toward the simple side.
law length_set_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -x: A
  {List.length(a, A, xs) == List.length(a, A, List.set(a, A, xs, n, x)) : Nat}

def length_set_sym(a, A, xs, n, x):
  Equal.sym(Nat, List.length(a, A, List.set(a, A, xs, n, x)), List.length(a, A, xs), length_set(a, A, xs, n, x))

# Reading the index just set gives the new value wherever the index is in range, reversed to rewrite toward the simple side.
law get_set_self_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -x: A
  {Maybe.map(a, A, A, y => x, List.get(a, A, xs, n)) == List.get(a, A, List.set(a, A, xs, n, x), n) : Maybe<a, A>}

def get_set_self_sym(a, A, xs, n, x):
  Equal.sym(Maybe<a, A>, List.get(a, A, List.set(a, A, xs, n, x), n), Maybe.map(a, A, A, y => x, List.get(a, A, xs, n)), get_set_self(a, A, xs, n, x))

# The last element of xs ++ [x] is x, reversed to rewrite toward the simple side.
law last_append_singleton_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -x: A
  {Some{x} == List.last(a, A, List.append(a, A, xs, [x])) : Maybe<a, A>}

def last_append_singleton_sym(a, A, xs, x):
  Equal.sym(Maybe<a, A>, List.last(a, A, List.append(a, A, xs, [x])), Some{x}, last_append_singleton(a, A, xs, x))

# The head of the reverse is the last element, reversed to rewrite toward the simple side.
law head_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.last(a, A, xs) == List.head(a, A, List.reverse(a, A, xs)) : Maybe<a, A>}

def head_reverse_sym(a, A, xs):
  Equal.sym(Maybe<a, A>, List.head(a, A, List.reverse(a, A, xs)), List.last(a, A, xs), head_reverse(a, A, xs))

# The last element of the reverse is the head, reversed to rewrite toward the simple side.
law last_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.head(a, A, xs) == List.last(a, A, List.reverse(a, A, xs)) : Maybe<a, A>}

def last_reverse_sym(a, A, xs):
  Equal.sym(Maybe<a, A>, List.last(a, A, List.reverse(a, A, xs)), List.head(a, A, xs), last_reverse(a, A, xs))

# A list is empty exactly when its length is zero, reversed to rewrite toward the simple side.
law is_empty_iff_length_eq_zero_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {Nat.is_eq(List.length(a, A, xs), 0n) == List.is_empty(a, A, xs) : Bool}

def is_empty_iff_length_eq_zero_sym(a, A, xs):
  Equal.sym(Bool, List.is_empty(a, A, xs), Nat.is_eq(List.length(a, A, xs), 0n), is_empty_iff_length_eq_zero(a, A, xs))

# An append is empty exactly when both parts are, reversed to rewrite toward the simple side.
law is_empty_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {Bool.and(List.is_empty(a, A, xs), List.is_empty(a, A, ys)) == List.is_empty(a, A, List.append(a, A, xs, ys)) : Bool}

def is_empty_append_sym(a, A, xs, ys):
  Equal.sym(Bool, List.is_empty(a, A, List.append(a, A, xs, ys)), Bool.and(List.is_empty(a, A, xs), List.is_empty(a, A, ys)), is_empty_append(a, A, xs, ys))

# The reverse is empty exactly when the list is, reversed to rewrite toward the simple side.
law is_empty_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.is_empty(a, A, xs) == List.is_empty(a, A, List.reverse(a, A, xs)) : Bool}

def is_empty_reverse_sym(a, A, xs):
  Equal.sym(Bool, List.is_empty(a, A, List.reverse(a, A, xs)), List.is_empty(a, A, xs), is_empty_reverse(a, A, xs))

# A map is empty exactly when the list is, reversed to rewrite toward the simple side.
law is_empty_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.is_empty(&1, A, xs) == List.is_empty(&1, B, List.map(~A, ~B, ~f, xs)) : Bool}

def is_empty_map_sym(A, B, f, xs):
  Equal.sym(Bool, List.is_empty(&1, B, List.map(~A, ~B, ~f, xs)), List.is_empty(&1, A, xs), is_empty_map(~A, ~B, ~f, xs))

# Filtering commutes with reversing: filter p (reverse xs) = reverse (filter p xs), reversed to rewrite toward the simple side.
law filter_reverse_sym:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {List.reverse(&2, A, List.filter(~A, ~f, xs)) == List.filter(~A, ~f, List.reverse(&2, A, xs)) : List<&2, A>}

def filter_reverse_sym(A, f, xs):
  Equal.sym(List<&2, A>, List.filter(~A, ~f, List.reverse(&2, A, xs)), List.reverse(&2, A, List.filter(~A, ~f, xs)), filter_reverse(~A, ~f, xs))

# Folding cons from the right, starting from the empty list, rebuilds the list, reversed to rewrite toward the simple side.
law foldr_cons_nil_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for xs: List<a, A>
  {xs == List.foldr(~a, ~A, ~List<a, A>, ~(x => acc => x <> acc), xs, Nil{}) : List<a, A>}

def foldr_cons_nil_sym(a, A, xs):
  Equal.sym(List<a, A>, List.foldr(~a, ~A, ~List<a, A>, ~(x => acc => x <> acc), xs, Nil{}), xs, foldr_cons_nil(~a, ~A, xs))

# A left fold over the reverse is a right fold with the arguments flipped, reversed to rewrite toward the simple side.
law foldl_reverse_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for -z: B
  {List.foldr(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z) == List.foldl(~a, ~A, ~B, ~f, List.reverse(a, A, xs), z) : B}

def foldl_reverse_sym(a, A, B, f, xs, z):
  Equal.sym(B, List.foldl(~a, ~A, ~B, ~f, List.reverse(a, A, xs), z), List.foldr(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z), foldl_reverse(~a, ~A, ~B, ~f, xs, z))

# A right fold over the reverse is a left fold with the arguments flipped, reversed to rewrite toward the simple side.
law foldr_reverse_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: A -> B -> B
  for xs: List<a, A>
  for -z: B
  {List.foldl(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z) == List.foldr(~a, ~A, ~B, ~f, List.reverse(a, A, xs), z) : B}

def foldr_reverse_sym(a, A, B, f, xs, z):
  Equal.sym(B, List.foldr(~a, ~A, ~B, ~f, List.reverse(a, A, xs), z), List.foldl(~a, ~A, ~B, ~(x => y => f(y, x)), xs, z), foldr_reverse(~a, ~A, ~B, ~f, xs, z))

# Range(n + 1) is range(n) followed by n, reversed to rewrite toward the simple side.
law range_succ_sym:
  for n: Nat
  {List.append(&2, Nat, List.range(n), [n]) == List.range(1n+n) : List<&2, Nat>}

def range_succ_sym(n):
  Equal.sym(List<&2, Nat>, List.range(1n+n), List.append(&2, Nat, List.range(n), [n]), range_succ(n))

# Finding in an append finds in the first part, or else in the second, reversed to rewrite toward the simple side.
law find_append_sym:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {Maybe.or(&2, A, List.find(~A, ~f, xs), List.find(~A, ~f, ys)) == List.find(~A, ~f, List.append(&2, A, xs, ys)) : Maybe<&2, A>}

def find_append_sym(A, f, xs, ys):
  Equal.sym(Maybe<&2, A>, List.find(~A, ~f, List.append(&2, A, xs, ys)), Maybe.or(&2, A, List.find(~A, ~f, xs), List.find(~A, ~f, ys)), find_append(~A, ~f, xs, ys))

# All elements satisfy f exactly when no element fails it, reversed to rewrite toward the simple side.
law all_eq_not_any_not_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {Bool.not(List.any(~a, ~A, ~(x => Bool.not(f(x))), xs)) == List.all(~a, ~A, ~f, xs) : Bool}

def all_eq_not_any_not_sym(a, A, f, xs):
  Equal.sym(Bool, List.all(~a, ~A, ~f, xs), Bool.not(List.any(~a, ~A, ~(x => Bool.not(f(x))), xs)), all_eq_not_any_not(~a, ~A, ~f, xs))

# Some element satisfies f exactly when not all elements fail it, reversed to rewrite toward the simple side.
law any_eq_not_all_not_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  {Bool.not(List.all(~a, ~A, ~(x => Bool.not(f(x))), xs)) == List.any(~a, ~A, ~f, xs) : Bool}

def any_eq_not_all_not_sym(a, A, f, xs):
  Equal.sym(Bool, List.any(~a, ~A, ~f, xs), Bool.not(List.all(~a, ~A, ~(x => Bool.not(f(x))), xs)), any_eq_not_all_not(~a, ~A, ~f, xs))

# A one-element list has length one, reversed to rewrite toward the simple side.
law length_singleton_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  {1n == List.length(a, A, [x]) : Nat}

def length_singleton_sym(a, A, x):
  Equal.sym(Nat, List.length(a, A, [x]), 1n, length_singleton(a, A, x))

# Reversing a cons puts its head last: reverse (x :: xs) = reverse xs ++ [x], reversed to rewrite toward the simple side.
law reverse_cons_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for xs: List<a, A>
  {List.append(a, A, List.reverse(a, A, xs), [x]) == List.reverse(a, A, x <> xs) : List<a, A>}

def reverse_cons_sym(a, A, x, xs):
  Equal.sym(List<a, A>, List.reverse(a, A, x <> xs), List.append(a, A, List.reverse(a, A, xs), [x]), reverse_cons(a, A, x, xs))

# Taking n + 1 elements of a cons keeps its head and takes n from its tail, reversed to rewrite toward the simple side.
law take_succ_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -n: Nat
  {x <> List.take(a, A, xs, n) == List.take(a, A, x <> xs, 1n+n) : List<a, A>}

def take_succ_sym(a, A, x, xs, n):
  Equal.sym(List<a, A>, List.take(a, A, x <> xs, 1n+n), x <> List.take(a, A, xs, n), take_succ(a, A, x, xs, n))

# Dropping n + 1 elements of a cons drops its head and n from its tail, reversed to rewrite toward the simple side.
law drop_succ_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -n: Nat
  {List.drop(a, A, xs, n) == List.drop(a, A, x <> xs, 1n+n) : List<a, A>}

def drop_succ_sym(a, A, x, xs, n):
  Equal.sym(List<a, A>, List.drop(a, A, x <> xs, 1n+n), List.drop(a, A, xs, n), drop_succ(a, A, x, xs, n))
