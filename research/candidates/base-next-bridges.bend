# Proofs of bend-mathlib's internal_ bridge lemmas for Base after 2.0.37 (PLAN F39), checked at bend 234cb9b.
# They replace the {==} bodies in list.bend and string.bend when the pin moves past #1548/#1459.
import Base

def internal_all_go_false(~a: Quant, ~A: Kind(a), ~f: A -> Bool, t: List<a, A>) -> {False{} == List.all.go(~a, ~A, ~f, t, False{}) : Bool}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

def internal_all_go(~a: Quant, ~A: Kind(a), ~f: A -> Bool, t: List<a, A>, b: Bool) -> {Bool.and(b, List.all(~a, ~A, ~f, t)) == List.all.go(~a, ~A, ~f, t, b) : Bool}:
  match b:
    case False{}:
      internal_all_go_false(~a, ~A, ~f, t)
    case True{}:
      {==}

def internal_all_cons(~a: Quant, ~A: Kind(a), ~f: A -> Bool, h: A, t: List<a, A>) -> {Bool.and(f(h), List.all(~a, ~A, ~f, t)) == List.all(~a, ~A, ~f, h <> t) : Bool}:
  internal_all_go(~a, ~A, ~f, t, f(h))

def internal_any_go_true(~a: Quant, ~A: Kind(a), ~f: A -> Bool, t: List<a, A>) -> {True{} == List.any.go(~a, ~A, ~f, t, True{}) : Bool}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

def internal_any_go(~a: Quant, ~A: Kind(a), ~f: A -> Bool, t: List<a, A>, b: Bool) -> {Bool.or(b, List.any(~a, ~A, ~f, t)) == List.any.go(~a, ~A, ~f, t, b) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      internal_any_go_true(~a, ~A, ~f, t)

def internal_any_cons(~a: Quant, ~A: Kind(a), ~f: A -> Bool, h: A, t: List<a, A>) -> {Bool.or(f(h), List.any(~a, ~A, ~f, t)) == List.any(~a, ~A, ~f, h <> t) : Bool}:
  internal_any_go(~a, ~A, ~f, t, f(h))

def internal_find_go_some(~A: Data, ~f: A -> Bool, t: List<&2, A>, x: A) -> {Some{x} == List.find.go(~A, ~f, t, Some{x}) : Maybe<&2, A>}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

def internal_find_go(~A: Data, ~f: A -> Bool, +h: A, t: List<&2, A>, b: Bool) -> {List.find.put(A, h, List.find(~A, ~f, t), b) == List.find.go(~A, ~f, t, List.find.put(A, h, None{}, b)) : Maybe<&2, A>}:
  match b:
    case False{}:
      {==}
    case True{}:
      internal_find_go_some(~A, ~f, t, h)

def internal_find_cons(~A: Data, ~f: A -> Bool, +h: A, t: List<&2, A>) -> {List.find.put(A, h, List.find(~A, ~f, t), f(h)) == List.find(~A, ~f, h <> t) : Maybe<&2, A>}:
  internal_find_go(~A, ~f, h, t, f(h))

def internal_contains_go_true(~A: Data, ~eq: A -> A -> Bool, t: List<&2, A>, +x: A) -> {True{} == List.contains.go(~A, ~eq, t, x, True{}) : Bool}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

def internal_contains_go(~A: Data, ~eq: A -> A -> Bool, t: List<&2, A>, +x: A, b: Bool) -> {Bool.or(b, List.contains(~A, ~eq, t, x)) == List.contains.go(~A, ~eq, t, x, b) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      internal_contains_go_true(~A, ~eq, t, x)

def internal_contains_cons(~A: Data, ~eq: A -> A -> Bool, h: A, t: List<&2, A>, +x: A) -> {Bool.or(eq(h, x), List.contains(~A, ~eq, t, x)) == List.contains(~A, ~eq, h <> t, x) : Bool}:
  internal_contains_go(~A, ~eq, t, x, eq(h, x))

def internal_sorted_cons_true(-x: Nat, -y: Nat, -z: List<&1, Nat & Nat>, e: {Nat.is_le(x, y) == True{} : Bool}) -> {List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), z) == List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), (x, y) <> z) : Bool}:
  %Equal.sym(Bool, Nat.is_le(x, y), True{}, e) : {List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), z) == List.all.go(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), z, _) : Bool}
  {==}

def internal_sorted_cons_false(-x: Nat, -y: Nat, z: List<&1, Nat & Nat>, e: {Nat.is_le(x, y) == False{} : Bool}) -> {False{} == List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), (x, y) <> z) : Bool}:
  %Equal.sym(Bool, Nat.is_le(x, y), False{}, e) : {False{} == List.all.go(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), z, _) : Bool}
  internal_all_go_false(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), z)

def internal_all_map_go(~A: Type, ~B: Type, ~f: A -> B, ~p: B -> Bool, t: List<A>, b: Bool) -> {List.all.go(~&1, ~B, ~p, List.map(~A, ~B, ~f, t), b) == List.all.go(~&1, ~A, ~(x => p(f(x))), t, b) : Bool}:
  match t:
    case Nil{}:
      match b:
        case False{}:
          {==}
        case True{}:
          {==}
    case h <> r:
      match b:
        case False{}:
          {==}
        case True{}:
          internal_all_map_go(~A, ~B, ~f, ~p, r, p(f(h)))

def internal_all_map(~A: Type, ~B: Type, ~f: A -> B, ~p: B -> Bool, xs: List<A>) -> {List.all(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) == List.all(~&1, ~A, ~(x => p(f(x))), xs) : Bool}:
  internal_all_map_go(~A, ~B, ~f, ~p, xs, True{})

def internal_any_map_go(~A: Type, ~B: Type, ~f: A -> B, ~p: B -> Bool, t: List<A>, b: Bool) -> {List.any.go(~&1, ~B, ~p, List.map(~A, ~B, ~f, t), b) == List.any.go(~&1, ~A, ~(x => p(f(x))), t, b) : Bool}:
  match t:
    case Nil{}:
      match b:
        case False{}:
          {==}
        case True{}:
          {==}
    case h <> r:
      match b:
        case False{}:
          internal_any_map_go(~A, ~B, ~f, ~p, r, p(f(h)))
        case True{}:
          {==}

def internal_any_map(~A: Type, ~B: Type, ~f: A -> B, ~p: B -> Bool, xs: List<A>) -> {List.any(~&1, ~B, ~p, List.map(~A, ~B, ~f, xs)) == List.any(~&1, ~A, ~(x => p(f(x))), xs) : Bool}:
  internal_any_map_go(~A, ~B, ~f, ~p, xs, False{})

def internal_order_go_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def internal_order_go_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def internal_cmp_rec_snd(h1: Char, h2: Char, rr: (String & String) & Cmp) -> {Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, rr)) == Pair.snd(String & String, Cmp, rr) : Cmp}:
  match rr:
    case (ts, r):
      match ts:
        case (t1, t2):
          {==}

def internal_order_step(+t1: String, +t2: String, h1: Char, h2: Char, c: Cmp, ih: {String.order.go(t1, t2, EQ{}) == Pair.snd(String & String, Cmp, String.cmp(t1, t2)) : Cmp}) -> {String.order.go(t1, t2, c) == Pair.snd(String & String, Cmp, String.cmp.fin(t1, t2, ((h1, h2), c))) : Cmp}:
  match c:
    case LT{}:
      internal_order_go_lt(t1, t2)
    case EQ{}:
      Equal.trans(Cmp, String.order.go(t1, t2, EQ{}), Pair.snd(String & String, Cmp, String.cmp(t1, t2)), Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, String.cmp(t1, t2))), ih, Equal.sym(Cmp, Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, String.cmp(t1, t2))), Pair.snd(String & String, Cmp, String.cmp(t1, t2)), internal_cmp_rec_snd(h1, h2, String.cmp(t1, t2))))
    case GT{}:
      internal_order_go_gt(t1, t2)

def internal_order_cmp_go(+a: String, +b: String) -> {String.order(a, b) == Pair.snd(String & String, Cmp, String.cmp(a, b)) : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      internal_order_step(t1, t2, Chr{x}, Chr{y}, U32.cmp(x, y), internal_order_cmp_go(t1, t2))

def internal_order_cmp(+a: String, +b: String) -> {Pair.snd(String & String, Cmp, String.cmp(a, b)) == String.order(a, b) : Cmp}:
  Equal.sym(Cmp, String.order(a, b), Pair.snd(String & String, Cmp, String.cmp(a, b)), internal_order_cmp_go(a, b))

def main() -> Nat:
  0n
