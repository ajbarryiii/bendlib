import Base
import ./rv1/pred.bend as P1

def wk_le(a: Nat, b: Nat, h: P1.le(a, b)) -> P1.le(a, b):
  h

def wk_allz(xs: List<&2, Nat>, h: P1.allz(xs)) -> P1.allz(xs):
  h

law allz_nil_r:
  for xs: List<&2, Nat>
  for h: P1.allz(xs)
  P1.allz(List.append(&2, Nat, xs, Nil{}))

def allz_nil_r(xs, h):
  match xs:
    case Nil{}:
      Unit{}
    case x <> t:
      (e, r) = h
      (e, allz_nil_r(t, r))

def two_zero() -> P1.allz([0n, 0n]):
  ({==}, ({==}, Unit{}))

def wk_isz(n: Nat, h: P1.isz(n)) -> P1.isz(n):
  h

def wk_add2(a: Nat, b: Nat, h: {P1.add2(a, b) == P1.add2(b, a) : Nat}) -> {P1.add2(a, b) == P1.add2(b, a) : Nat}:
  h

def wk_perm(xs: List<&2, Nat>, ys: List<&2, Nat>, h: P1.perm(xs, ys)) -> P1.perm(xs, ys):
  h

def bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

# Base 2.0.38 short-circuits List.all through List.all.if (PLAN F39), so the tail is split off by cases on the head's test.
law all_if_elim:
  for b: Bool
  for -r: Bool
  for h: {List.all.if(u => r, b) == True{} : Bool}
  {r == True{} : Bool}

def all_if_elim(b, r, h):
  match b:
    case False{}:
      Empty.absurd({r == True{} : Bool}, false_ne_true(h))
    case True{}:
      h

# inversion: sorted_b(x <> t) -> sorted_b(t), proved against version 1
law sorted_b_tail:
  for +x: Nat
  for +t: List<&2, Nat>
  for h: P1.sorted_b(~Nat, ~Nat.is_le, x <> t)
  P1.sorted_b(~Nat, ~Nat.is_le, t)

def sorted_b_tail(x, t, h):
  match t:
    case Nil{}:
      {==}
    case +y <> +r:
      all_if_elim(Nat.is_le(x, y), List.all(~&1, ~(Nat & Nat), ~(p => P1.adj_le(~Nat, ~Nat.is_le, p)), List.zip(&2, Nat, &2, Nat, y <> r, r)), h)

def wk_mem(x: Nat, xs: List<&2, Nat>, h: P1.mem(~Nat, ~Nat.is_eq, x, xs)) -> P1.mem(~Nat, ~Nat.is_eq, x, xs):
  h
