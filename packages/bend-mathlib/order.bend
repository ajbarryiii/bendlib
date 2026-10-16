# bend-mathlib/order.bend: abstract preorder/total-order facts over a Bool comparator ~le.
import Base
import ./nat.bend as MNat

# A chain of three comparisons composes.
law le_trans3:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  for ab: {le(a, b) == True{} : Bool}
  for bc: {le(b, c) == True{} : Bool}
  for cd: {le(c, d) == True{} : Bool}
  {le(a, d) == True{} : Bool}

def le_trans3(A, le, le_trans, a, b, c, d, ab, bc, cd):
  le_trans(a, c, d, le_trans(a, b, c, ab, bc), cd)

# A chain of four comparisons composes.
law le_trans4:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  for +e: A
  for ab: {le(a, b) == True{} : Bool}
  for bc: {le(b, c) == True{} : Bool}
  for cd: {le(c, d) == True{} : Bool}
  for de: {le(d, e) == True{} : Bool}
  {le(a, e) == True{} : Bool}

def le_trans4(A, le, le_trans, a, b, c, d, e, ab, bc, cd, de):
  le_trans(a, d, e, le_trans3(A, le, le_trans, a, b, c, d, ab, bc, cd), de)

# Antisymmetry gives equality.
law le_antisymm_eq:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_antisymm: @x: A -> @y: A -> {le(x, y) == True{} : Bool} -> {le(y, x) == True{} : Bool} -> {x == y : A}
  for +a: A
  for +b: A
  for ab: {le(a, b) == True{} : Bool}
  for ba: {le(b, a) == True{} : Bool}
  {a == b : A}

def le_antisymm_eq(A, le, le_antisymm, a, b, ab, ba):
  le_antisymm(a, b, ab, ba)

# Totality as a Bool disjunction.
law le_total_true:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}
  for +a: A
  for +b: A
  {Bool.or(le(a, b), le(b, a)) == True{} : Bool}

def le_total_true(A, le, le_total, a, b):
  le_total(a, b)

def internal_or_of_false_right(a: Bool, b: Bool, h: {Bool.or(a, b) == True{} : Bool}, ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == True{} : Bool}, MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, ha)))

# The other side of a total order holds when one side fails.
law le_total_of_not_le:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}
  for +a: A
  for +b: A
  for h: {le(a, b) == False{} : Bool}
  {le(b, a) == True{} : Bool}

def le_total_of_not_le(A, le, le_total, a, b, h):
  internal_or_of_false_right(le(a, b), le(b, a), le_total(a, b), h)

# Nat calls of the laws above: --verdict takes a ~ constant's model from a call of its law (PLAN F38).
def internal_nat_le_total(a: Nat, b: Nat) -> {Bool.or(Nat.is_le(a, b), Nat.is_le(b, a)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      internal_nat_le_total(p, q)

def internal_nat_le_trans3(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: MNat.le(a, b), bc: MNat.le(b, c), cd: MNat.le(c, d)) -> MNat.le(a, d):
  le_trans3(~Nat, ~Nat.is_le, ~MNat.le_trans, a, b, c, d, ab, bc, cd)

def internal_nat_le_trans4(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, ab: MNat.le(a, b), bc: MNat.le(b, c), cd: MNat.le(c, d), de: MNat.le(d, e)) -> MNat.le(a, e):
  le_trans4(~Nat, ~Nat.is_le, ~MNat.le_trans, a, b, c, d, e, ab, bc, cd, de)

def internal_nat_le_antisymm_eq(+a: Nat, +b: Nat, ab: MNat.le(a, b), ba: MNat.le(b, a)) -> {a == b : Nat}:
  le_antisymm_eq(~Nat, ~Nat.is_le, ~MNat.le_antisymm, a, b, ab, ba)

def internal_nat_le_total_true(+a: Nat, +b: Nat) -> {Bool.or(Nat.is_le(a, b), Nat.is_le(b, a)) == True{} : Bool}:
  le_total_true(~Nat, ~Nat.is_le, ~internal_nat_le_total, a, b)

def internal_nat_le_total_of_not_le(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> MNat.le(b, a):
  le_total_of_not_le(~Nat, ~Nat.is_le, ~internal_nat_le_total, a, b, h)

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Totality as a Bool disjunction, reversed to rewrite toward the simple side.
law le_total_true_sym:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}
  for +a: A
  for +b: A
  {True{} == Bool.or(le(a, b), le(b, a)) : Bool}

def le_total_true_sym(A, le, le_total, a, b):
  Equal.sym(Bool, Bool.or(le(a, b), le(b, a)), True{}, le_total_true(~A, ~le, ~le_total, a, b))
