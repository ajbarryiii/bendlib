# bend-mathlib/nat.bend: Nat arithmetic (add, mul, sub, div, mod, min, max, pow, double) and order
# (le, lt, ge, gt).
import Base

# Zero is a right identity for addition: x + 0 = x.
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# Zero is a left identity for addition: 0 + x = x.
law zero_add:
  for -x: Nat
  {Nat.add(0n, x) == x : Nat}

def zero_add(x):
  {==}

# Adding a successor on the right: n + (m + 1) = (n + m) + 1.
law add_succ:
  for n: Nat
  for -m: Nat
  {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}

def add_succ(n, m):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

# Adding a successor on the left: (n + 1) + m = (n + m) + 1.
law succ_add:
  for -n: Nat
  for -m: Nat
  {Nat.add(1n+n, m) == 1n+Nat.add(n, m) : Nat}

def succ_add(n, m):
  {==}

# Addition is commutative: n + m = m + n.
law add_comm:
  for n: Nat
  for m: Nat
  {Nat.add(n, m) == Nat.add(m, n) : Nat}

def add_comm(n, m):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %add_zero(q) : {1n+_ == 1n+Nat.add(q, 0n) : Nat}
      {==}
    case 1n+p 0n:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), add_succ(p, q)) : {1n+_ == 1n+Nat.add(q, 1n+p) : Nat}
      %Equal.sym(Nat, Nat.add(q, 1n+p), 1n+Nat.add(q, p), add_succ(q, p)) : {2n+Nat.add(p, q) == 1n+_ : Nat}
      %add_comm(p, q) : {2n+Nat.add(p, q) == 2n+_ : Nat}
      {==}

# Addition is associative: (a + b) + c = a + (b + c).
law add_assoc:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# Left commutativity of addition: a + (b + c) = b + (a + c).
law add_left_comm:
  for a: Nat
  for b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_left_comm(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +b = b
      %Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), add_succ(b, Nat.add(p, c))) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      %add_left_comm(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# Right commutativity of addition: (a + b) + c = (a + c) + b.
law add_right_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def add_right_comm(a, b, c):
  match a:
    case 0n:
      add_comm(b, c)
    case 1n+p:
      %add_right_comm(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d).
law add_add_add_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  for -d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def add_add_add_comm(a, b, c, d):
  match a:
    case 0n:
      add_left_comm(b, c, d)
    case 1n+p:
      %add_add_add_comm(p, b, c, d) : {1n+Nat.add(Nat.add(p, b), Nat.add(c, d)) == 1n+_ : Nat}
      {==}

def internal_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# The successor function is injective: a + 1 = b + 1 implies a = b.
law succ_inj:
  for -a: Nat
  for -b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  %e : {a == internal_pred(_) : Nat}
  {==}

def internal_zero_ne_succ(-n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  %e : Bool.pick(Type, Nat.is_eq(_, 0n), Unit, Empty)
  Unit{}

# Zero is not a successor.
law zero_ne_succ:
  for -n: Nat
  {0n != 1n+n : Nat}

def zero_ne_succ(n):
  e => internal_zero_ne_succ(n, e)

def internal_succ_ne_zero(-n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  %e : Bool.pick(Type, Nat.is_eq(_, 0n), Empty, Unit)
  Unit{}

# A successor is not zero.
law succ_ne_zero:
  for -n: Nat
  {1n+n != 0n : Nat}

def succ_ne_zero(n):
  e => internal_succ_ne_zero(n, e)

# Addition cancels on the left: a + b = a + c implies b = c.
law add_left_cancel:
  for a: Nat
  for -b: Nat
  for -c: Nat
  for e: {Nat.add(a, b) == Nat.add(a, c) : Nat}
  {b == c : Nat}

def add_left_cancel(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+p:
      add_left_cancel(p, b, c, succ_inj(Nat.add(p, b), Nat.add(p, c), e))

# Addition cancels on the right: a + b = c + b implies a = c.
law add_right_cancel:
  for a: Nat
  for b: Nat
  for c: Nat
  for e: {Nat.add(a, b) == Nat.add(c, b) : Nat}
  {a == c : Nat}

def add_right_cancel(a, b, c, e):
  +b = b
  add_left_cancel(b, a, c, Equal.trans(Nat, Nat.add(b, a), Nat.add(a, b), Nat.add(b, c), add_comm(b, a), Equal.trans(Nat, Nat.add(a, b), Nat.add(c, b), Nat.add(b, c), e, add_comm(c, b))))

# Zero absorbs multiplication on the right: x * 0 = 0.
law mul_zero:
  for x: Nat
  {Nat.mul(x, 0n) == 0n : Nat}

def mul_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

# Zero absorbs multiplication on the left: 0 * x = 0.
law zero_mul:
  for -x: Nat
  {Nat.mul(0n, x) == 0n : Nat}

def zero_mul(x):
  {==}

# One is a right identity for multiplication: x * 1 = x.
law mul_one:
  for x: Nat
  {Nat.mul(x, 1n) == x : Nat}

def mul_one(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

# One is a left identity for multiplication: 1 * x = x.
law one_mul:
  for x: Nat
  {Nat.mul(1n, x) == x : Nat}

def one_mul(x):
  add_zero(x)

# Multiplying by a successor on the right: n * (m + 1) = n * m + n.
law mul_succ:
  for n: Nat
  for m: Nat
  {Nat.mul(n, 1n+m) == Nat.add(Nat.mul(n, m), n) : Nat}

def mul_succ(n, m):
  match n:
    case 0n:
      {==}
    case 1n++p:
      +m = m
      %Equal.sym(Nat, Nat.add(Nat.add(m, Nat.mul(p, m)), 1n+p), 1n+Nat.add(Nat.add(m, Nat.mul(p, m)), p), add_succ(Nat.add(m, Nat.mul(p, m)), p)) : {1n+Nat.add(m, Nat.mul(p, 1n+m)) == _ : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(m, Nat.mul(p, m)), p), Nat.add(m, Nat.add(Nat.mul(p, m), p)), add_assoc(m, Nat.mul(p, m), p)) : {1n+Nat.add(m, Nat.mul(p, 1n+m)) == 1n+_ : Nat}
      %mul_succ(p, m) : {1n+Nat.add(m, Nat.mul(p, 1n+m)) == 1n+Nat.add(m, _) : Nat}
      {==}

# Multiplying by a successor on the left: (n + 1) * m = n * m + m.
law succ_mul:
  for n: Nat
  for m: Nat
  {Nat.mul(1n+n, m) == Nat.add(Nat.mul(n, m), m) : Nat}

def succ_mul(n, m):
  +m = m
  add_comm(m, Nat.mul(n, m))

# Multiplication is commutative: n * m = m * n.
law mul_comm:
  for n: Nat
  for m: Nat
  {Nat.mul(n, m) == Nat.mul(m, n) : Nat}

def mul_comm(n, m):
  match n:
    case 0n:
      %mul_zero(m) : {_ == Nat.mul(m, 0n) : Nat}
      {==}
    case 1n++p:
      +m = m
      %Equal.sym(Nat, Nat.mul(m, 1n+p), Nat.add(Nat.mul(m, p), m), mul_succ(m, p)) : {Nat.add(m, Nat.mul(p, m)) == _ : Nat}
      %mul_comm(p, m) : {Nat.add(m, Nat.mul(p, m)) == Nat.add(_, m) : Nat}
      add_comm(m, Nat.mul(p, m))

# Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c.
law add_mul:
  for a: Nat
  for -b: Nat
  for c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def add_mul(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +c = c
      %Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), add_assoc(c, Nat.mul(p, c), Nat.mul(b, c))) : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == _ : Nat}
      %add_mul(p, b, c) : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == Nat.add(c, _) : Nat}
      {==}

# Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c.
law mul_add:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

def mul_add(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n++p:
      +b = b
      +c = c
      %Equal.sym(Nat, Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)), mul_add(p, b, c)) : {Nat.add(Nat.add(b, c), _) == Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))) : Nat}
      add_add_add_comm(b, c, Nat.mul(p, b), Nat.mul(p, c))

# Multiplication is associative: (a * b) * c = a * (b * c).
law mul_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +b = b
      +c = c
      %mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      add_mul(b, Nat.mul(p, b), c)

# The order a <= b on naturals, as a reusable proposition.
def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

# The strict order a < b on naturals, as a reusable proposition.
def lt(a: Nat, b: Nat) -> Data:
  {Nat.is_lt(a, b) == True{} : Bool}

# The order a >= b on naturals, as a reusable proposition.
def ge(a: Nat, b: Nat) -> Data:
  {Nat.is_ge(a, b) == True{} : Bool}

# The strict order a > b on naturals, as a reusable proposition.
def gt(a: Nat, b: Nat) -> Data:
  {Nat.is_gt(a, b) == True{} : Bool}

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Every natural is at most itself: a <= a.
law le_refl:
  for a: Nat
  le(a, a)

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# Zero is at most every natural: 0 <= b.
law zero_le:
  for b: Nat
  le(0n, b)

def zero_le(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Every natural is at most its successor: n <= n + 1.
law le_succ:
  for n: Nat
  le(n, 1n+n)

def le_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

# Adding on the right never decreases a natural: n <= n + k.
law le_add_right:
  for n: Nat
  for k: Nat
  le(n, Nat.add(n, k))

def le_add_right(n, k):
  match n:
    case 0n:
      zero_le(k)
    case 1n+p:
      le_add_right(p, k)

# The order is transitive: a <= b and b <= c imply a <= c.
law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: le(a, b)
  for bc: le(b, c)
  le(a, c)

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd(le(1n+p, c), internal_false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd(le(1n+p, 0n), internal_false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

# The order is antisymmetric: a <= b and b <= a imply a = b.
law le_antisymm:
  for a: Nat
  for b: Nat
  for ab: le(a, b)
  for ba: le(b, a)
  {a == b : Nat}

def le_antisymm(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, internal_false_ne_true(ba))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, internal_false_ne_true(ab))
    case 1n+p 1n+q:
      %le_antisymm(p, q, ab, ba) : {1n+p == 1n+_ : Nat}
      {==}

# The order is total: a <= b or b <= a.
law le_total:
  for a: Nat
  for b: Nat
  Or(le(a, b), le(b, a))

def le_total(a, b):
  match a b:
    case 0n 0n:
      Inl{{==}}
    case 0n 1n+q:
      Inl{{==}}
    case 1n+p 0n:
      Inr{{==}}
    case 1n+p 1n+q:
      le_total(p, q)

# The order is total, as a reusable sum: a <= b or b <= a.
law le_total_d:
  for a: Nat
  for b: Nat
  Either<&2, &2, le(a, b), le(b, a)>

def le_total_d(a, b):
  match a b:
    case 0n 0n:
      Inl{{==}}
    case 0n 1n+q:
      Inl{{==}}
    case 1n+p 0n:
      Inr{{==}}
    case 1n+p 1n+q:
      le_total_d(p, q)

# No natural is less than itself.
law lt_irrefl:
  for a: Nat
  lt(a, a) -> Empty

def lt_irrefl(a):
  match a:
    case 0n:
      h => internal_false_ne_true(h)
    case 1n+p:
      lt_irrefl(p)

# The strict order is transitive: a < b and b < c imply a < c.
law lt_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: lt(a, b)
  for bc: lt(b, c)
  lt(a, c)

def lt_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd(lt(0n, c), internal_false_ne_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd(lt(1n+p, c), internal_false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd(lt(1n+p, 0n), internal_false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      lt_trans(p, q, r, ab, bc)

# A strict inequality implies the weak one: a < b implies a <= b.
law le_of_lt:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  le(a, b)

def le_of_lt(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd(le(1n+p, 0n), internal_false_ne_true(h))
    case 1n+p 1n+q:
      le_of_lt(p, q, h)

# Flipping a >= b gives b <= a.
law le_of_ge:
  for a: Nat
  for b: Nat
  for h: ge(a, b)
  le(b, a)

def le_of_ge(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd(le(1n+q, 0n), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_of_ge(p, q, h)

# Flipping b <= a gives a >= b.
law ge_of_le:
  for a: Nat
  for b: Nat
  for h: le(b, a)
  ge(a, b)

def ge_of_le(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd(ge(0n, 1n+q), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ge_of_le(p, q, h)

# Flipping a > b gives b < a.
law lt_of_gt:
  for a: Nat
  for b: Nat
  for h: gt(a, b)
  lt(b, a)

def lt_of_gt(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(h))
    case 0n 1n+q:
      Empty.absurd(lt(1n+q, 0n), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_of_gt(p, q, h)

# Flipping b < a gives a > b.
law gt_of_lt:
  for a: Nat
  for b: Nat
  for h: lt(b, a)
  gt(a, b)

def gt_of_lt(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd(gt(0n, 0n), internal_false_ne_true(h))
    case 0n 1n+q:
      Empty.absurd(gt(0n, 1n+q), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gt_of_lt(p, q, h)

# Subtracting zero changes nothing: n - 0 = n.
law sub_zero:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

def sub_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Truncated subtraction from zero is zero: 0 - n = 0.
law zero_sub:
  for n: Nat
  {Nat.sub(0n, n) == 0n : Nat}

def zero_sub(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# A natural minus itself is zero: n - n = 0.
law sub_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}

def sub_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# Subtracting successors: (n + 1) - (m + 1) = n - m.
law succ_sub_succ:
  for -n: Nat
  for -m: Nat
  {Nat.sub(1n+n, 1n+m) == Nat.sub(n, m) : Nat}

def succ_sub_succ(n, m):
  {==}

# Adding then subtracting m cancels: (n + m) - m = n.
law add_sub_cancel:
  for n: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, m), m) == n : Nat}

def add_sub_cancel(n, m):
  match m:
    case 0n:
      +n = n
      %Equal.sym(Nat, Nat.add(n, 0n), n, add_zero(n)) : {Nat.sub(_, 0n) == n : Nat}
      sub_zero(n)
    case 1n++q:
      +n = n
      %Equal.sym(Nat, Nat.add(n, 1n+q), 1n+Nat.add(n, q), add_succ(n, q)) : {Nat.sub(_, 1n+q) == n : Nat}
      add_sub_cancel(n, q)

# Adding then subtracting n cancels: (n + m) - n = m.
law add_sub_cancel_left:
  for n: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, m), n) == m : Nat}

def add_sub_cancel_left(n, m):
  match n:
    case 0n:
      sub_zero(m)
    case 1n+p:
      add_sub_cancel_left(p, m)

# If m <= n, subtracting and adding m back gives n: (n - m) + m = n.
law sub_add_cancel:
  for n: Nat
  for m: Nat
  for h: le(m, n)
  {Nat.add(Nat.sub(n, m), m) == n : Nat}

def sub_add_cancel(n, m, h):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({1n+q == 0n : Nat}, internal_false_ne_true(h))
    case 1n++p 0n:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), add_succ(Nat.sub(p, q), q)) : {_ == 1n+p : Nat}
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), q), p, sub_add_cancel(p, q, h)) : {1n+_ == 1n+p : Nat}
      {==}

# Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k).
law sub_sub:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(Nat.sub(n, m), k) == Nat.sub(n, Nat.add(m, k)) : Nat}

def sub_sub(n, m, k):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      zero_sub(k)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, k)

# Truncated subtraction never increases: n - m <= n.
law sub_le:
  for n: Nat
  for m: Nat
  le(Nat.sub(n, m), n)

def sub_le(n, m):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n++p 1n++q:
      le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), le_succ(p))

def internal_div_true_ne_false(h: {True{} == False{} : Bool}) -> Empty:
  internal_false_ne_true(Equal.sym(Bool, True{}, False{}, h))

def internal_div_add_zero_r(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(a, 0n), a, add_zero(a))

def internal_div_le_refl(a: Nat) -> {True{} == Nat.is_le(a, a) : Bool}:
  Equal.sym(Bool, Nat.is_le(a, a), True{}, le_refl(a))

def internal_div_zero_le(x: Nat) -> {True{} == Nat.is_le(0n, x) : Bool}:
  Equal.sym(Bool, Nat.is_le(0n, x), True{}, zero_le(x))

def internal_div_block_start(-bp: Nat, +r: Nat, h: {bp == Nat.add(r, 0n) : Nat}) -> {bp == r : Nat}:
  %add_zero(r) : {bp == _ : Nat}
  h

def internal_div_block_step(-bp: Nat, r: Nat, -mp: Nat, h: {bp == Nat.add(r, 1n+mp) : Nat}) -> {bp == 1n+Nat.add(r, mp) : Nat}:
  %add_succ(r, mp) : {bp == _ : Nat}
  h

def internal_div_go_eq(n: Nat, m: Nat, +bp: Nat, +d: Nat, +r: Nat, +h: {bp == Nat.add(r, m) : Nat}) -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n++np 0n:
      %add_succ(np, Nat.add(Nat.mul(d, 1n+bp), r)) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))) == _ : Nat}
      %add_comm(r, Nat.mul(d, 1n+bp)) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))) == Nat.add(np, 1n+_) : Nat}
      %internal_div_block_start(bp, r, h) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))) == Nat.add(np, 1n+Nat.add(_, Nat.mul(d, 1n+bp))) : Nat}
      %add_zero(Nat.add(bp, Nat.mul(d, 1n+bp))) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))) == Nat.add(np, 1n+_) : Nat}
      internal_div_go_eq(np, r, bp, 1n+d, 0n, internal_div_block_start(bp, r, h))
    case 1n++np 1n++mp:
      %add_succ(np, Nat.add(Nat.mul(d, 1n+bp), r)) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))) == _ : Nat}
      %add_succ(Nat.mul(d, 1n+bp), r) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))) == Nat.add(np, _) : Nat}
      internal_div_go_eq(np, mp, bp, d, 1n+r, internal_div_block_step(bp, r, mp, h))

# The division equation, for a positive divisor 1 + b: (a / (1 + b)) * (1 + b) + a % (1 + b) = a.
law div_mod_eq:
  for +a: Nat
  for +b: Nat
  {Nat.add(Nat.mul(Nat.div(a, 1n+b), 1n+b), Nat.mod(a, 1n+b)) == a : Nat}

def div_mod_eq(a, b):
  %add_zero(a) : {Nat.add(Nat.mul(Nat.div(a, 1n+b), 1n+b), Nat.mod(a, 1n+b)) == _ : Nat}
  internal_div_go_eq(a, b, b, 0n, 0n, {==})

def internal_div_wit_succ(+ap: Nat, +bq: Nat, w: &k:Nat -> {Nat.add(ap, k) == bq : Nat}) -> &k:Nat -> {Nat.add(1n+ap, k) == 1n+bq : Nat}:
  match w:
    case (k, e):
      (k, Equal.cong(Nat, Nat, x => 1n+x, Nat.add(ap, k), bq, e))

def internal_div_le_wit(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> &k:Nat -> {Nat.add(a, k) == b : Nat}:
  match a b:
    case 0n y:
      (y, {==})
    case 1n+ap 0n:
      Empty.absurd(&k:Nat -> {Nat.add(1n+ap, k) == 0n : Nat}, internal_false_ne_true(h))
    case 1n++ap 1n++bq:
      internal_div_wit_succ(ap, bq, internal_div_le_wit(ap, bq, h))

def internal_div_go_small(n: Nat, +k: Nat, +d: Nat, r: Nat) -> {d == Pair.fst(Nat, Nat, Nat.divmod.go(n, Nat.add(n, k), d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      internal_div_go_small(np, k, d, 1n+r)

def internal_div_zero_of_wit(+a: Nat, +b: Nat, w: &k:Nat -> {Nat.add(a, k) == b : Nat}) -> {Nat.div(a, 1n+b) == 0n : Nat}:
  match w:
    case (+k, e):
      %e : {Nat.div(a, 1n+_) == 0n : Nat}
      Equal.sym(Nat, 0n, Pair.fst(Nat, Nat, Nat.divmod.go(a, Nat.add(a, k), 0n, 0n)), internal_div_go_small(a, k, 0n, 0n))

# A number at most b divides by 1 + b to zero: a <= b implies a / (1 + b) = 0.
law div_eq_zero_of_le:
  for +a: Nat
  for +b: Nat
  for h: le(a, b)
  {Nat.div(a, 1n+b) == 0n : Nat}

def div_eq_zero_of_le(a, b, h):
  internal_div_zero_of_wit(a, b, internal_div_le_wit(a, b, h))

def internal_div_le_succ_r(j: Nat, d: Nat, h: {True{} == Nat.is_le(j, d) : Bool}) -> {True{} == Nat.is_le(j, 1n+d) : Bool}:
  match j d:
    case 0n _:
      {==}
    case 1n+i 0n:
      Empty.absurd({True{} == Nat.is_le(1n+i, 1n) : Bool}, internal_div_true_ne_false(h))
    case 1n+i 1n+e:
      internal_div_le_succ_r(i, e, h)

def internal_div_go_d_ge(+j: Nat, n: Nat, m: Nat, +d: Nat, r: Nat, h: {True{} == Nat.is_le(j, d) : Bool}) -> {True{} == Nat.is_le(j, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) : Bool}:
  match n m:
    case 0n _:
      h
    case 1n+np 0n:
      internal_div_go_d_ge(j, np, r, 1n+d, 0n, internal_div_le_succ_r(j, d, h))
    case 1n+np 1n+mp:
      internal_div_go_d_ge(j, np, mp, d, 1n+r, h)

def internal_div_mono_go(a: Nat, m: Nat, +d: Nat, r: Nat, +k: Nat) -> {True{} == Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(a, m, d, r)), Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(a, k), m, d, r))) : Bool}:
  match a m:
    case 0n _:
      internal_div_go_d_ge(d, k, m, d, r, internal_div_le_refl(d))
    case 1n+ap 0n:
      internal_div_mono_go(ap, r, 1n+d, 0n, k)
    case 1n+ap 1n+mp:
      internal_div_mono_go(ap, mp, d, 1n+r, k)

def internal_div_mono_wit(+a: Nat, +c: Nat, b: Nat, w: &k:Nat -> {Nat.add(a, k) == c : Nat}) -> le(Nat.div(a, 1n+b), Nat.div(c, 1n+b)):
  match w:
    case (+k, e):
      %e : le(Nat.div(a, 1n+b), Nat.div(_, 1n+b))
      Equal.sym(Bool, True{}, Nat.is_le(Nat.div(a, 1n+b), Nat.div(Nat.add(a, k), 1n+b)), internal_div_mono_go(a, b, 0n, 0n, k))

# Division by a positive divisor is monotone: a <= c implies a / (1 + b) <= c / (1 + b).
law div_le_div:
  for +a: Nat
  for +c: Nat
  for b: Nat
  for h: le(a, c)
  le(Nat.div(a, 1n+b), Nat.div(c, 1n+b))

def div_le_div(a, c, b, h):
  internal_div_mono_wit(a, c, b, internal_div_le_wit(a, c, h))

def internal_div_go_shift(n: Nat, m: Nat, +d: Nat, +r: Nat) -> {1n+Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      internal_div_go_shift(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      internal_div_go_shift(np, mp, d, 1n+r)

def internal_div_go_run(m: Nat, +a: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(a, Nat.add(m, r), 1n+d, 0n) == Nat.divmod.go(Nat.add(1n+m, a), m, d, r) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n++mp:
      %add_succ(mp, r) : {Nat.divmod.go(a, _, 1n+d, 0n) == Nat.divmod.go(1n+Nat.add(mp, a), mp, d, 1n+r) : Nat & Nat}
      internal_div_go_run(mp, a, d, 1n+r)

# Adding the divisor adds one to the quotient: ((1 + b) + a) / (1 + b) = 1 + a / (1 + b).
law add_div_left:
  for +a: Nat
  for +b: Nat
  {Nat.div(Nat.add(1n+b, a), 1n+b) == 1n+Nat.div(a, 1n+b) : Nat}

def add_div_left(a, b):
  %internal_div_go_run(b, a, 0n, 0n) : {Pair.fst(Nat, Nat, _) == 1n+Nat.div(a, 1n+b) : Nat}
  %internal_div_add_zero_r(b) : {Pair.fst(Nat, Nat, Nat.divmod.go(a, _, 1n, 0n)) == 1n+Nat.div(a, 1n+b) : Nat}
  Equal.sym(Nat, 1n+Nat.div(a, 1n+b), Pair.fst(Nat, Nat, Nat.divmod.go(a, b, 1n, 0n)), internal_div_go_shift(a, b, 0n, 0n))

def internal_div_le_add_cancel(t: Nat, +x: Nat, +y: Nat) -> {Nat.is_le(x, y) == Nat.is_le(Nat.add(t, x), Nat.add(t, y)) : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+tp:
      internal_div_le_add_cancel(tp, x, y)

def internal_div_gt_add(a: Nat, +y: Nat) -> {False{} == Nat.is_le(1n+Nat.add(a, y), a) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      internal_div_gt_add(ap, y)

def internal_div_not_succ_le(a: Nat, bp: Nat, h: {False{} == Nat.is_le(1n+bp, a) : Bool}) -> {Nat.is_le(a, bp) == True{} : Bool}:
  match a bp:
    case 0n q:
      Equal.sym(Bool, True{}, Nat.is_le(0n, q), internal_div_zero_le(q))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, internal_div_true_ne_false(Equal.sym(Bool, False{}, True{}, Equal.trans(Bool, False{}, Nat.is_le(0n, ap), True{}, h, Equal.sym(Bool, True{}, Nat.is_le(0n, ap), internal_div_zero_le(ap))))))
    case 1n+ap 1n+q:
      internal_div_not_succ_le(ap, q, h)

def internal_div_le_big(+np: Nat, +a: Nat, +bp: Nat, w: &k:Nat -> {Nat.add(1n+bp, k) == a : Nat}, ih: @x:Nat -> {Nat.is_le(np, Nat.div(x, 1n+bp)) == Nat.is_le(Nat.mul(np, 1n+bp), x) : Bool}) -> {Nat.is_le(1n+np, Nat.div(a, 1n+bp)) == Nat.is_le(Nat.mul(1n+np, 1n+bp), a) : Bool}:
  match w:
    case (+k, e):
      %e : {Nat.is_le(1n+np, Nat.div(_, 1n+bp)) == Nat.is_le(1n+Nat.add(bp, Nat.mul(np, 1n+bp)), _) : Bool}
      %internal_div_le_add_cancel(bp, Nat.mul(np, 1n+bp), k) : {Nat.is_le(1n+np, Nat.div(1n+Nat.add(bp, k), 1n+bp)) == _ : Bool}
      %Equal.sym(Nat, Nat.div(Nat.add(1n+bp, k), 1n+bp), 1n+Nat.div(k, 1n+bp), add_div_left(k, bp)) : {Nat.is_le(1n+np, _) == Nat.is_le(Nat.mul(np, 1n+bp), k) : Bool}
      ih(k)

def internal_div_le_small(+np: Nat, +a: Nat, +bp: Nat, w: &k:Nat -> {Nat.add(a, k) == bp : Nat}) -> {Nat.is_le(1n+np, Nat.div(a, 1n+bp)) == Nat.is_le(Nat.mul(1n+np, 1n+bp), a) : Bool}:
  match w:
    case (+k, e):
      %e : {Nat.is_le(1n+np, Nat.div(a, 1n+_)) == Nat.is_le(1n+Nat.add(_, Nat.mul(np, 1n+_)), a) : Bool}
      %internal_div_go_small(a, k, 0n, 0n) : {Nat.is_le(1n+np, _) == Nat.is_le(1n+Nat.add(Nat.add(a, k), Nat.mul(np, 1n+Nat.add(a, k))), a) : Bool}
      %Equal.sym(Nat, Nat.add(Nat.add(a, k), Nat.mul(np, 1n+Nat.add(a, k))), Nat.add(a, Nat.add(k, Nat.mul(np, 1n+Nat.add(a, k)))), add_assoc(a, k, Nat.mul(np, 1n+Nat.add(a, k)))) : {False{} == Nat.is_le(1n+_, a) : Bool}
      internal_div_gt_add(a, Nat.add(k, Nat.mul(np, 1n+Nat.add(a, k))))

def internal_div_le_step(+np: Nat, +a: Nat, +bp: Nat, b: Bool, eb: {b == Nat.is_le(1n+bp, a) : Bool}, ih: @x:Nat -> {Nat.is_le(np, Nat.div(x, 1n+bp)) == Nat.is_le(Nat.mul(np, 1n+bp), x) : Bool}) -> {Nat.is_le(1n+np, Nat.div(a, 1n+bp)) == Nat.is_le(Nat.mul(1n+np, 1n+bp), a) : Bool}:
  match b:
    case True{}:
      internal_div_le_big(np, a, bp, internal_div_le_wit(1n+bp, a, Equal.sym(Bool, True{}, Nat.is_le(1n+bp, a), eb)), ih)
    case False{}:
      internal_div_le_small(np, a, bp, internal_div_le_wit(a, bp, internal_div_not_succ_le(a, bp, eb)))

# A quotient is compared by multiplying back: n <= a / (1 + b) tests as n * (1 + b) <= a.
law le_div_iff_mul_le:
  for n: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(n, Nat.div(a, 1n+b)) == Nat.is_le(Nat.mul(n, 1n+b), a) : Bool}

def le_div_iff_mul_le(n, a, b):
  match n:
    case 0n:
      %internal_div_zero_le(Nat.div(a, 1n+b)) : {_ == Nat.is_le(0n, a) : Bool}
      %internal_div_zero_le(a) : {True{} == _ : Bool}
      {==}
    case 1n++np:
      internal_div_le_step(np, a, b, Nat.is_le(1n+b, a), {==}, x => le_div_iff_mul_le(np, x, b))

# Minimum is commutative.
law min_comm:
  for a: Nat
  for b: Nat
  {Nat.min(a, b) == Nat.min(b, a) : Nat}

def min_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %min_comm(p, q) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# Maximum is commutative.
law max_comm:
  for a: Nat
  for b: Nat
  {Nat.max(a, b) == Nat.max(b, a) : Nat}

def max_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %max_comm(p, q) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

# The minimum of a natural and itself is itself.
law min_self:
  for a: Nat
  {Nat.min(a, a) == a : Nat}

def min_self(a):
  match a:
    case 0n:
      {==}
    case 1n++p:
      %min_self(p) : {1n+Nat.min(p, p) == 1n+_ : Nat}
      {==}

# The maximum of a natural and itself is itself.
law max_self:
  for a: Nat
  {Nat.max(a, a) == a : Nat}

def max_self(a):
  match a:
    case 0n:
      {==}
    case 1n++p:
      %max_self(p) : {1n+Nat.max(p, p) == 1n+_ : Nat}
      {==}

# The minimum with zero is zero: min(a, 0) = 0.
law min_zero:
  for a: Nat
  {Nat.min(a, 0n) == 0n : Nat}

def min_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The minimum with zero is zero: min(0, a) = 0.
law zero_min:
  for a: Nat
  {Nat.min(0n, a) == 0n : Nat}

def zero_min(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Zero is an identity for maximum: max(a, 0) = a.
law max_zero:
  for a: Nat
  {Nat.max(a, 0n) == a : Nat}

def max_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Zero is an identity for maximum: max(0, a) = a.
law zero_max:
  for a: Nat
  {Nat.max(0n, a) == a : Nat}

def zero_max(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Minimum is associative.
law min_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(Nat.min(a, b), c) == Nat.min(a, Nat.min(b, c)) : Nat}

def min_assoc(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q 0n:
      {==}
    case 1n++p 1n++q 1n++r:
      %min_assoc(p, q, r) : {1n+Nat.min(Nat.min(p, q), r) == 1n+_ : Nat}
      {==}

# Maximum is associative.
law max_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}

def max_assoc(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q 0n:
      {==}
    case 1n++p 1n++q 1n++r:
      %max_assoc(p, q, r) : {1n+Nat.max(Nat.max(p, q), r) == 1n+_ : Nat}
      {==}

# The minimum plus the maximum is the sum: min(a, b) + max(a, b) = a + b.
law min_add_max:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.min(a, b), Nat.max(a, b)) == Nat.add(a, b) : Nat}

def min_add_max(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n++p 0n:
      %add_zero(p) : {1n+_ == 1n+Nat.add(p, 0n) : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.min(p, q), 1n+Nat.max(p, q)), 1n+Nat.add(Nat.min(p, q), Nat.max(p, q)), add_succ(Nat.min(p, q), Nat.max(p, q))) : {1n+_ == 1n+Nat.add(p, 1n+q) : Nat}
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), add_succ(p, q)) : {2n+Nat.add(Nat.min(p, q), Nat.max(p, q)) == 1n+_ : Nat}
      %min_add_max(p, q) : {2n+Nat.add(Nat.min(p, q), Nat.max(p, q)) == 2n+_ : Nat}
      {==}

# The minimum is at most its left argument.
law min_le_left:
  for a: Nat
  for b: Nat
  le(Nat.min(a, b), a)

def min_le_left(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_left(p, q)

# The minimum is at most its right argument.
law min_le_right:
  for a: Nat
  for b: Nat
  le(Nat.min(a, b), b)

def min_le_right(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_right(p, q)

# The left argument is at most the maximum.
law le_max_left:
  for a: Nat
  for b: Nat
  le(a, Nat.max(a, b))

def le_max_left(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n+p 1n+q:
      le_max_left(p, q)

# The right argument is at most the maximum.
law le_max_right:
  for a: Nat
  for b: Nat
  le(b, Nat.max(a, b))

def le_max_right(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      le_refl(1n+q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_max_right(p, q)

# Any natural to the power zero is one.
law pow_zero:
  for -a: Nat
  {Nat.pow(a, 0n) == 1n : Nat}

def pow_zero(a):
  {==}

# A power with a successor exponent: a^(n+1) = a * a^n.
law pow_succ:
  for -a: Nat
  for -n: Nat
  {Nat.pow(a, 1n+n) == Nat.mul(a, Nat.pow(a, n)) : Nat}

def pow_succ(a, n):
  {==}

# Any natural to the power one is itself.
law pow_one:
  for a: Nat
  {Nat.pow(a, 1n) == a : Nat}

def pow_one(a):
  mul_one(a)

# One to any power is one.
law one_pow:
  for n: Nat
  {Nat.pow(1n, n) == 1n : Nat}

def one_pow(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(1n, Nat.pow(1n, p)), Nat.pow(1n, p), one_mul(Nat.pow(1n, p))) : {_ == 1n : Nat}
      one_pow(p)

# Exponents add under multiplication: a^(m+n) = a^m * a^n.
law pow_add:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(a, Nat.add(m, n)) == Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) : Nat}

def pow_add(a, m, n):
  match m:
    case 0n:
      +a = a
      +n = n
      %Equal.sym(Nat, Nat.mul(1n, Nat.pow(a, n)), Nat.pow(a, n), one_mul(Nat.pow(a, n))) : {Nat.pow(a, n) == _ : Nat}
      {==}
    case 1n++p:
      +a = a
      +n = n
      %Equal.sym(Nat, Nat.pow(a, Nat.add(p, n)), Nat.mul(Nat.pow(a, p), Nat.pow(a, n)), pow_add(a, p, n)) : {Nat.mul(a, _) == Nat.mul(Nat.mul(a, Nat.pow(a, p)), Nat.pow(a, n)) : Nat}
      Equal.sym(Nat, Nat.mul(Nat.mul(a, Nat.pow(a, p)), Nat.pow(a, n)), Nat.mul(a, Nat.mul(Nat.pow(a, p), Nat.pow(a, n))), mul_assoc(a, Nat.pow(a, p), Nat.pow(a, n)))

# Doubling is adding a natural to itself.
law double_eq_add:
  for n: Nat
  {Nat.double(n) == Nat.add(n, n) : Nat}

def double_eq_add(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      %double_eq_add(p) : {2n+Nat.double(p) == 2n+_ : Nat}
      {==}

# Every natural tests equal to itself.
law is_eq_refl:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def is_eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      is_eq_refl(p)

# The equality test is symmetric.
law is_eq_comm:
  for a: Nat
  for b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

def is_eq_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %is_eq_comm(p, q) : {Nat.is_eq(p, q) == _ : Bool}
      {==}

# If the equality test says true, the naturals are equal.
law eq_of_is_eq:
  for a: Nat
  for b: Nat
  for h: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_of_is_eq(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, internal_false_ne_true(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, internal_false_ne_true(h))
    case 1n++p 1n++q:
      %eq_of_is_eq(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# A >= b tests the same as b <= a.
law is_ge_eq_is_le:
  for a: Nat
  for b: Nat
  {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}

def is_ge_eq_is_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %is_ge_eq_is_le(p, q) : {Nat.is_ge(p, q) == _ : Bool}
      {==}

# A > b tests the same as b < a.
law is_gt_eq_is_lt:
  for a: Nat
  for b: Nat
  {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}

def is_gt_eq_is_lt(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %is_gt_eq_is_lt(p, q) : {Nat.is_gt(p, q) == _ : Bool}
      {==}

# A < b tests the same as a + 1 <= b.
law is_lt_eq_succ_le:
  for a: Nat
  for b: Nat
  {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}

def is_lt_eq_succ_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      is_lt_eq_succ_le(p, q)

# Not (a <= b) tests the same as b < a.
law not_is_le:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_le(a, b)) == Nat.is_lt(b, a) : Bool}

def not_is_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_is_le(p, q)

# Not (a < b) tests the same as b <= a.
law not_is_lt:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}

def not_is_lt(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_is_lt(p, q)

# Every natural is less than its successor: n < n + 1.
law lt_succ_self:
  for n: Nat
  lt(n, 1n+n)

def lt_succ_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ_self(p)

# The successor preserves the order: a <= b implies a + 1 <= b + 1.
law succ_le_succ:
  for -a: Nat
  for -b: Nat
  for h: le(a, b)
  le(1n+a, 1n+b)

def succ_le_succ(a, b, h):
  h

# The order of successors is the order of the naturals: a + 1 <= b + 1 implies a <= b.
law le_of_succ_le_succ:
  for -a: Nat
  for -b: Nat
  for h: le(1n+a, 1n+b)
  le(a, b)

def le_of_succ_le_succ(a, b, h):
  h

# A < b and b <= c imply a < c.
law lt_of_lt_of_le:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: lt(a, b)
  for bc: le(b, c)
  lt(a, c)

def lt_of_lt_of_le(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd(lt(0n, c), internal_false_ne_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd(lt(1n+p, c), internal_false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd(lt(1n+p, 0n), internal_false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      lt_of_lt_of_le(p, q, r, ab, bc)

# A <= b and b < c imply a < c.
law lt_of_le_of_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: le(a, b)
  for bc: lt(b, c)
  lt(a, c)

def lt_of_le_of_lt(a, b, c, ab, bc):
  match a b c:
    case 0n 0n 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(bc))
    case 0n 1n+q 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(bc))
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd(lt(1n+p, c), internal_false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd(lt(1n+p, 0n), internal_false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      lt_of_le_of_lt(p, q, r, ab, bc)

# Adding on the left preserves the order: a <= b implies k + a <= k + b.
law add_le_add_left:
  for -a: Nat
  for -b: Nat
  for k: Nat
  for h: le(a, b)
  le(Nat.add(k, a), Nat.add(k, b))

def add_le_add_left(a, b, k, h):
  match k:
    case 0n:
      h
    case 1n+p:
      add_le_add_left(a, b, p, h)

# Adding on the right preserves the order: a <= b implies a + k <= b + k.
law add_le_add_right:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for h: le(a, b)
  le(Nat.add(a, k), Nat.add(b, k))

def add_le_add_right(a, b, k, h):
  %add_comm(k, a) : le(_, Nat.add(b, k))
  %add_comm(k, b) : le(Nat.add(k, a), _)
  add_le_add_left(a, b, k, h)

# Adding the same amount on the left does not change the order test: a <= b tests as k + a <= k + b.
law add_le_add_iff_left:
  for k: Nat
  for -a: Nat
  for -b: Nat
  {Nat.is_le(a, b) == Nat.is_le(Nat.add(k, a), Nat.add(k, b)) : Bool}

def add_le_add_iff_left(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+p:
      add_le_add_iff_left(p, a, b)

# Adding two bounded summands stays bounded: a <= c and b <= d imply a + b <= c + d.
law add_le_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for h1: le(a, c)
  for h2: le(b, d)
  le(Nat.add(a, b), Nat.add(c, d))

def add_le_add(a, b, c, d, h1, h2):
  le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), add_le_add_right(a, c, b, h1), add_le_add_left(b, d, c, h2))

# A sum is at most c exactly when a <= c and b <= c - a: a + b <= c tests as both.
law le_and_le_sub_iff_add_le:
  for a: Nat
  for -b: Nat
  for c: Nat
  {Bool.and(Nat.is_le(a, c), Nat.is_le(b, Nat.sub(c, a))) == Nat.is_le(Nat.add(a, b), c) : Bool}

def le_and_le_sub_iff_add_le(a, b, c):
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      le_and_le_sub_iff_add_le(i, b, j)

# The only natural at most zero is zero.
law le_zero_eq:
  for n: Nat
  for h: le(n, 0n)
  {n == 0n : Nat}

def le_zero_eq(n, h):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, internal_false_ne_true(h))

# No natural is less than zero.
law lt_zero:
  for n: Nat
  lt(n, 0n) -> Empty

def lt_zero(n):
  match n:
    case 0n:
      h => internal_false_ne_true(h)
    case 1n+p:
      h => internal_false_ne_true(h)

# A strict inequality rules out the reverse weak one: a < b implies b <= a is false.
law not_le_of_lt:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  {Nat.is_le(b, a) == False{} : Bool}

def not_le_of_lt(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, internal_false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, internal_false_ne_true(h))
    case 1n+p 1n+q:
      not_le_of_lt(p, q, h)

# A weak inequality rules out the reverse strict one: a <= b implies b < a is false.
law not_lt_of_le:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  {Nat.is_lt(b, a) == False{} : Bool}

def not_lt_of_le(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, internal_false_ne_true(h))
    case 1n+p 1n+q:
      not_lt_of_le(p, q, h)

# A failed weak test gives the reverse strict order: a <= b false implies b < a.
law lt_of_not_le:
  for a: Nat
  for b: Nat
  for h: {Nat.is_le(a, b) == False{} : Bool}
  lt(b, a)

def lt_of_not_le(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n+q:
      Empty.absurd(lt(1n+q, 0n), internal_false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_of_not_le(p, q, h)

# A failed strict test gives the reverse weak order: a < b false implies b <= a.
law le_of_not_lt:
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(a, b) == False{} : Bool}
  le(b, a)

def le_of_not_lt(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd(le(1n+q, 0n), internal_false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_of_not_lt(p, q, h)

# A number below both bounds is below their minimum: a < b and a < c imply a < min b c.
law lt_min:
  for a: Nat
  for b: Nat
  for c: Nat
  for hb: lt(a, b)
  for hc: lt(a, c)
  lt(a, Nat.min(b, c))

def lt_min(a, b, c, hb, hc):
  match a b c:
    case _ 0n _:
      Empty.absurd(lt(a, Nat.min(0n, c)), lt_zero(a)(hb))
    case _ 1n+q 0n:
      Empty.absurd(lt(a, Nat.min(1n+q, 0n)), lt_zero(a)(hc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      lt_min(p, q, r, hb, hc)

def internal_or_true_sym(x: Bool) -> {True{} == Bool.or(x, True{}) : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_or_false_sym(x: Bool) -> {x == Bool.or(x, False{}) : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# The minimum is at most c exactly when one argument is: min a b <= c tests as a <= c or b <= c.
law min_le_iff:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_le(Nat.min(a, b), c) == Bool.or(Nat.is_le(a, c), Nat.is_le(b, c)) : Bool}

def min_le_iff(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      internal_or_true_sym(Nat.is_le(p, r))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      min_le_iff(p, q, r)

# The maximum is above a exactly when one argument is: a < max b c tests as a < b or a < c.
law lt_max_iff:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_lt(a, Nat.max(b, c)) == Bool.or(Nat.is_lt(a, b), Nat.is_lt(a, c)) : Bool}

def lt_max_iff(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      internal_or_false_sym(Nat.is_lt(p, q))
    case 1n+p 1n+q 1n+r:
      lt_max_iff(p, q, r)

# Subtracting a larger number gives zero: a <= b implies a - b = 0.
law sub_eq_zero_of_le:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  {Nat.sub(a, b) == 0n : Nat}

def sub_eq_zero_of_le(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, internal_false_ne_true(h))
    case 1n+p 1n+q:
      sub_eq_zero_of_le(p, q, h)

# Above the subtrahend, a successor subtracts to a successor: b <= a implies (a + 1) - b = (a - b) + 1.
law succ_sub:
  for a: Nat
  for b: Nat
  for h: le(b, a)
  {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}

def succ_sub(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, internal_false_ne_true(h))
    case 1n+p 1n+q:
      succ_sub(p, q, h)

# Adding back what was subtracted restores the number: a <= b implies a + (b - a) = b.
law add_sub_of_le:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  {Nat.add(a, Nat.sub(b, a)) == b : Nat}

def add_sub_of_le(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, internal_false_ne_true(h))
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(p, Nat.sub(q, p)), q, add_sub_of_le(p, q, h)) : {1n+_ == 1n+q : Nat}
      {==}

def internal_lt_sub_zero(a: Nat, p: Nat) -> {Nat.is_lt(a, Nat.sub(0n, 1n+p)) == Nat.is_lt(Nat.add(1n+p, a), 0n) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+x:
      {==}

# Comparing against a difference is comparing the sum: a < c - b tests as b + a < c.
law lt_sub_iff_add_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_lt(a, Nat.sub(c, b)) == Nat.is_lt(Nat.add(b, a), c) : Bool}

def lt_sub_iff_add_lt(a, b, c):
  match b c:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+p 0n:
      internal_lt_sub_zero(a, p)
    case 1n+p 1n+r:
      lt_sub_iff_add_lt(a, p, r)

# A witnessed difference gives the order: a + k = b implies a <= b.
law le_of_add_eq:
  for a: Nat
  for k: Nat
  for -b: Nat
  for e: {Nat.add(a, k) == b : Nat}
  le(a, b)

def le_of_add_eq(a, k, b, e):
  %e : {Nat.is_le(a, _) == True{} : Bool}
  le_add_right(a, k)

# Multiplying on the right preserves the order: a <= b implies a * k <= b * k.
law mul_le_mul_right:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for h: le(a, b)
  le(Nat.mul(a, k), Nat.mul(b, k))

def mul_le_mul_right(a, b, k, h):
  %sub_add_cancel(b, a, h) : {Nat.is_le(Nat.mul(a, k), Nat.mul(_, k)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.sub(b, a), a), k), Nat.add(Nat.mul(Nat.sub(b, a), k), Nat.mul(a, k)), add_mul(Nat.sub(b, a), a, k)) : {Nat.is_le(Nat.mul(a, k), _) == True{} : Bool}
  %add_comm(Nat.mul(a, k), Nat.mul(Nat.sub(b, a), k)) : {Nat.is_le(Nat.mul(a, k), _) == True{} : Bool}
  le_add_right(Nat.mul(a, k), Nat.mul(Nat.sub(b, a), k))

# Zero divided by anything is zero: 0 / b = 0.
law zero_div:
  for b: Nat
  {Nat.div(0n, b) == 0n : Nat}

def zero_div(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Zero modulo anything is zero: 0 % b = 0.
law zero_mod:
  for b: Nat
  {Nat.mod(0n, b) == 0n : Nat}

def zero_mod(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def internal_div_go_one(a: Nat, +d: Nat) -> {(Nat.add(a, d), 0n) == Nat.divmod.go(a, 0n, d, 0n) : Nat & Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %add_succ(p, d) : {(_, 0n) == Nat.divmod.go(p, 0n, 1n+d, 0n) : Nat & Nat}
      internal_div_go_one(p, 1n+d)

# Dividing by one changes nothing: a / 1 = a.
law div_one:
  for a: Nat
  {Nat.div(a, 1n) == a : Nat}

def div_one(a):
  +a = a
  %internal_div_go_one(a, 0n) : {Pair.fst(Nat, Nat, _) == a : Nat}
  add_zero(a)

# Any natural modulo one is zero: a % 1 = 0.
law mod_one:
  for a: Nat
  {Nat.mod(a, 1n) == 0n : Nat}

def mod_one(a):
  +a = a
  %internal_div_go_one(a, 0n) : {Pair.snd(Nat, Nat, _) == 0n : Nat}
  {==}

def internal_div_go_self(m: Nat, -d: Nat, -r: Nat) -> {(1n+d, 0n) == Nat.divmod.go(1n+m, m, d, r) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      internal_div_go_self(p, d, 1n+r)

# A natural modulo itself is zero: n % n = 0.
law mod_self:
  for n: Nat
  {Nat.mod(n, n) == 0n : Nat}

def mod_self(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %internal_div_go_self(p, 0n, 0n) : {Pair.snd(Nat, Nat, _) == 0n : Nat}
      {==}

# A positive natural divided by itself is one: (1 + b) / (1 + b) = 1.
law div_self:
  for b: Nat
  {Nat.div(1n+b, 1n+b) == 1n : Nat}

def div_self(b):
  +b = b
  %internal_div_go_self(b, 0n, 0n) : {Pair.fst(Nat, Nat, _) == 1n : Nat}
  {==}

def internal_mod_go_le(n: Nat, m: Nat, -d: Nat, +r: Nat) -> le(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), Nat.add(r, m)):
  match n m:
    case 0n k:
      le_add_right(r, k)
    case 1n++np 0n:
      %internal_div_add_zero_r(r) : le(Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), _)
      internal_mod_go_le(np, r, 1n+d, 0n)
    case 1n++np 1n++mp:
      %Equal.sym(Nat, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), add_succ(r, mp)) : le(Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), _)
      internal_mod_go_le(np, mp, d, 1n+r)

# A remainder is below its positive divisor: a % (1 + b) < 1 + b.
law mod_lt:
  for a: Nat
  for b: Nat
  lt(Nat.mod(a, 1n+b), 1n+b)

def mod_lt(a, b):
  +a = a
  +b = b
  %Equal.sym(Bool, Nat.is_lt(Nat.mod(a, 1n+b), 1n+b), Nat.is_le(1n+Nat.mod(a, 1n+b), 1n+b), is_lt_eq_succ_le(Nat.mod(a, 1n+b), 1n+b)) : {_ == True{} : Bool}
  internal_mod_go_le(a, b, 0n, 0n)

# A remainder never exceeds the dividend: a % b <= a.
law mod_le:
  for a: Nat
  for b: Nat
  le(Nat.mod(a, b), a)

def mod_le(a, b):
  match b:
    case 0n:
      le_refl(a)
    case 1n++bp:
      +a = a
      +bp = bp
      le_of_add_eq(Nat.mod(a, 1n+bp), Nat.mul(Nat.div(a, 1n+bp), 1n+bp), a, Equal.trans(Nat, Nat.add(Nat.mod(a, 1n+bp), Nat.mul(Nat.div(a, 1n+bp), 1n+bp)), Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)), a, add_comm(Nat.mod(a, 1n+bp), Nat.mul(Nat.div(a, 1n+bp), 1n+bp)), div_mod_eq(a, bp)))

def internal_div_le_self_eq(+q: Nat, +bp: Nat, +m: Nat, -a: Nat, e: {Nat.add(Nat.mul(q, 1n+bp), m) == a : Nat}) -> {Nat.add(q, Nat.add(Nat.mul(bp, q), m)) == a : Nat}:
  %e : {Nat.add(q, Nat.add(Nat.mul(bp, q), m)) == _ : Nat}
  %mul_comm(1n+bp, q) : {Nat.add(q, Nat.add(Nat.mul(bp, q), m)) == Nat.add(_, m) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(q, Nat.mul(bp, q)), m), Nat.add(q, Nat.add(Nat.mul(bp, q), m)), add_assoc(q, Nat.mul(bp, q), m))

# A quotient never exceeds the dividend: a / b <= a.
law div_le_self:
  for a: Nat
  for b: Nat
  le(Nat.div(a, b), a)

def div_le_self(a, b):
  match b:
    case 0n:
      zero_le(a)
    case 1n++bp:
      +a = a
      +bp = bp
      le_of_add_eq(Nat.div(a, 1n+bp), Nat.add(Nat.mul(bp, Nat.div(a, 1n+bp)), Nat.mod(a, 1n+bp)), a, internal_div_le_self_eq(Nat.div(a, 1n+bp), bp, Nat.mod(a, 1n+bp), a, div_mod_eq(a, bp)))

def internal_mod_go_small(n: Nat, -k: Nat, -d: Nat, +r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, Nat.add(n, k), d, r)) == Nat.add(n, r) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      %add_succ(np, r) : {Pair.snd(Nat, Nat, Nat.divmod.go(np, Nat.add(np, k), d, 1n+r)) == _ : Nat}
      internal_mod_go_small(np, k, d, 1n+r)

def internal_mod_eq_of_wit(+a: Nat, +b: Nat, w: &k:Nat -> {Nat.add(a, k) == b : Nat}) -> {Nat.mod(a, 1n+b) == a : Nat}:
  match w:
    case (+k, e):
      %e : {Nat.mod(a, 1n+_) == a : Nat}
      Equal.trans(Nat, Nat.mod(a, 1n+Nat.add(a, k)), Nat.add(a, 0n), a, internal_mod_go_small(a, k, 0n, 0n), add_zero(a))

# A number below the divisor is its own remainder: a < b implies a % b = a.
law mod_eq_of_lt:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  {Nat.mod(a, b) == a : Nat}

def mod_eq_of_lt(a, b, h):
  match b:
    case 0n:
      +a = a
      Empty.absurd({Nat.mod(a, 0n) == a : Nat}, lt_zero(a)(h))
    case 1n++bp:
      +a = a
      +bp = bp
      internal_mod_eq_of_wit(a, bp, internal_div_le_wit(a, bp, Equal.trans(Bool, Nat.is_le(1n+a, 1n+bp), Nat.is_lt(a, 1n+bp), True{}, Equal.sym(Bool, Nat.is_lt(a, 1n+bp), Nat.is_le(1n+a, 1n+bp), is_lt_eq_succ_le(a, 1n+bp)), h)))

# Taking a remainder twice is taking it once: (a % n) % n = a % n.
law mod_mod:
  for a: Nat
  for n: Nat
  {Nat.mod(Nat.mod(a, n), n) == Nat.mod(a, n) : Nat}

def mod_mod(a, n):
  match n:
    case 0n:
      {==}
    case 1n++b:
      +a = a
      +b = b
      mod_eq_of_lt(Nat.mod(a, 1n+b), 1n+b, mod_lt(a, b))

def internal_mod_go_d(n: Nat, m: Nat, -d: Nat, -e: Nat, r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, e, r)) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      internal_mod_go_d(np, r, 1n+d, 1n+e, 0n)
    case 1n+np 1n+mp:
      internal_mod_go_d(np, mp, d, e, 1n+r)

# Adding the divisor does not change the remainder: (b + a) % b = a % b.
law add_mod_left:
  for a: Nat
  for b: Nat
  {Nat.mod(Nat.add(b, a), b) == Nat.mod(a, b) : Nat}

def add_mod_left(a, b):
  match b:
    case 0n:
      {==}
    case 1n++bp:
      +a = a
      %internal_div_go_run(bp, a, 0n, 0n) : {Pair.snd(Nat, Nat, _) == Nat.mod(a, 1n+bp) : Nat}
      %internal_div_add_zero_r(bp) : {Pair.snd(Nat, Nat, Nat.divmod.go(a, _, 1n, 0n)) == Nat.mod(a, 1n+bp) : Nat}
      internal_mod_go_d(a, bp, 1n, 0n, 0n)

# Multiplying by a positive divisor then dividing by it cancels: (a * (1 + b)) / (1 + b) = a.
law mul_div_cancel:
  for a: Nat
  for b: Nat
  {Nat.div(Nat.mul(a, 1n+b), 1n+b) == a : Nat}

def mul_div_cancel(a, b):
  match a:
    case 0n:
      {==}
    case 1n++p:
      +b = b
      %Equal.sym(Nat, Nat.div(Nat.add(1n+b, Nat.mul(p, 1n+b)), 1n+b), 1n+Nat.div(Nat.mul(p, 1n+b), 1n+b), add_div_left(Nat.mul(p, 1n+b), b)) : {_ == 1n+p : Nat}
      %mul_div_cancel(p, b) : {1n+Nat.div(Nat.mul(p, 1n+b), 1n+b) == 1n+_ : Nat}
      {==}

# Multiplying on the left by a positive divisor then dividing by it cancels: ((1 + b) * a) / (1 + b) = a.
law mul_div_cancel_left:
  for a: Nat
  for b: Nat
  {Nat.div(Nat.mul(1n+b, a), 1n+b) == a : Nat}

def mul_div_cancel_left(a, b):
  +a = a
  +b = b
  %mul_comm(a, 1n+b) : {Nat.div(_, 1n+b) == a : Nat}
  mul_div_cancel(a, b)

# A multiple of b leaves no remainder modulo b: (a * b) % b = 0.
law mul_mod_left:
  for a: Nat
  for b: Nat
  {Nat.mod(Nat.mul(a, b), b) == 0n : Nat}

def mul_mod_left(a, b):
  match a b:
    case _ 0n:
      mul_zero(a)
    case 0n 1n+bp:
      {==}
    case 1n++p 1n++bp:
      Equal.trans(Nat, Nat.mod(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), 1n+bp), Nat.mod(Nat.mul(p, 1n+bp), 1n+bp), 0n, add_mod_left(Nat.mul(p, 1n+bp), 1n+bp), mul_mod_left(p, 1n+bp))

# A multiple of a leaves no remainder modulo a: (a * b) % a = 0.
law mul_mod_right:
  for a: Nat
  for b: Nat
  {Nat.mod(Nat.mul(a, b), a) == 0n : Nat}

def mul_mod_right(a, b):
  +a = a
  +b = b
  %mul_comm(b, a) : {Nat.mod(_, a) == 0n : Nat}
  mul_mod_left(b, a)

# The remainder plus the divisor times the quotient is the dividend: a % b + b * (a / b) = a.
law mod_add_div:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.mod(a, b), Nat.mul(b, Nat.div(a, b))) == a : Nat}

def mod_add_div(a, b):
  match b:
    case 0n:
      add_zero(a)
    case 1n++bp:
      +a = a
      %add_comm(Nat.mul(1n+bp, Nat.div(a, 1n+bp)), Nat.mod(a, 1n+bp)) : {_ == a : Nat}
      %mul_comm(Nat.div(a, 1n+bp), 1n+bp) : {Nat.add(_, Nat.mod(a, 1n+bp)) == a : Nat}
      div_mod_eq(a, bp)

# The quotient times the divisor never exceeds the dividend: (a / b) * b <= a.
law div_mul_le_self:
  for a: Nat
  for b: Nat
  le(Nat.mul(Nat.div(a, b), b), a)

def div_mul_le_self(a, b):
  match b:
    case 0n:
      zero_le(a)
    case 1n++bp:
      +a = a
      le_of_add_eq(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp), a, div_mod_eq(a, bp))

# Left commutativity of multiplication: a * (b * c) = b * (a * c).
law mul_left_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}

def mul_left_comm(a, b, c):
  +a = a
  +b = b
  +c = c
  %mul_assoc(a, b, c) : {_ == Nat.mul(b, Nat.mul(a, c)) : Nat}
  %mul_comm(b, a) : {Nat.mul(_, c) == Nat.mul(b, Nat.mul(a, c)) : Nat}
  mul_assoc(b, a, c)

# Right commutativity of multiplication: (a * b) * c = (a * c) * b.
law mul_right_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(Nat.mul(a, c), b) : Nat}

def mul_right_comm(a, b, c):
  +a = a
  +b = b
  +c = c
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), b), Nat.mul(a, Nat.mul(c, b)), mul_assoc(a, c, b)) : {Nat.mul(Nat.mul(a, b), c) == _ : Nat}
  %mul_comm(b, c) : {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, _) : Nat}
  mul_assoc(a, b, c)

# Four-way regrouping of a product: (a * b) * (c * d) = (a * c) * (b * d).
law mul_mul_mul_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}

def mul_mul_mul_comm(a, b, c, d):
  +a = a
  +b = b
  +c = c
  +d = d
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), Nat.mul(b, d)), Nat.mul(a, Nat.mul(c, Nat.mul(b, d))), mul_assoc(a, c, Nat.mul(b, d))) : {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == _ : Nat}
  %mul_left_comm(b, c, d) : {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(a, _) : Nat}
  mul_assoc(a, b, Nat.mul(c, d))

# Zero to a positive power is zero: 0^(n+1) = 0.
law zero_pow:
  for -n: Nat
  {Nat.pow(0n, 1n+n) == 0n : Nat}

def zero_pow(n):
  {==}

# A power of a product is the product of the powers: (a * b)^n = a^n * b^n.
law mul_pow:
  for +a: Nat
  for +b: Nat
  for n: Nat
  {Nat.pow(Nat.mul(a, b), n) == Nat.mul(Nat.pow(a, n), Nat.pow(b, n)) : Nat}

def mul_pow(a, b, n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.pow(Nat.mul(a, b), p), Nat.mul(Nat.pow(a, p), Nat.pow(b, p)), mul_pow(a, b, p)) : {Nat.mul(Nat.mul(a, b), _) == Nat.mul(Nat.mul(a, Nat.pow(a, p)), Nat.mul(b, Nat.pow(b, p))) : Nat}
      mul_mul_mul_comm(a, b, Nat.pow(a, p), Nat.pow(b, p))

# Exponents multiply under repeated powers: a^(m * n) = (a^m)^n.
law pow_mul:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(a, Nat.mul(m, n)) == Nat.pow(Nat.pow(a, m), n) : Nat}

def pow_mul(a, m, n):
  match m:
    case 0n:
      Equal.sym(Nat, Nat.pow(1n, n), 1n, one_pow(n))
    case 1n++p:
      +a = a
      +n = n
      %Equal.sym(Nat, Nat.pow(Nat.mul(a, Nat.pow(a, p)), n), Nat.mul(Nat.pow(a, n), Nat.pow(Nat.pow(a, p), n)), mul_pow(a, Nat.pow(a, p), n)) : {Nat.pow(a, Nat.add(n, Nat.mul(p, n))) == _ : Nat}
      %pow_mul(a, p, n) : {Nat.pow(a, Nat.add(n, Nat.mul(p, n))) == Nat.mul(Nat.pow(a, n), _) : Nat}
      pow_add(a, n, Nat.mul(p, n))

# A power of a positive base is at least one: 1 <= (1 + a)^n.
law one_le_pow:
  for n: Nat
  for a: Nat
  le(1n, Nat.pow(1n+a, n))

def one_le_pow(n, a):
  match n:
    case 0n:
      {==}
    case 1n++p:
      +a = a
      le_trans(1n, Nat.pow(1n+a, p), Nat.add(Nat.pow(1n+a, p), Nat.mul(a, Nat.pow(1n+a, p))), one_le_pow(p, a), le_add_right(Nat.pow(1n+a, p), Nat.mul(a, Nat.pow(1n+a, p))))

# A power of a positive base is positive: 0 < (1 + a)^n.
law pow_pos:
  for n: Nat
  for a: Nat
  lt(0n, Nat.pow(1n+a, n))

def pow_pos(n, a):
  +n = n
  +a = a
  %Equal.sym(Bool, Nat.is_lt(0n, Nat.pow(1n+a, n)), Nat.is_le(1n, Nat.pow(1n+a, n)), is_lt_eq_succ_le(0n, Nat.pow(1n+a, n))) : {_ == True{} : Bool}
  one_le_pow(n, a)

# Adding on the left never decreases a natural: n <= m + n.
law le_add_left:
  for n: Nat
  for m: Nat
  le(n, Nat.add(m, n))

def le_add_left(n, m):
  match m:
    case 0n:
      le_refl(n)
    case 1n++p:
      +n = n
      le_trans(n, Nat.add(p, n), 1n+Nat.add(p, n), le_add_left(n, p), le_succ(Nat.add(p, n)))

# A common left summand cancels in a difference: (k + n) - (k + m) = n - m.
law add_sub_add_left:
  for k: Nat
  for -n: Nat
  for -m: Nat
  {Nat.sub(Nat.add(k, n), Nat.add(k, m)) == Nat.sub(n, m) : Nat}

def add_sub_add_left(k, n, m):
  match k:
    case 0n:
      {==}
    case 1n+p:
      add_sub_add_left(p, n, m)

# A common right summand cancels in a difference: (n + k) - (m + k) = n - m.
law add_sub_add_right:
  for n: Nat
  for k: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, k), Nat.add(m, k)) == Nat.sub(n, m) : Nat}

def add_sub_add_right(n, k, m):
  +n = n
  +k = k
  +m = m
  %add_comm(k, n) : {Nat.sub(_, Nat.add(m, k)) == Nat.sub(n, m) : Nat}
  %add_comm(k, m) : {Nat.sub(Nat.add(k, n), _) == Nat.sub(n, m) : Nat}
  add_sub_add_left(k, n, m)

# Subtracting a part of the right summand: k <= m implies (n + m) - k = n + (m - k).
law add_sub_assoc:
  for k: Nat
  for m: Nat
  for h: le(k, m)
  for n: Nat
  {Nat.sub(Nat.add(n, m), k) == Nat.add(n, Nat.sub(m, k)) : Nat}

def add_sub_assoc(k, m, h, n):
  +k = k
  +m = m
  +n = n
  %sub_add_cancel(m, k, h) : {Nat.sub(Nat.add(n, _), k) == Nat.add(n, Nat.sub(m, k)) : Nat}
  %add_assoc(n, Nat.sub(m, k), k) : {Nat.sub(_, k) == Nat.add(n, Nat.sub(m, k)) : Nat}
  add_sub_cancel(Nat.add(n, Nat.sub(m, k)), k)

# Subtracting a difference from its minuend: m <= n implies n - (n - m) = m.
law sub_sub_self:
  for n: Nat
  for m: Nat
  for h: le(m, n)
  {Nat.sub(n, Nat.sub(n, m)) == m : Nat}

def sub_sub_self(n, m, h):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+q)) == 1n+q : Nat}, internal_false_ne_true(h))
    case 1n+p 0n:
      sub_self(p)
    case 1n++p 1n++q:
      Equal.trans(Nat, Nat.sub(1n+p, Nat.sub(p, q)), 1n+Nat.sub(p, Nat.sub(p, q)), 1n+q, succ_sub(p, Nat.sub(p, q), sub_le(p, q)), Equal.cong(Nat, Nat, x => 1n+x, Nat.sub(p, Nat.sub(p, q)), q, sub_sub_self(p, q, h)))

# Multiplication distributes over subtraction on the right: (n - m) * k = n * k - m * k.
law sub_mul:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.mul(Nat.sub(n, m), k) == Nat.sub(Nat.mul(n, k), Nat.mul(m, k)) : Nat}

def sub_mul(n, m, k):
  match n m:
    case 0n _:
      {==}
    case 1n++p 0n:
      +k = k
      Equal.sym(Nat, Nat.sub(Nat.mul(1n+p, k), 0n), Nat.mul(1n+p, k), sub_zero(Nat.mul(1n+p, k)))
    case 1n++p 1n++q:
      +k = k
      %Equal.sym(Nat, Nat.sub(Nat.add(k, Nat.mul(p, k)), Nat.add(k, Nat.mul(q, k))), Nat.sub(Nat.mul(p, k), Nat.mul(q, k)), add_sub_add_left(k, Nat.mul(p, k), Nat.mul(q, k))) : {Nat.mul(Nat.sub(p, q), k) == _ : Nat}
      sub_mul(p, q, k)

# Multiplication distributes over subtraction on the left: n * (m - k) = n * m - n * k.
law mul_sub:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.mul(n, Nat.sub(m, k)) == Nat.sub(Nat.mul(n, m), Nat.mul(n, k)) : Nat}

def mul_sub(n, m, k):
  +n = n
  +m = m
  +k = k
  %mul_comm(Nat.sub(m, k), n) : {_ == Nat.sub(Nat.mul(n, m), Nat.mul(n, k)) : Nat}
  %mul_comm(m, n) : {Nat.mul(Nat.sub(m, k), n) == Nat.sub(_, Nat.mul(n, k)) : Nat}
  %mul_comm(k, n) : {Nat.mul(Nat.sub(m, k), n) == Nat.sub(Nat.mul(m, n), _) : Nat}
  sub_mul(m, k, n)

# The minimum is the smaller argument on the left: a <= b implies min a b = a.
law min_eq_left:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  {Nat.min(a, b) == a : Nat}

def min_eq_left(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.min(1n+p, 0n) == 1n+p : Nat}, internal_false_ne_true(h))
    case 1n++p 1n+q:
      %min_eq_left(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# The minimum is the smaller argument on the right: b <= a implies min a b = b.
law min_eq_right:
  for a: Nat
  for b: Nat
  for h: le(b, a)
  {Nat.min(a, b) == b : Nat}

def min_eq_right(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.min(0n, 1n+q) == 1n+q : Nat}, internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n++q:
      %min_eq_right(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# The maximum is the larger argument on the left: b <= a implies max a b = a.
law max_eq_left:
  for a: Nat
  for b: Nat
  for h: le(b, a)
  {Nat.max(a, b) == a : Nat}

def max_eq_left(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.max(0n, 1n+q) == 0n : Nat}, internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n++p 1n+q:
      %max_eq_left(p, q, h) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

# The maximum is the larger argument on the right: a <= b implies max a b = b.
law max_eq_right:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  {Nat.max(a, b) == b : Nat}

def max_eq_right(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.max(1n+p, 0n) == 0n : Nat}, internal_false_ne_true(h))
    case 1n+p 1n++q:
      %max_eq_right(p, q, h) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

def internal_and_false_sym(x: Bool) -> {False{} == Bool.and(x, False{}) : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_and_true_sym(x: Bool) -> {x == Bool.and(x, True{}) : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# A number is at most the minimum exactly when it is at most both: a <= min b c tests as a <= b and a <= c (Mathlib's le_min_iff; the implication is le_min_of_le_of_le).
law le_min:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_le(a, Nat.min(b, c)) == Bool.and(Nat.is_le(a, b), Nat.is_le(a, c)) : Bool}

def le_min(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q 0n:
      internal_and_false_sym(Nat.is_le(p, q))
    case 1n+p 1n+q 1n+r:
      le_min(p, q, r)

# The maximum is at most c exactly when both arguments are: max a b <= c tests as a <= c and b <= c (Mathlib's max_le_iff; the implication is max_le_of_le_of_le).
law max_le:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_le(Nat.max(a, b), c) == Bool.and(Nat.is_le(a, c), Nat.is_le(b, c)) : Bool}

def max_le(a, b, c):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      internal_and_true_sym(Nat.is_le(p, r))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      max_le(p, q, r)

# Multiplying on the left preserves the order: a <= b implies k * a <= k * b.
law mul_le_mul_left:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: le(a, b)
  le(Nat.mul(k, a), Nat.mul(k, b))

def mul_le_mul_left(a, b, k, h):
  +a = a
  +b = b
  +k = k
  %mul_comm(a, k) : le(_, Nat.mul(k, b))
  %mul_comm(b, k) : le(Nat.mul(a, k), _)
  mul_le_mul_right(a, b, k, h)

# Multiplying two bounded factors stays bounded: a <= c and b <= d imply a * b <= c * d.
law mul_le_mul:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  for h1: le(a, c)
  for h2: le(b, d)
  le(Nat.mul(a, b), Nat.mul(c, d))

def mul_le_mul(a, b, c, d, h1, h2):
  +a = a
  +b = b
  +c = c
  +d = d
  le_trans(Nat.mul(a, b), Nat.mul(c, b), Nat.mul(c, d), mul_le_mul_right(a, c, b, h1), mul_le_mul_left(b, d, c, h2))

# Every successor is positive: 0 < n + 1.
law succ_pos:
  for -n: Nat
  lt(0n, 1n+n)

def succ_pos(n):
  {==}

# Below a successor means at most: m < n + 1 tests as m <= n.
law lt_succ_iff:
  for m: Nat
  for n: Nat
  {Nat.is_lt(m, 1n+n) == Nat.is_le(m, n) : Bool}

def lt_succ_iff(m, n):
  is_lt_eq_succ_le(m, 1n+n)

# The successor preserves the strict order: a < b implies a + 1 < b + 1.
law succ_lt_succ:
  for -a: Nat
  for -b: Nat
  for h: lt(a, b)
  lt(1n+a, 1n+b)

def succ_lt_succ(a, b, h):
  h

# The strict order of successors is the strict order of the naturals: a + 1 < b + 1 implies a < b.
law lt_of_succ_lt_succ:
  for -a: Nat
  for -b: Nat
  for h: lt(1n+a, 1n+b)
  lt(a, b)

def lt_of_succ_lt_succ(a, b, h):
  h

# Below a successor is at most: m < n + 1 implies m <= n.
law le_of_lt_succ:
  for m: Nat
  for n: Nat
  for h: lt(m, 1n+n)
  le(m, n)

def le_of_lt_succ(m, n, h):
  Equal.trans(Bool, Nat.is_le(m, n), Nat.is_lt(m, 1n+n), True{}, Equal.sym(Bool, Nat.is_lt(m, 1n+n), Nat.is_le(m, n), lt_succ_iff(m, n)), h)

# At most is below the successor: m <= n implies m < n + 1.
law lt_succ_of_le:
  for m: Nat
  for n: Nat
  for h: le(m, n)
  lt(m, 1n+n)

def lt_succ_of_le(m, n, h):
  Equal.trans(Bool, Nat.is_lt(m, 1n+n), Nat.is_le(m, n), True{}, lt_succ_iff(m, n), h)

# A strict inequality gives the weak one from the successor: n < m implies n + 1 <= m.
law succ_le_of_lt:
  for n: Nat
  for m: Nat
  for h: lt(n, m)
  le(1n+n, m)

def succ_le_of_lt(n, m, h):
  Equal.trans(Bool, Nat.is_le(1n+n, m), Nat.is_lt(n, m), True{}, Equal.sym(Bool, Nat.is_lt(n, m), Nat.is_le(1n+n, m), is_lt_eq_succ_le(n, m)), h)

# A weak inequality from the successor gives the strict one: n + 1 <= m implies n < m.
law lt_of_succ_le:
  for n: Nat
  for m: Nat
  for h: le(1n+n, m)
  lt(n, m)

def lt_of_succ_le(n, m, h):
  Equal.trans(Bool, Nat.is_lt(n, m), Nat.is_le(1n+n, m), True{}, is_lt_eq_succ_le(n, m), h)

# The strict order is asymmetric: a < b rules out b < a.
law lt_asymm:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  lt(b, a) -> Empty

def lt_asymm(a, b, h):
  +a = a
  h2 => lt_irrefl(a)(lt_trans(a, b, a, h, h2))

# At most means below or equal: a <= b tests as a < b or a = b.
law le_iff_lt_or_eq:
  for a: Nat
  for b: Nat
  {Nat.is_le(a, b) == Bool.or(Nat.is_lt(a, b), Nat.is_eq(a, b)) : Bool}

def le_iff_lt_or_eq(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_iff_lt_or_eq(p, q)

# Below means at most and different: a < b tests as a <= b and not a = b.
law lt_iff_le_and_ne:
  for a: Nat
  for b: Nat
  {Nat.is_lt(a, b) == Bool.and(Nat.is_le(a, b), Bool.not(Nat.is_eq(a, b))) : Bool}

def lt_iff_le_and_ne(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_iff_le_and_ne(p, q)

# A natural that does not test equal to zero is positive.
law pos_of_ne_zero:
  for n: Nat
  for h: {Nat.is_eq(n, 0n) == False{} : Bool}
  lt(0n, n)

def pos_of_ne_zero(n, h):
  match n:
    case 0n:
      Empty.absurd(lt(0n, 0n), internal_div_true_ne_false(h))
    case 1n+p:
      {==}

# Adding on the right keeps a strict bound: n < m implies n < m + k.
law lt_add_right:
  for n: Nat
  for m: Nat
  for -k: Nat
  for h: lt(n, m)
  lt(n, Nat.add(m, k))

def lt_add_right(n, m, k, h):
  match n m:
    case 0n 0n:
      Empty.absurd(lt(0n, Nat.add(0n, k)), internal_false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd(lt(1n+p, Nat.add(0n, k)), internal_false_ne_true(h))
    case 1n+p 1n+q:
      lt_add_right(p, q, k, h)

# Adding a positive amount on the right strictly increases: n < n + (1 + k).
law lt_add_of_pos_right:
  for n: Nat
  for -k: Nat
  lt(n, Nat.add(n, 1n+k))

def lt_add_of_pos_right(n, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_add_of_pos_right(p, k)

# Adding a positive amount on the left strictly increases: n < (1 + k) + n.
law lt_add_of_pos_left:
  for n: Nat
  for k: Nat
  lt(n, Nat.add(1n+k, n))

def lt_add_of_pos_left(n, k):
  +n = n
  +k = k
  lt_succ_of_le(n, Nat.add(k, n), le_add_left(n, k))

# Adding on the left preserves the strict order: a < b implies k + a < k + b.
law add_lt_add_left:
  for -a: Nat
  for -b: Nat
  for k: Nat
  for h: lt(a, b)
  lt(Nat.add(k, a), Nat.add(k, b))

def add_lt_add_left(a, b, k, h):
  match k:
    case 0n:
      h
    case 1n+p:
      add_lt_add_left(a, b, p, h)

# Adding on the right preserves the strict order: a < b implies a + k < b + k.
law add_lt_add_right:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: lt(a, b)
  lt(Nat.add(a, k), Nat.add(b, k))

def add_lt_add_right(a, b, k, h):
  +a = a
  +b = b
  +k = k
  %add_comm(k, a) : lt(_, Nat.add(b, k))
  %add_comm(k, b) : lt(Nat.add(k, a), _)
  add_lt_add_left(a, b, k, h)

# Adding the same amount on the left does not change the strict order test: a < b tests as k + a < k + b.
law add_lt_add_iff_left:
  for k: Nat
  for -a: Nat
  for -b: Nat
  {Nat.is_lt(a, b) == Nat.is_lt(Nat.add(k, a), Nat.add(k, b)) : Bool}

def add_lt_add_iff_left(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+p:
      add_lt_add_iff_left(p, a, b)

# Adding the same amount on the right does not change the strict order test: a < b tests as a + k < b + k.
law add_lt_add_iff_right:
  for a: Nat
  for b: Nat
  for k: Nat
  {Nat.is_lt(a, b) == Nat.is_lt(Nat.add(a, k), Nat.add(b, k)) : Bool}

def add_lt_add_iff_right(a, b, k):
  +a = a
  +b = b
  +k = k
  %add_comm(k, a) : {Nat.is_lt(a, b) == Nat.is_lt(_, Nat.add(b, k)) : Bool}
  %add_comm(k, b) : {Nat.is_lt(a, b) == Nat.is_lt(Nat.add(k, a), _) : Bool}
  add_lt_add_iff_left(k, a, b)

# A common left summand cancels in a strict inequality: k + a < k + b implies a < b.
law lt_of_add_lt_add_left:
  for k: Nat
  for -a: Nat
  for -b: Nat
  for h: lt(Nat.add(k, a), Nat.add(k, b))
  lt(a, b)

def lt_of_add_lt_add_left(k, a, b, h):
  match k:
    case 0n:
      h
    case 1n+p:
      lt_of_add_lt_add_left(p, a, b, h)

# A common right summand cancels in a strict inequality: a + k < b + k implies a < b.
law lt_of_add_lt_add_right:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: lt(Nat.add(a, k), Nat.add(b, k))
  lt(a, b)

def lt_of_add_lt_add_right(a, b, k, h):
  Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_lt(Nat.add(a, k), Nat.add(b, k)), True{}, add_lt_add_iff_right(a, b, k), h)

# Adding two strict bounds keeps a strict bound: a < c and b < d imply a + b < c + d.
law add_lt_add:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  for h1: lt(a, c)
  for h2: lt(b, d)
  lt(Nat.add(a, b), Nat.add(c, d))

def add_lt_add(a, b, c, d, h1, h2):
  +a = a
  +b = b
  +c = c
  +d = d
  lt_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), add_lt_add_right(a, c, b, h1), add_lt_add_left(b, d, c, h2))

# A positive left factor never decreases: m <= (1 + n) * m.
law le_mul_of_pos_left:
  for m: Nat
  for n: Nat
  le(m, Nat.mul(1n+n, m))

def le_mul_of_pos_left(m, n):
  +m = m
  le_add_right(m, Nat.mul(n, m))

# A positive right factor never decreases: m <= m * (1 + n).
law le_mul_of_pos_right:
  for m: Nat
  for n: Nat
  le(m, Nat.mul(m, 1n+n))

def le_mul_of_pos_right(m, n):
  +m = m
  +n = n
  %mul_comm(1n+n, m) : le(m, _)
  le_mul_of_pos_left(m, n)

# Multiplying on the left by a positive factor preserves the strict order: a < b implies (1 + k) * a < (1 + k) * b.
law mul_lt_mul_of_pos_left:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: lt(a, b)
  lt(Nat.mul(1n+k, a), Nat.mul(1n+k, b))

def mul_lt_mul_of_pos_left(a, b, k, h):
  +a = a
  +b = b
  +k = k
  +h = h
  lt_of_lt_of_le(Nat.add(a, Nat.mul(k, a)), Nat.add(b, Nat.mul(k, a)), Nat.add(b, Nat.mul(k, b)), add_lt_add_right(a, b, Nat.mul(k, a), h), add_le_add_left(Nat.mul(k, a), Nat.mul(k, b), b, mul_le_mul_left(a, b, k, le_of_lt(a, b, h))))

# Multiplying on the right by a positive factor preserves the strict order: a < b implies a * (1 + k) < b * (1 + k).
law mul_lt_mul_of_pos_right:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: lt(a, b)
  lt(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))

def mul_lt_mul_of_pos_right(a, b, k, h):
  +a = a
  +b = b
  +k = k
  %mul_comm(1n+k, a) : lt(_, Nat.mul(b, 1n+k))
  %mul_comm(1n+k, b) : lt(Nat.mul(1n+k, a), _)
  mul_lt_mul_of_pos_left(a, b, k, h)

def internal_lt_of_not_le(+a: Nat, +b: Nat, v: Bool, e: {v == Nat.is_lt(a, b) : Bool}, f: le(b, a) -> Empty) -> lt(a, b):
  match v:
    case True{}:
      Equal.sym(Bool, True{}, Nat.is_lt(a, b), e)
    case False{}:
      Empty.absurd(lt(a, b), f(le_of_not_lt(a, b, Equal.sym(Bool, False{}, Nat.is_lt(a, b), e))))

# A common left factor cancels in a strict inequality: k * a < k * b implies a < b.
law lt_of_mul_lt_mul_left:
  for k: Nat
  for a: Nat
  for b: Nat
  for h: lt(Nat.mul(k, a), Nat.mul(k, b))
  lt(a, b)

def lt_of_mul_lt_mul_left(k, a, b, h):
  +k = k
  +a = a
  +b = b
  internal_lt_of_not_le(a, b, Nat.is_lt(a, b), {==}, hb => internal_false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(Nat.mul(k, b), Nat.mul(k, a)), True{}, Equal.sym(Bool, Nat.is_le(Nat.mul(k, b), Nat.mul(k, a)), False{}, not_le_of_lt(Nat.mul(k, a), Nat.mul(k, b), h)), mul_le_mul_left(b, a, k, hb))))

# A common right factor cancels in a strict inequality: a * k < b * k implies a < b.
law lt_of_mul_lt_mul_right:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: lt(Nat.mul(a, k), Nat.mul(b, k))
  lt(a, b)

def lt_of_mul_lt_mul_right(a, b, k, h):
  +k = k
  +a = a
  +b = b
  internal_lt_of_not_le(a, b, Nat.is_lt(a, b), {==}, hb => internal_false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(Nat.mul(b, k), Nat.mul(a, k)), True{}, Equal.sym(Bool, Nat.is_le(Nat.mul(b, k), Nat.mul(a, k)), False{}, not_le_of_lt(Nat.mul(a, k), Nat.mul(b, k), h)), mul_le_mul_right(b, a, k, hb))))

# Multiplying two strict bounds keeps a strict bound: a < c and b < d imply a * b < c * d.
law mul_lt_mul_of_lt_of_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  for h1: lt(a, c)
  for h2: lt(b, d)
  lt(Nat.mul(a, b), Nat.mul(c, d))

def mul_lt_mul_of_lt_of_lt(a, b, c, d, h1, h2):
  match c:
    case 0n:
      Empty.absurd(lt(Nat.mul(a, b), Nat.mul(0n, d)), lt_zero(a)(h1))
    case 1n++cp:
      +a = a
      +b = b
      +d = d
      lt_of_le_of_lt(Nat.mul(a, b), Nat.mul(1n+cp, b), Nat.mul(1n+cp, d), mul_le_mul_right(a, 1n+cp, b, le_of_lt(a, 1n+cp, h1)), mul_lt_mul_of_pos_left(b, d, cp, h2))

# Squares are monotone: a <= b implies a * a <= b * b.
law mul_self_le_mul_self:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  le(Nat.mul(a, a), Nat.mul(b, b))

def mul_self_le_mul_self(a, b, h):
  +a = a
  +b = b
  +h = h
  mul_le_mul(a, a, b, b, h, h)

# Squares are strictly monotone: a < b implies a * a < b * b.
law mul_self_lt_mul_self:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  lt(Nat.mul(a, a), Nat.mul(b, b))

def mul_self_lt_mul_self(a, b, h):
  +a = a
  +b = b
  +h = h
  mul_lt_mul_of_lt_of_lt(a, a, b, b, h, h)

# Subtracting a positive amount from a positive number decreases it: (1 + n) - (1 + m) < 1 + n.
law sub_lt:
  for n: Nat
  for m: Nat
  lt(Nat.sub(1n+n, 1n+m), 1n+n)

def sub_lt(n, m):
  +n = n
  +m = m
  lt_succ_of_le(Nat.sub(n, m), n, sub_le(n, m))

# Subtracting more gives less: n <= m implies k - m <= k - n.
law sub_le_sub_left:
  for n: Nat
  for m: Nat
  for h: le(n, m)
  for k: Nat
  le(Nat.sub(k, m), Nat.sub(k, n))

def sub_le_sub_left(n, m, h, k):
  +n = n
  +m = m
  +k = k
  %add_sub_of_le(n, m, h) : le(Nat.sub(k, _), Nat.sub(k, n))
  %sub_sub(k, n, Nat.sub(m, n)) : le(_, Nat.sub(k, n))
  sub_le(Nat.sub(k, n), Nat.sub(m, n))

# Subtraction on the right preserves the order: n <= m implies n - k <= m - k.
law sub_le_sub_right:
  for n: Nat
  for m: Nat
  for h: le(n, m)
  for k: Nat
  le(Nat.sub(n, k), Nat.sub(m, k))

def sub_le_sub_right(n, m, h, k):
  match n m k:
    case 0n _ _:
      +k = k
      %Equal.sym(Nat, Nat.sub(0n, k), 0n, zero_sub(k)) : le(_, Nat.sub(m, k))
      zero_le(Nat.sub(m, k))
    case 1n+p 0n _:
      Empty.absurd(le(Nat.sub(1n+p, k), Nat.sub(0n, k)), internal_false_ne_true(h))
    case 1n+p 1n+q 0n:
      h
    case 1n+p 1n+q 1n+r:
      sub_le_sub_right(p, q, h, r)

# A strict bound on a sum bounds a difference: a + b < c implies a < c - b.
law lt_sub_of_add_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  for h: lt(Nat.add(a, b), c)
  lt(a, Nat.sub(c, b))

def lt_sub_of_add_lt(a, b, c, h):
  +a = a
  +b = b
  %Equal.sym(Bool, Nat.is_lt(a, Nat.sub(c, b)), Nat.is_lt(Nat.add(b, a), c), lt_sub_iff_add_lt(a, b, c)) : {_ == True{} : Bool}
  %add_comm(a, b) : {Nat.is_lt(_, c) == True{} : Bool}
  h

# A difference is positive below the minuend: m < n implies 0 < n - m.
law sub_pos_of_lt:
  for m: Nat
  for n: Nat
  for h: lt(m, n)
  lt(0n, Nat.sub(n, m))

def sub_pos_of_lt(m, n, h):
  lt_sub_of_add_lt(0n, m, n, h)

# Minimum distributes over maximum on the left: min a (max b c) = max (min a b) (min a c).
law min_max_distrib_left:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(a, Nat.max(b, c)) == Nat.max(Nat.min(a, b), Nat.min(a, c)) : Nat}

def min_max_distrib_left(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      %min_max_distrib_left(p, q, r) : {1n+Nat.min(p, Nat.max(q, r)) == 1n+_ : Nat}
      {==}

# Maximum distributes over minimum on the left: max a (min b c) = min (max a b) (max a c).
law max_min_distrib_left:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(a, Nat.min(b, c)) == Nat.min(Nat.max(a, b), Nat.max(a, c)) : Nat}

def max_min_distrib_left(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n++p 0n 0n:
      %Equal.sym(Nat, Nat.min(p, p), p, min_self(p)) : {1n+p == 1n+_ : Nat}
      {==}
    case 1n++p 0n 1n++r:
      %Equal.sym(Nat, Nat.min(p, Nat.max(p, r)), p, min_eq_left(p, Nat.max(p, r), le_max_left(p, r))) : {1n+p == 1n+_ : Nat}
      {==}
    case 1n++p 1n++q 0n:
      %Equal.sym(Nat, Nat.min(Nat.max(p, q), p), p, min_eq_right(Nat.max(p, q), p, le_max_left(p, q))) : {1n+p == 1n+_ : Nat}
      {==}
    case 1n+p 1n+q 1n+r:
      %max_min_distrib_left(p, q, r) : {1n+Nat.max(p, Nat.min(q, r)) == 1n+_ : Nat}
      {==}

# A common left summand leaves the minimum: min (a + b) (a + c) = a + min b c.
law min_add_add_left:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.min(Nat.add(a, b), Nat.add(a, c)) == Nat.add(a, Nat.min(b, c)) : Nat}

def min_add_add_left(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %min_add_add_left(p, b, c) : {1n+Nat.min(Nat.add(p, b), Nat.add(p, c)) == 1n+_ : Nat}
      {==}

# A common right summand leaves the minimum: min (a + c) (b + c) = min a b + c.
law min_add_add_right:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(Nat.add(a, c), Nat.add(b, c)) == Nat.add(Nat.min(a, b), c) : Nat}

def min_add_add_right(a, b, c):
  +a = a
  +b = b
  +c = c
  %add_comm(c, a) : {Nat.min(_, Nat.add(b, c)) == Nat.add(Nat.min(a, b), c) : Nat}
  %add_comm(c, b) : {Nat.min(Nat.add(c, a), _) == Nat.add(Nat.min(a, b), c) : Nat}
  %add_comm(c, Nat.min(a, b)) : {Nat.min(Nat.add(c, a), Nat.add(c, b)) == _ : Nat}
  min_add_add_left(c, a, b)

# A common left summand leaves the maximum: max (a + b) (a + c) = a + max b c.
law max_add_add_left:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.max(Nat.add(a, b), Nat.add(a, c)) == Nat.add(a, Nat.max(b, c)) : Nat}

def max_add_add_left(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %max_add_add_left(p, b, c) : {1n+Nat.max(Nat.add(p, b), Nat.add(p, c)) == 1n+_ : Nat}
      {==}

# A common right summand leaves the maximum: max (a + c) (b + c) = max a b + c.
law max_add_add_right:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(Nat.add(a, c), Nat.add(b, c)) == Nat.add(Nat.max(a, b), c) : Nat}

def max_add_add_right(a, b, c):
  +a = a
  +b = b
  +c = c
  %add_comm(c, a) : {Nat.max(_, Nat.add(b, c)) == Nat.add(Nat.max(a, b), c) : Nat}
  %add_comm(c, b) : {Nat.max(Nat.add(c, a), _) == Nat.add(Nat.max(a, b), c) : Nat}
  %add_comm(c, Nat.max(a, b)) : {Nat.max(Nat.add(c, a), Nat.add(c, b)) == _ : Nat}
  max_add_add_left(c, a, b)

# The minimum is below c exactly when one argument is: min a b < c tests as a < c or b < c.
law min_lt_iff:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_lt(Nat.min(a, b), c) == Bool.or(Nat.is_lt(a, c), Nat.is_lt(b, c)) : Bool}

def min_lt_iff(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      internal_or_true_sym(Nat.is_lt(p, r))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      min_lt_iff(p, q, r)

# A number is below the minimum exactly when it is below both: a < min b c tests as a < b and a < c.
law lt_min_iff:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_lt(a, Nat.min(b, c)) == Bool.and(Nat.is_lt(a, b), Nat.is_lt(a, c)) : Bool}

def lt_min_iff(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      internal_and_false_sym(Nat.is_lt(p, q))
    case 1n+p 1n+q 1n+r:
      lt_min_iff(p, q, r)

# The maximum is below c exactly when both arguments are: max a b < c tests as a < c and b < c.
law max_lt_iff:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_lt(Nat.max(a, b), c) == Bool.and(Nat.is_lt(a, c), Nat.is_lt(b, c)) : Bool}

def max_lt_iff(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      internal_and_true_sym(Nat.is_lt(p, r))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      max_lt_iff(p, q, r)

# A number is at most the maximum exactly when it is at most one argument: a <= max b c tests as a <= b or a <= c.
law le_max_iff:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_le(a, Nat.max(b, c)) == Bool.or(Nat.is_le(a, b), Nat.is_le(a, c)) : Bool}

def le_max_iff(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      internal_or_false_sym(Nat.is_le(p, q))
    case 1n+p 1n+q 1n+r:
      le_max_iff(p, q, r)

# A bound by the left argument bounds the maximum: a <= b implies a <= max b c.
law le_max_of_le_left:
  for a: Nat
  for b: Nat
  for c: Nat
  for h: le(a, b)
  le(a, Nat.max(b, c))

def le_max_of_le_left(a, b, c, h):
  +b = b
  +c = c
  le_trans(a, b, Nat.max(b, c), h, le_max_left(b, c))

# A bound by the right argument bounds the maximum: a <= c implies a <= max b c.
law le_max_of_le_right:
  for a: Nat
  for b: Nat
  for c: Nat
  for h: le(a, c)
  le(a, Nat.max(b, c))

def le_max_of_le_right(a, b, c, h):
  +b = b
  +c = c
  le_trans(a, c, Nat.max(b, c), h, le_max_right(b, c))

# A bounded left argument bounds the minimum: a <= c implies min a b <= c.
law min_le_of_left_le:
  for a: Nat
  for b: Nat
  for c: Nat
  for h: le(a, c)
  le(Nat.min(a, b), c)

def min_le_of_left_le(a, b, c, h):
  +a = a
  +b = b
  le_trans(Nat.min(a, b), a, c, min_le_left(a, b), h)

# A bounded right argument bounds the minimum: b <= c implies min a b <= c.
law min_le_of_right_le:
  for a: Nat
  for b: Nat
  for c: Nat
  for h: le(b, c)
  le(Nat.min(a, b), c)

def min_le_of_right_le(a, b, c, h):
  +a = a
  +b = b
  le_trans(Nat.min(a, b), b, c, min_le_right(a, b), h)

# Minimum is monotone in both arguments: a <= c and b <= d imply min a b <= min c d.
law min_le_min:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  for h1: le(a, c)
  for h2: le(b, d)
  le(Nat.min(a, b), Nat.min(c, d))

def min_le_min(a, b, c, d, h1, h2):
  +a = a
  +b = b
  +c = c
  +d = d
  %Equal.sym(Bool, Nat.is_le(Nat.min(a, b), Nat.min(c, d)), Bool.and(Nat.is_le(Nat.min(a, b), c), Nat.is_le(Nat.min(a, b), d)), le_min(Nat.min(a, b), c, d)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(Nat.min(a, b), c), True{}, min_le_of_left_le(a, b, c, h1)) : {Bool.and(_, Nat.is_le(Nat.min(a, b), d)) == True{} : Bool}
  min_le_of_right_le(a, b, d, h2)

# Maximum is monotone in both arguments: a <= c and b <= d imply max a b <= max c d.
law max_le_max:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  for h1: le(a, c)
  for h2: le(b, d)
  le(Nat.max(a, b), Nat.max(c, d))

def max_le_max(a, b, c, d, h1, h2):
  +a = a
  +b = b
  +c = c
  +d = d
  %Equal.sym(Bool, Nat.is_le(Nat.max(a, b), Nat.max(c, d)), Bool.and(Nat.is_le(a, Nat.max(c, d)), Nat.is_le(b, Nat.max(c, d))), max_le(a, b, Nat.max(c, d))) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(a, Nat.max(c, d)), True{}, le_max_of_le_left(a, c, d, h1)) : {Bool.and(_, Nat.is_le(b, Nat.max(c, d))) == True{} : Bool}
  le_max_of_le_right(b, c, d, h2)

# Powers are monotone in the base: a <= b implies a^n <= b^n.
law pow_le_pow_left:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  for n: Nat
  le(Nat.pow(a, n), Nat.pow(b, n))

def pow_le_pow_left(a, b, h, n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      +a = a
      +b = b
      +h = h
      mul_le_mul(a, Nat.pow(a, p), b, Nat.pow(b, p), h, pow_le_pow_left(a, b, h, p))

# Powers of a positive base are monotone in the exponent: i <= j implies (1 + a)^i <= (1 + a)^j.
law pow_le_pow_right:
  for a: Nat
  for i: Nat
  for j: Nat
  for h: le(i, j)
  le(Nat.pow(1n+a, i), Nat.pow(1n+a, j))

def pow_le_pow_right(a, i, j, h):
  match i j:
    case 0n y:
      one_le_pow(y, a)
    case 1n+p 0n:
      Empty.absurd(le(Nat.pow(1n+a, 1n+p), Nat.pow(1n+a, 0n)), internal_false_ne_true(h))
    case 1n++p 1n++q:
      +a = a
      mul_le_mul_left(Nat.pow(1n+a, p), Nat.pow(1n+a, q), 1n+a, pow_le_pow_right(a, p, q, h))

def internal_lt_mul_two_add(a: Nat, x: Nat, hx: lt(0n, x)) -> lt(x, Nat.mul(2n+a, x)):
  match x:
    case 0n:
      Empty.absurd(lt(0n, Nat.mul(2n+a, 0n)), internal_false_ne_true(hx))
    case 1n++y:
      lt_add_of_pos_right(y, Nat.add(y, Nat.mul(a, 1n+y)))

# Powers of a base above one are strictly monotone in the exponent: i < j implies (2 + a)^i < (2 + a)^j.
law pow_lt_pow_right:
  for a: Nat
  for i: Nat
  for j: Nat
  for h: lt(i, j)
  lt(Nat.pow(2n+a, i), Nat.pow(2n+a, j))

def pow_lt_pow_right(a, i, j, h):
  match i j:
    case 0n 0n:
      Empty.absurd(lt(Nat.pow(2n+a, 0n), Nat.pow(2n+a, 0n)), internal_false_ne_true(h))
    case 0n 1n+q:
      +a = a
      +q = q
      lt_of_le_of_lt(1n, Nat.pow(2n+a, q), Nat.mul(2n+a, Nat.pow(2n+a, q)), one_le_pow(q, 1n+a), internal_lt_mul_two_add(a, Nat.pow(2n+a, q), pow_pos(q, 1n+a)))
    case 1n+p 0n:
      Empty.absurd(lt(Nat.pow(2n+a, 1n+p), Nat.pow(2n+a, 0n)), internal_false_ne_true(h))
    case 1n++p 1n++q:
      +a = a
      mul_lt_mul_of_pos_left(Nat.pow(2n+a, p), Nat.pow(2n+a, q), 1n+a, pow_lt_pow_right(a, p, q, h))

# Positive powers are strictly monotone in the base: a < b implies a^(1 + n) < b^(1 + n).
law pow_lt_pow_left:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  for n: Nat
  lt(Nat.pow(a, 1n+n), Nat.pow(b, 1n+n))

def pow_lt_pow_left(a, b, h, n):
  match n:
    case 0n:
      +a = a
      +b = b
      %Equal.sym(Nat, Nat.mul(a, 1n), a, mul_one(a)) : lt(_, Nat.mul(b, 1n))
      %Equal.sym(Nat, Nat.mul(b, 1n), b, mul_one(b)) : lt(a, _)
      h
    case 1n++p:
      +a = a
      +b = b
      +h = h
      mul_lt_mul_of_lt_of_lt(a, Nat.pow(a, 1n+p), b, Nat.pow(b, 1n+p), h, pow_lt_pow_left(a, b, h, p))

# Adding a multiple of a positive divisor adds to the quotient: (x + z * (1 + b)) / (1 + b) = x / (1 + b) + z.
law add_mul_div_right:
  for x: Nat
  for z: Nat
  for b: Nat
  {Nat.div(Nat.add(x, Nat.mul(z, 1n+b)), 1n+b) == Nat.add(Nat.div(x, 1n+b), z) : Nat}

def add_mul_div_right(x, z, b):
  match z:
    case 0n:
      +x = x
      +b = b
      %Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x)) : {Nat.div(_, 1n+b) == Nat.add(Nat.div(x, 1n+b), 0n) : Nat}
      Equal.sym(Nat, Nat.add(Nat.div(x, 1n+b), 0n), Nat.div(x, 1n+b), add_zero(Nat.div(x, 1n+b)))
    case 1n++w:
      +x = x
      +b = b
      %Equal.sym(Nat, Nat.add(x, Nat.add(1n+b, Nat.mul(w, 1n+b))), Nat.add(1n+b, Nat.add(x, Nat.mul(w, 1n+b))), add_left_comm(x, 1n+b, Nat.mul(w, 1n+b))) : {Nat.div(_, 1n+b) == Nat.add(Nat.div(x, 1n+b), 1n+w) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(1n+b, Nat.add(x, Nat.mul(w, 1n+b))), 1n+b), 1n+Nat.div(Nat.add(x, Nat.mul(w, 1n+b)), 1n+b), add_div_left(Nat.add(x, Nat.mul(w, 1n+b)), b)) : {_ == Nat.add(Nat.div(x, 1n+b), 1n+w) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(x, Nat.mul(w, 1n+b)), 1n+b), Nat.add(Nat.div(x, 1n+b), w), add_mul_div_right(x, w, b)) : {1n+_ == Nat.add(Nat.div(x, 1n+b), 1n+w) : Nat}
      Equal.sym(Nat, Nat.add(Nat.div(x, 1n+b), 1n+w), 1n+Nat.add(Nat.div(x, 1n+b), w), add_succ(Nat.div(x, 1n+b), w))

# Adding a multiple of a positive divisor adds to the quotient: (x + (1 + b) * z) / (1 + b) = x / (1 + b) + z.
law add_mul_div_left:
  for x: Nat
  for z: Nat
  for b: Nat
  {Nat.div(Nat.add(x, Nat.mul(1n+b, z)), 1n+b) == Nat.add(Nat.div(x, 1n+b), z) : Nat}

def add_mul_div_left(x, z, b):
  +x = x
  +z = z
  +b = b
  %mul_comm(z, 1n+b) : {Nat.div(Nat.add(x, _), 1n+b) == Nat.add(Nat.div(x, 1n+b), z) : Nat}
  add_mul_div_right(x, z, b)

# Adding a multiple of the divisor keeps the remainder: (a + c * b) % b = a % b.
law add_mul_mod_self_right:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mod(Nat.add(a, Nat.mul(c, b)), b) == Nat.mod(a, b) : Nat}

def add_mul_mod_self_right(a, b, c):
  match c:
    case 0n:
      +a = a
      %Equal.sym(Nat, Nat.add(a, 0n), a, add_zero(a)) : {Nat.mod(_, b) == Nat.mod(a, b) : Nat}
      {==}
    case 1n++w:
      +a = a
      +b = b
      %Equal.sym(Nat, Nat.add(a, Nat.add(b, Nat.mul(w, b))), Nat.add(b, Nat.add(a, Nat.mul(w, b))), add_left_comm(a, b, Nat.mul(w, b))) : {Nat.mod(_, b) == Nat.mod(a, b) : Nat}
      Equal.trans(Nat, Nat.mod(Nat.add(b, Nat.add(a, Nat.mul(w, b))), b), Nat.mod(Nat.add(a, Nat.mul(w, b)), b), Nat.mod(a, b), add_mod_left(Nat.add(a, Nat.mul(w, b)), b), add_mul_mod_self_right(a, b, w))

# Adding a multiple of the divisor keeps the remainder: (a + b * c) % b = a % b.
law add_mul_mod_self_left:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mod(Nat.add(a, Nat.mul(b, c)), b) == Nat.mod(a, b) : Nat}

def add_mul_mod_self_left(a, b, c):
  +a = a
  +b = b
  +c = c
  %mul_comm(c, b) : {Nat.mod(Nat.add(a, _), b) == Nat.mod(a, b) : Nat}
  add_mul_mod_self_right(a, b, c)

def internal_lt_one_succ(y: Nat, h: lt(y, 1n)) -> {Bool.or(Nat.is_eq(1n+y, 0n), Nat.is_eq(1n+y, 1n)) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+z:
      Empty.absurd({Bool.or(Nat.is_eq(2n+z, 0n), Nat.is_eq(2n+z, 1n)) == True{} : Bool}, lt_zero(z)(h))

def internal_lt_two(x: Nat, h: lt(x, 2n)) -> {Bool.or(Nat.is_eq(x, 0n), Nat.is_eq(x, 1n)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      internal_lt_one_succ(y, h)

# A remainder modulo two is zero or one.
law mod_two_eq_zero_or_one:
  for n: Nat
  {Bool.or(Nat.is_eq(Nat.mod(n, 2n), 0n), Nat.is_eq(Nat.mod(n, 2n), 1n)) == True{} : Bool}

def mod_two_eq_zero_or_one(n):
  +n = n
  internal_lt_two(Nat.mod(n, 2n), mod_lt(n, 1n))

# The divisor times the quotient plus the remainder is the dividend: b * (a / b) + a % b = a.
law div_add_mod:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.mul(b, Nat.div(a, b)), Nat.mod(a, b)) == a : Nat}

def div_add_mod(a, b):
  +a = a
  +b = b
  %add_comm(Nat.mod(a, b), Nat.mul(b, Nat.div(a, b))) : {_ == a : Nat}
  mod_add_div(a, b)

# Two times n is n + n.
law two_mul:
  for n: Nat
  {Nat.mul(2n, n) == Nat.add(n, n) : Nat}

def two_mul(n):
  +n = n
  %Equal.sym(Nat, Nat.add(n, 0n), n, add_zero(n)) : {Nat.add(n, _) == Nat.add(n, n) : Nat}
  {==}

# Doubling is multiplying by two: double n = 2 * n.
law double_eq_two_mul:
  for n: Nat
  {Nat.double(n) == Nat.mul(2n, n) : Nat}

def double_eq_two_mul(n):
  +n = n
  %Equal.sym(Nat, Nat.mul(2n, n), Nat.add(n, n), two_mul(n)) : {Nat.double(n) == _ : Nat}
  double_eq_add(n)

# Doubling distributes over addition: double (a + b) = double a + double b.
law double_add:
  for a: Nat
  for b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}

def double_add(a, b):
  +a = a
  +b = b
  %Equal.sym(Nat, Nat.double(Nat.add(a, b)), Nat.add(Nat.add(a, b), Nat.add(a, b)), double_eq_add(Nat.add(a, b))) : {_ == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
  %Equal.sym(Nat, Nat.double(a), Nat.add(a, a), double_eq_add(a)) : {Nat.add(Nat.add(a, b), Nat.add(a, b)) == Nat.add(_, Nat.double(b)) : Nat}
  %Equal.sym(Nat, Nat.double(b), Nat.add(b, b), double_eq_add(b)) : {Nat.add(Nat.add(a, b), Nat.add(a, b)) == Nat.add(Nat.add(a, a), _) : Nat}
  add_add_add_comm(a, b, a, b)

# Doubling a product doubles its left factor: double (a * b) = double a * b.
law double_mul:
  for a: Nat
  for b: Nat
  {Nat.double(Nat.mul(a, b)) == Nat.mul(Nat.double(a), b) : Nat}

def double_mul(a, b):
  +a = a
  +b = b
  %Equal.sym(Nat, Nat.double(Nat.mul(a, b)), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), double_eq_add(Nat.mul(a, b))) : {_ == Nat.mul(Nat.double(a), b) : Nat}
  %Equal.sym(Nat, Nat.double(a), Nat.add(a, a), double_eq_add(a)) : {Nat.add(Nat.mul(a, b), Nat.mul(a, b)) == Nat.mul(_, b) : Nat}
  Equal.sym(Nat, Nat.mul(Nat.add(a, a), b), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), add_mul(a, a, b))

# Multiplying by a doubled factor doubles the product: a * double b = double (a * b).
law mul_double:
  for a: Nat
  for b: Nat
  {Nat.mul(a, Nat.double(b)) == Nat.double(Nat.mul(a, b)) : Nat}

def mul_double(a, b):
  +a = a
  +b = b
  %Equal.sym(Nat, Nat.double(b), Nat.add(b, b), double_eq_add(b)) : {Nat.mul(a, _) == Nat.double(Nat.mul(a, b)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.mul(a, b)), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), double_eq_add(Nat.mul(a, b))) : {Nat.mul(a, Nat.add(b, b)) == _ : Nat}
  mul_add(a, b, b)

# Doubling distributes over truncated subtraction: double (a - b) = double a - double b.
law double_sub:
  for a: Nat
  for b: Nat
  {Nat.double(Nat.sub(a, b)) == Nat.sub(Nat.double(a), Nat.double(b)) : Nat}

def double_sub(a, b):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      double_sub(p, q)

# A natural is at most its double: n <= double n.
law le_double:
  for n: Nat
  le(n, Nat.double(n))

def le_double(n):
  +n = n
  %Equal.sym(Nat, Nat.double(n), Nat.add(n, n), double_eq_add(n)) : le(n, _)
  le_add_right(n, n)

# Doubling preserves the order: a <= b implies double a <= double b.
law double_le_double:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  le(Nat.double(a), Nat.double(b))

def double_le_double(a, b, h):
  +a = a
  +b = b
  +h = h
  %Equal.sym(Nat, Nat.double(a), Nat.add(a, a), double_eq_add(a)) : le(_, Nat.double(b))
  %Equal.sym(Nat, Nat.double(b), Nat.add(b, b), double_eq_add(b)) : le(Nat.add(a, a), _)
  add_le_add(a, a, b, b, h, h)

# Doubling preserves the strict order: a < b implies double a < double b.
law double_lt_double:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  lt(Nat.double(a), Nat.double(b))

def double_lt_double(a, b, h):
  +a = a
  +b = b
  +h = h
  %Equal.sym(Nat, Nat.double(a), Nat.add(a, a), double_eq_add(a)) : lt(_, Nat.double(b))
  %Equal.sym(Nat, Nat.double(b), Nat.add(b, b), double_eq_add(b)) : lt(Nat.add(a, a), _)
  add_lt_add(a, a, b, b, h, h)

# Twice the half plus the parity is the number: double (n / 2) + n % 2 = n.
law double_div_two_add_mod_two:
  for n: Nat
  {Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)) == n : Nat}

def double_div_two_add_mod_two(n):
  +n = n
  %Equal.sym(Nat, Nat.double(Nat.div(n, 2n)), Nat.mul(2n, Nat.div(n, 2n)), double_eq_two_mul(Nat.div(n, 2n))) : {Nat.add(_, Nat.mod(n, 2n)) == n : Nat}
  div_add_mod(n, 2n)

# Adding the same amount on the right does not change the order test: a <= b tests as a + k <= b + k.
law add_le_add_iff_right:
  for a: Nat
  for b: Nat
  for k: Nat
  {Nat.is_le(a, b) == Nat.is_le(Nat.add(a, k), Nat.add(b, k)) : Bool}

def add_le_add_iff_right(a, b, k):
  +a = a
  +b = b
  +k = k
  %add_comm(k, a) : {Nat.is_le(a, b) == Nat.is_le(_, Nat.add(b, k)) : Bool}
  %add_comm(k, b) : {Nat.is_le(a, b) == Nat.is_le(Nat.add(k, a), _) : Bool}
  add_le_add_iff_left(k, a, b)

# Adding the same amount on the left does not change the equality test: a = b tests as k + a = k + b.
law add_left_cancel_iff:
  for k: Nat
  for -a: Nat
  for -b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(Nat.add(k, a), Nat.add(k, b)) : Bool}

def add_left_cancel_iff(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+p:
      add_left_cancel_iff(p, a, b)

# Adding the same amount on the right does not change the equality test: a = b tests as a + k = b + k.
law add_right_cancel_iff:
  for a: Nat
  for b: Nat
  for k: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(Nat.add(a, k), Nat.add(b, k)) : Bool}

def add_right_cancel_iff(a, b, k):
  +a = a
  +b = b
  +k = k
  %add_comm(k, a) : {Nat.is_eq(a, b) == Nat.is_eq(_, Nat.add(b, k)) : Bool}
  %add_comm(k, b) : {Nat.is_eq(a, b) == Nat.is_eq(Nat.add(k, a), _) : Bool}
  add_left_cancel_iff(k, a, b)

# Subtracting from the left summand commutes with adding the right one: k <= n implies (n + m) - k = (n - k) + m.
law sub_add_comm:
  for n: Nat
  for m: Nat
  for k: Nat
  for h: le(k, n)
  {Nat.sub(Nat.add(n, m), k) == Nat.add(Nat.sub(n, k), m) : Nat}

def sub_add_comm(n, m, k, h):
  +n = n
  +m = m
  +k = k
  %add_comm(m, n) : {Nat.sub(_, k) == Nat.add(Nat.sub(n, k), m) : Nat}
  %add_comm(m, Nat.sub(n, k)) : {Nat.sub(Nat.add(m, n), k) == _ : Nat}
  add_sub_assoc(k, n, h, m)

# A lower bound of both b and c is a lower bound of their minimum: a <= b and a <= c imply a <= min b c.
law le_min_of_le_of_le:
  for a: Nat
  for b: Nat
  for c: Nat
  for hb: le(a, b)
  for hc: le(a, c)
  le(a, Nat.min(b, c))

def le_min_of_le_of_le(a, b, c, hb, hc):
  +a = a
  +b = b
  +c = c
  %Equal.sym(Bool, Nat.is_le(a, Nat.min(b, c)), Bool.and(Nat.is_le(a, b), Nat.is_le(a, c)), le_min(a, b, c)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(a, b), True{}, hb) : {Bool.and(_, Nat.is_le(a, c)) == True{} : Bool}
  hc

# An upper bound of both a and b bounds their maximum: a <= c and b <= c imply max a b <= c.
law max_le_of_le_of_le:
  for a: Nat
  for b: Nat
  for c: Nat
  for ha: le(a, c)
  for hb: le(b, c)
  le(Nat.max(a, b), c)

def max_le_of_le_of_le(a, b, c, ha, hb):
  +a = a
  +b = b
  +c = c
  %Equal.sym(Bool, Nat.is_le(Nat.max(a, b), c), Bool.and(Nat.is_le(a, c), Nat.is_le(b, c)), max_le(a, b, c)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(a, c), True{}, ha) : {Bool.and(_, Nat.is_le(b, c)) == True{} : Bool}
  hb

# Multiplying n by two gives n + n.
law mul_two:
  for n: Nat
  {Nat.mul(n, 2n) == Nat.add(n, n) : Nat}

def mul_two(n):
  +n = n
  %mul_comm(2n, n) : {_ == Nat.add(n, n) : Nat}
  two_mul(n)

# Squaring n gives n times n.
law pow_two:
  for n: Nat
  {Nat.pow(n, 2n) == Nat.mul(n, n) : Nat}

def pow_two(n):
  +n = n
  %Equal.sym(Nat, Nat.mul(n, 1n), n, mul_one(n)) : {Nat.mul(n, _) == Nat.mul(n, n) : Nat}
  {==}

# The minimum of two numbers is at most their maximum.
law min_le_max:
  for a: Nat
  for b: Nat
  {Nat.is_le(Nat.min(a, b), Nat.max(a, b)) == True{} : Bool}

def min_le_max(a, b):
  +a = a
  +b = b
  le_trans(Nat.min(a, b), a, Nat.max(a, b), min_le_left(a, b), le_max_left(a, b))

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Zero is a right identity for addition: x + 0 = x, reversed to rewrite toward the simple side.
law add_zero_sym:
  for x: Nat
  {x == Nat.add(x, 0n) : Nat}

def add_zero_sym(x):
  Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x))

# Zero is a left identity for addition: 0 + x = x, reversed to rewrite toward the simple side.
law zero_add_sym:
  for -x: Nat
  {x == Nat.add(0n, x) : Nat}

def zero_add_sym(x):
  Equal.sym(Nat, Nat.add(0n, x), x, zero_add(x))

# Adding a successor on the right: n + (m + 1) = (n + m) + 1, reversed to rewrite toward the simple side.
law add_succ_sym:
  for n: Nat
  for -m: Nat
  {1n+Nat.add(n, m) == Nat.add(n, 1n+m) : Nat}

def add_succ_sym(n, m):
  Equal.sym(Nat, Nat.add(n, 1n+m), 1n+Nat.add(n, m), add_succ(n, m))

# Adding a successor on the left: (n + 1) + m = (n + m) + 1, reversed to rewrite toward the simple side.
law succ_add_sym:
  for -n: Nat
  for -m: Nat
  {1n+Nat.add(n, m) == Nat.add(1n+n, m) : Nat}

def succ_add_sym(n, m):
  Equal.sym(Nat, Nat.add(1n+n, m), 1n+Nat.add(n, m), succ_add(n, m))

# Addition is commutative: n + m = m + n, reversed to rewrite toward the simple side.
law add_comm_sym:
  for n: Nat
  for m: Nat
  {Nat.add(m, n) == Nat.add(n, m) : Nat}

def add_comm_sym(n, m):
  Equal.sym(Nat, Nat.add(n, m), Nat.add(m, n), add_comm(n, m))

# Addition is associative: (a + b) + c = a + (b + c), reversed to rewrite toward the simple side.
law add_assoc_sym:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

def add_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c))

# Left commutativity of addition: a + (b + c) = b + (a + c), reversed to rewrite toward the simple side.
law add_left_comm_sym:
  for a: Nat
  for b: Nat
  for -c: Nat
  {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_left_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(b, Nat.add(a, c)), add_left_comm(a, b, c))

# Right commutativity of addition: (a + b) + c = (a + c) + b, reversed to rewrite toward the simple side.
law add_right_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(a, b), c) : Nat}

def add_right_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a, c), b), add_right_comm(a, b, c))

# Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d), reversed to rewrite toward the simple side.
law add_add_add_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  for -d: Nat
  {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}

def add_add_add_comm_sym(a, b, c, d):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(Nat.add(a, c), Nat.add(b, d)), add_add_add_comm(a, b, c, d))

# Zero absorbs multiplication on the right: x * 0 = 0, reversed to rewrite toward the simple side.
law mul_zero_sym:
  for x: Nat
  {0n == Nat.mul(x, 0n) : Nat}

def mul_zero_sym(x):
  Equal.sym(Nat, Nat.mul(x, 0n), 0n, mul_zero(x))

# Zero absorbs multiplication on the left: 0 * x = 0, reversed to rewrite toward the simple side.
law zero_mul_sym:
  for -x: Nat
  {0n == Nat.mul(0n, x) : Nat}

def zero_mul_sym(x):
  Equal.sym(Nat, Nat.mul(0n, x), 0n, zero_mul(x))

# One is a right identity for multiplication: x * 1 = x, reversed to rewrite toward the simple side.
law mul_one_sym:
  for x: Nat
  {x == Nat.mul(x, 1n) : Nat}

def mul_one_sym(x):
  Equal.sym(Nat, Nat.mul(x, 1n), x, mul_one(x))

# One is a left identity for multiplication: 1 * x = x, reversed to rewrite toward the simple side.
law one_mul_sym:
  for x: Nat
  {x == Nat.mul(1n, x) : Nat}

def one_mul_sym(x):
  Equal.sym(Nat, Nat.mul(1n, x), x, one_mul(x))

# Multiplying by a successor on the right: n * (m + 1) = n * m + n, reversed to rewrite toward the simple side.
law mul_succ_sym:
  for n: Nat
  for m: Nat
  {Nat.add(Nat.mul(n, m), n) == Nat.mul(n, 1n+m) : Nat}

def mul_succ_sym(n, m):
  Equal.sym(Nat, Nat.mul(n, 1n+m), Nat.add(Nat.mul(n, m), n), mul_succ(n, m))

# Multiplying by a successor on the left: (n + 1) * m = n * m + m, reversed to rewrite toward the simple side.
law succ_mul_sym:
  for n: Nat
  for m: Nat
  {Nat.add(Nat.mul(n, m), m) == Nat.mul(1n+n, m) : Nat}

def succ_mul_sym(n, m):
  Equal.sym(Nat, Nat.mul(1n+n, m), Nat.add(Nat.mul(n, m), m), succ_mul(n, m))

# Multiplication is commutative: n * m = m * n, reversed to rewrite toward the simple side.
law mul_comm_sym:
  for n: Nat
  for m: Nat
  {Nat.mul(m, n) == Nat.mul(n, m) : Nat}

def mul_comm_sym(n, m):
  Equal.sym(Nat, Nat.mul(n, m), Nat.mul(m, n), mul_comm(n, m))

# Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c, reversed to rewrite toward the simple side.
law add_mul_sym:
  for a: Nat
  for -b: Nat
  for c: Nat
  {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}

def add_mul_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(Nat.add(a, b), c), Nat.add(Nat.mul(a, c), Nat.mul(b, c)), add_mul(a, b, c))

# Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c, reversed to rewrite toward the simple side.
law mul_add_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}

def mul_add_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)), mul_add(a, b, c))

# Multiplication is associative: (a * b) * c = a * (b * c), reversed to rewrite toward the simple side.
law mul_assoc_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}

def mul_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), mul_assoc(a, b, c))

# Subtracting zero changes nothing: n - 0 = n, reversed to rewrite toward the simple side.
law sub_zero_sym:
  for n: Nat
  {n == Nat.sub(n, 0n) : Nat}

def sub_zero_sym(n):
  Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero(n))

# Truncated subtraction from zero is zero: 0 - n = 0, reversed to rewrite toward the simple side.
law zero_sub_sym:
  for n: Nat
  {0n == Nat.sub(0n, n) : Nat}

def zero_sub_sym(n):
  Equal.sym(Nat, Nat.sub(0n, n), 0n, zero_sub(n))

# A natural minus itself is zero: n - n = 0, reversed to rewrite toward the simple side.
law sub_self_sym:
  for n: Nat
  {0n == Nat.sub(n, n) : Nat}

def sub_self_sym(n):
  Equal.sym(Nat, Nat.sub(n, n), 0n, sub_self(n))

# Subtracting successors: (n + 1) - (m + 1) = n - m, reversed to rewrite toward the simple side.
law succ_sub_succ_sym:
  for -n: Nat
  for -m: Nat
  {Nat.sub(n, m) == Nat.sub(1n+n, 1n+m) : Nat}

def succ_sub_succ_sym(n, m):
  Equal.sym(Nat, Nat.sub(1n+n, 1n+m), Nat.sub(n, m), succ_sub_succ(n, m))

# Adding then subtracting m cancels: (n + m) - m = n, reversed to rewrite toward the simple side.
law add_sub_cancel_sym:
  for n: Nat
  for m: Nat
  {n == Nat.sub(Nat.add(n, m), m) : Nat}

def add_sub_cancel_sym(n, m):
  Equal.sym(Nat, Nat.sub(Nat.add(n, m), m), n, add_sub_cancel(n, m))

# Adding then subtracting n cancels: (n + m) - n = m, reversed to rewrite toward the simple side.
law add_sub_cancel_left_sym:
  for n: Nat
  for m: Nat
  {m == Nat.sub(Nat.add(n, m), n) : Nat}

def add_sub_cancel_left_sym(n, m):
  Equal.sym(Nat, Nat.sub(Nat.add(n, m), n), m, add_sub_cancel_left(n, m))

# Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k), reversed to rewrite toward the simple side.
law sub_sub_sym:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(n, Nat.add(m, k)) == Nat.sub(Nat.sub(n, m), k) : Nat}

def sub_sub_sym(n, m, k):
  Equal.sym(Nat, Nat.sub(Nat.sub(n, m), k), Nat.sub(n, Nat.add(m, k)), sub_sub(n, m, k))

# The division equation, for a positive divisor 1 + b: (a / (1 + b)) * (1 + b) + a % (1 + b) = a, reversed to rewrite toward the simple side.
law div_mod_eq_sym:
  for +a: Nat
  for +b: Nat
  {a == Nat.add(Nat.mul(Nat.div(a, 1n+b), 1n+b), Nat.mod(a, 1n+b)) : Nat}

def div_mod_eq_sym(a, b):
  Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(a, 1n+b), 1n+b), Nat.mod(a, 1n+b)), a, div_mod_eq(a, b))

# Adding the divisor adds one to the quotient: ((1 + b) + a) / (1 + b) = 1 + a / (1 + b), reversed to rewrite toward the simple side.
law add_div_left_sym:
  for +a: Nat
  for +b: Nat
  {1n+Nat.div(a, 1n+b) == Nat.div(Nat.add(1n+b, a), 1n+b) : Nat}

def add_div_left_sym(a, b):
  Equal.sym(Nat, Nat.div(Nat.add(1n+b, a), 1n+b), 1n+Nat.div(a, 1n+b), add_div_left(a, b))

# A quotient is compared by multiplying back: n <= a / (1 + b) tests as n * (1 + b) <= a, reversed to rewrite toward the simple side.
law le_div_iff_mul_le_sym:
  for n: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.mul(n, 1n+b), a) == Nat.is_le(n, Nat.div(a, 1n+b)) : Bool}

def le_div_iff_mul_le_sym(n, a, b):
  Equal.sym(Bool, Nat.is_le(n, Nat.div(a, 1n+b)), Nat.is_le(Nat.mul(n, 1n+b), a), le_div_iff_mul_le(n, a, b))

# Minimum is commutative, reversed to rewrite toward the simple side.
law min_comm_sym:
  for a: Nat
  for b: Nat
  {Nat.min(b, a) == Nat.min(a, b) : Nat}

def min_comm_sym(a, b):
  Equal.sym(Nat, Nat.min(a, b), Nat.min(b, a), min_comm(a, b))

# Maximum is commutative, reversed to rewrite toward the simple side.
law max_comm_sym:
  for a: Nat
  for b: Nat
  {Nat.max(b, a) == Nat.max(a, b) : Nat}

def max_comm_sym(a, b):
  Equal.sym(Nat, Nat.max(a, b), Nat.max(b, a), max_comm(a, b))

# The minimum of a natural and itself is itself, reversed to rewrite toward the simple side.
law min_self_sym:
  for a: Nat
  {a == Nat.min(a, a) : Nat}

def min_self_sym(a):
  Equal.sym(Nat, Nat.min(a, a), a, min_self(a))

# The maximum of a natural and itself is itself, reversed to rewrite toward the simple side.
law max_self_sym:
  for a: Nat
  {a == Nat.max(a, a) : Nat}

def max_self_sym(a):
  Equal.sym(Nat, Nat.max(a, a), a, max_self(a))

# The minimum with zero is zero: min(a, 0) = 0, reversed to rewrite toward the simple side.
law min_zero_sym:
  for a: Nat
  {0n == Nat.min(a, 0n) : Nat}

def min_zero_sym(a):
  Equal.sym(Nat, Nat.min(a, 0n), 0n, min_zero(a))

# The minimum with zero is zero: min(0, a) = 0, reversed to rewrite toward the simple side.
law zero_min_sym:
  for a: Nat
  {0n == Nat.min(0n, a) : Nat}

def zero_min_sym(a):
  Equal.sym(Nat, Nat.min(0n, a), 0n, zero_min(a))

# Zero is an identity for maximum: max(a, 0) = a, reversed to rewrite toward the simple side.
law max_zero_sym:
  for a: Nat
  {a == Nat.max(a, 0n) : Nat}

def max_zero_sym(a):
  Equal.sym(Nat, Nat.max(a, 0n), a, max_zero(a))

# Zero is an identity for maximum: max(0, a) = a, reversed to rewrite toward the simple side.
law zero_max_sym:
  for a: Nat
  {a == Nat.max(0n, a) : Nat}

def zero_max_sym(a):
  Equal.sym(Nat, Nat.max(0n, a), a, zero_max(a))

# Minimum is associative, reversed to rewrite toward the simple side.
law min_assoc_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(a, Nat.min(b, c)) == Nat.min(Nat.min(a, b), c) : Nat}

def min_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.min(Nat.min(a, b), c), Nat.min(a, Nat.min(b, c)), min_assoc(a, b, c))

# Maximum is associative, reversed to rewrite toward the simple side.
law max_assoc_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(a, Nat.max(b, c)) == Nat.max(Nat.max(a, b), c) : Nat}

def max_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.max(Nat.max(a, b), c), Nat.max(a, Nat.max(b, c)), max_assoc(a, b, c))

# The minimum plus the maximum is the sum: min(a, b) + max(a, b) = a + b, reversed to rewrite toward the simple side.
law min_add_max_sym:
  for a: Nat
  for b: Nat
  {Nat.add(a, b) == Nat.add(Nat.min(a, b), Nat.max(a, b)) : Nat}

def min_add_max_sym(a, b):
  Equal.sym(Nat, Nat.add(Nat.min(a, b), Nat.max(a, b)), Nat.add(a, b), min_add_max(a, b))

# Any natural to the power zero is one, reversed to rewrite toward the simple side.
law pow_zero_sym:
  for -a: Nat
  {1n == Nat.pow(a, 0n) : Nat}

def pow_zero_sym(a):
  Equal.sym(Nat, Nat.pow(a, 0n), 1n, pow_zero(a))

# A power with a successor exponent: a^(n+1) = a * a^n, reversed to rewrite toward the simple side.
law pow_succ_sym:
  for -a: Nat
  for -n: Nat
  {Nat.mul(a, Nat.pow(a, n)) == Nat.pow(a, 1n+n) : Nat}

def pow_succ_sym(a, n):
  Equal.sym(Nat, Nat.pow(a, 1n+n), Nat.mul(a, Nat.pow(a, n)), pow_succ(a, n))

# Any natural to the power one is itself, reversed to rewrite toward the simple side.
law pow_one_sym:
  for a: Nat
  {a == Nat.pow(a, 1n) : Nat}

def pow_one_sym(a):
  Equal.sym(Nat, Nat.pow(a, 1n), a, pow_one(a))

# One to any power is one, reversed to rewrite toward the simple side.
law one_pow_sym:
  for n: Nat
  {1n == Nat.pow(1n, n) : Nat}

def one_pow_sym(n):
  Equal.sym(Nat, Nat.pow(1n, n), 1n, one_pow(n))

# Exponents add under multiplication: a^(m+n) = a^m * a^n, reversed to rewrite toward the simple side.
law pow_add_sym:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) == Nat.pow(a, Nat.add(m, n)) : Nat}

def pow_add_sym(a, m, n):
  Equal.sym(Nat, Nat.pow(a, Nat.add(m, n)), Nat.mul(Nat.pow(a, m), Nat.pow(a, n)), pow_add(a, m, n))

# Doubling is adding a natural to itself, reversed to rewrite toward the simple side.
law double_eq_add_sym:
  for n: Nat
  {Nat.add(n, n) == Nat.double(n) : Nat}

def double_eq_add_sym(n):
  Equal.sym(Nat, Nat.double(n), Nat.add(n, n), double_eq_add(n))

# Every natural tests equal to itself, reversed to rewrite toward the simple side.
law is_eq_refl_sym:
  for n: Nat
  {True{} == Nat.is_eq(n, n) : Bool}

def is_eq_refl_sym(n):
  Equal.sym(Bool, Nat.is_eq(n, n), True{}, is_eq_refl(n))

# The equality test is symmetric, reversed to rewrite toward the simple side.
law is_eq_comm_sym:
  for a: Nat
  for b: Nat
  {Nat.is_eq(b, a) == Nat.is_eq(a, b) : Bool}

def is_eq_comm_sym(a, b):
  Equal.sym(Bool, Nat.is_eq(a, b), Nat.is_eq(b, a), is_eq_comm(a, b))

# A >= b tests the same as b <= a, reversed to rewrite toward the simple side.
law is_ge_eq_is_le_sym:
  for a: Nat
  for b: Nat
  {Nat.is_le(b, a) == Nat.is_ge(a, b) : Bool}

def is_ge_eq_is_le_sym(a, b):
  Equal.sym(Bool, Nat.is_ge(a, b), Nat.is_le(b, a), is_ge_eq_is_le(a, b))

# A > b tests the same as b < a, reversed to rewrite toward the simple side.
law is_gt_eq_is_lt_sym:
  for a: Nat
  for b: Nat
  {Nat.is_lt(b, a) == Nat.is_gt(a, b) : Bool}

def is_gt_eq_is_lt_sym(a, b):
  Equal.sym(Bool, Nat.is_gt(a, b), Nat.is_lt(b, a), is_gt_eq_is_lt(a, b))

# A < b tests the same as a + 1 <= b, reversed to rewrite toward the simple side.
law is_lt_eq_succ_le_sym:
  for a: Nat
  for b: Nat
  {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}

def is_lt_eq_succ_le_sym(a, b):
  Equal.sym(Bool, Nat.is_lt(a, b), Nat.is_le(1n+a, b), is_lt_eq_succ_le(a, b))

# Not (a <= b) tests the same as b < a, reversed to rewrite toward the simple side.
law not_is_le_sym:
  for a: Nat
  for b: Nat
  {Nat.is_lt(b, a) == Bool.not(Nat.is_le(a, b)) : Bool}

def not_is_le_sym(a, b):
  Equal.sym(Bool, Bool.not(Nat.is_le(a, b)), Nat.is_lt(b, a), not_is_le(a, b))

# Not (a < b) tests the same as b <= a, reversed to rewrite toward the simple side.
law not_is_lt_sym:
  for a: Nat
  for b: Nat
  {Nat.is_le(b, a) == Bool.not(Nat.is_lt(a, b)) : Bool}

def not_is_lt_sym(a, b):
  Equal.sym(Bool, Bool.not(Nat.is_lt(a, b)), Nat.is_le(b, a), not_is_lt(a, b))

# Adding the same amount on the left does not change the order test: a <= b tests as k + a <= k + b, reversed to rewrite toward the simple side.
law add_le_add_iff_left_sym:
  for k: Nat
  for -a: Nat
  for -b: Nat
  {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == Nat.is_le(a, b) : Bool}

def add_le_add_iff_left_sym(k, a, b):
  Equal.sym(Bool, Nat.is_le(a, b), Nat.is_le(Nat.add(k, a), Nat.add(k, b)), add_le_add_iff_left(k, a, b))

# A sum is at most c exactly when a <= c and b <= c - a: a + b <= c tests as both, reversed to rewrite toward the simple side.
law le_and_le_sub_iff_add_le_sym:
  for a: Nat
  for -b: Nat
  for c: Nat
  {Nat.is_le(Nat.add(a, b), c) == Bool.and(Nat.is_le(a, c), Nat.is_le(b, Nat.sub(c, a))) : Bool}

def le_and_le_sub_iff_add_le_sym(a, b, c):
  Equal.sym(Bool, Bool.and(Nat.is_le(a, c), Nat.is_le(b, Nat.sub(c, a))), Nat.is_le(Nat.add(a, b), c), le_and_le_sub_iff_add_le(a, b, c))

# The minimum is at most c exactly when one argument is: min a b <= c tests as a <= c or b <= c, reversed to rewrite toward the simple side.
law min_le_iff_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.or(Nat.is_le(a, c), Nat.is_le(b, c)) == Nat.is_le(Nat.min(a, b), c) : Bool}

def min_le_iff_sym(a, b, c):
  Equal.sym(Bool, Nat.is_le(Nat.min(a, b), c), Bool.or(Nat.is_le(a, c), Nat.is_le(b, c)), min_le_iff(a, b, c))

# The maximum is above a exactly when one argument is: a < max b c tests as a < b or a < c, reversed to rewrite toward the simple side.
law lt_max_iff_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.or(Nat.is_lt(a, b), Nat.is_lt(a, c)) == Nat.is_lt(a, Nat.max(b, c)) : Bool}

def lt_max_iff_sym(a, b, c):
  Equal.sym(Bool, Nat.is_lt(a, Nat.max(b, c)), Bool.or(Nat.is_lt(a, b), Nat.is_lt(a, c)), lt_max_iff(a, b, c))

# Comparing against a difference is comparing the sum: a < c - b tests as b + a < c, reversed to rewrite toward the simple side.
law lt_sub_iff_add_lt_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.is_lt(Nat.add(b, a), c) == Nat.is_lt(a, Nat.sub(c, b)) : Bool}

def lt_sub_iff_add_lt_sym(a, b, c):
  Equal.sym(Bool, Nat.is_lt(a, Nat.sub(c, b)), Nat.is_lt(Nat.add(b, a), c), lt_sub_iff_add_lt(a, b, c))

# Zero divided by anything is zero: 0 / b = 0, reversed to rewrite toward the simple side.
law zero_div_sym:
  for b: Nat
  {0n == Nat.div(0n, b) : Nat}

def zero_div_sym(b):
  Equal.sym(Nat, Nat.div(0n, b), 0n, zero_div(b))

# Zero modulo anything is zero: 0 % b = 0, reversed to rewrite toward the simple side.
law zero_mod_sym:
  for b: Nat
  {0n == Nat.mod(0n, b) : Nat}

def zero_mod_sym(b):
  Equal.sym(Nat, Nat.mod(0n, b), 0n, zero_mod(b))

# Dividing by one changes nothing: a / 1 = a, reversed to rewrite toward the simple side.
law div_one_sym:
  for a: Nat
  {a == Nat.div(a, 1n) : Nat}

def div_one_sym(a):
  Equal.sym(Nat, Nat.div(a, 1n), a, div_one(a))

# Any natural modulo one is zero: a % 1 = 0, reversed to rewrite toward the simple side.
law mod_one_sym:
  for a: Nat
  {0n == Nat.mod(a, 1n) : Nat}

def mod_one_sym(a):
  Equal.sym(Nat, Nat.mod(a, 1n), 0n, mod_one(a))

# A natural modulo itself is zero: n % n = 0, reversed to rewrite toward the simple side.
law mod_self_sym:
  for n: Nat
  {0n == Nat.mod(n, n) : Nat}

def mod_self_sym(n):
  Equal.sym(Nat, Nat.mod(n, n), 0n, mod_self(n))

# A positive natural divided by itself is one: (1 + b) / (1 + b) = 1, reversed to rewrite toward the simple side.
law div_self_sym:
  for b: Nat
  {1n == Nat.div(1n+b, 1n+b) : Nat}

def div_self_sym(b):
  Equal.sym(Nat, Nat.div(1n+b, 1n+b), 1n, div_self(b))

# Taking a remainder twice is taking it once: (a % n) % n = a % n, reversed to rewrite toward the simple side.
law mod_mod_sym:
  for a: Nat
  for n: Nat
  {Nat.mod(a, n) == Nat.mod(Nat.mod(a, n), n) : Nat}

def mod_mod_sym(a, n):
  Equal.sym(Nat, Nat.mod(Nat.mod(a, n), n), Nat.mod(a, n), mod_mod(a, n))

# Adding the divisor does not change the remainder: (b + a) % b = a % b, reversed to rewrite toward the simple side.
law add_mod_left_sym:
  for a: Nat
  for b: Nat
  {Nat.mod(a, b) == Nat.mod(Nat.add(b, a), b) : Nat}

def add_mod_left_sym(a, b):
  Equal.sym(Nat, Nat.mod(Nat.add(b, a), b), Nat.mod(a, b), add_mod_left(a, b))

# Multiplying by a positive divisor then dividing by it cancels: (a * (1 + b)) / (1 + b) = a, reversed to rewrite toward the simple side.
law mul_div_cancel_sym:
  for a: Nat
  for b: Nat
  {a == Nat.div(Nat.mul(a, 1n+b), 1n+b) : Nat}

def mul_div_cancel_sym(a, b):
  Equal.sym(Nat, Nat.div(Nat.mul(a, 1n+b), 1n+b), a, mul_div_cancel(a, b))

# Multiplying on the left by a positive divisor then dividing by it cancels: ((1 + b) * a) / (1 + b) = a, reversed to rewrite toward the simple side.
law mul_div_cancel_left_sym:
  for a: Nat
  for b: Nat
  {a == Nat.div(Nat.mul(1n+b, a), 1n+b) : Nat}

def mul_div_cancel_left_sym(a, b):
  Equal.sym(Nat, Nat.div(Nat.mul(1n+b, a), 1n+b), a, mul_div_cancel_left(a, b))

# A multiple of b leaves no remainder modulo b: (a * b) % b = 0, reversed to rewrite toward the simple side.
law mul_mod_left_sym:
  for a: Nat
  for b: Nat
  {0n == Nat.mod(Nat.mul(a, b), b) : Nat}

def mul_mod_left_sym(a, b):
  Equal.sym(Nat, Nat.mod(Nat.mul(a, b), b), 0n, mul_mod_left(a, b))

# A multiple of a leaves no remainder modulo a: (a * b) % a = 0, reversed to rewrite toward the simple side.
law mul_mod_right_sym:
  for a: Nat
  for b: Nat
  {0n == Nat.mod(Nat.mul(a, b), a) : Nat}

def mul_mod_right_sym(a, b):
  Equal.sym(Nat, Nat.mod(Nat.mul(a, b), a), 0n, mul_mod_right(a, b))

# The remainder plus the divisor times the quotient is the dividend: a % b + b * (a / b) = a, reversed to rewrite toward the simple side.
law mod_add_div_sym:
  for a: Nat
  for b: Nat
  {a == Nat.add(Nat.mod(a, b), Nat.mul(b, Nat.div(a, b))) : Nat}

def mod_add_div_sym(a, b):
  Equal.sym(Nat, Nat.add(Nat.mod(a, b), Nat.mul(b, Nat.div(a, b))), a, mod_add_div(a, b))

# Left commutativity of multiplication: a * (b * c) = b * (a * c), reversed to rewrite toward the simple side.
law mul_left_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(b, Nat.mul(a, c)) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def mul_left_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(a, Nat.mul(b, c)), Nat.mul(b, Nat.mul(a, c)), mul_left_comm(a, b, c))

# Right commutativity of multiplication: (a * b) * c = (a * c) * b, reversed to rewrite toward the simple side.
law mul_right_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.mul(a, c), b) == Nat.mul(Nat.mul(a, b), c) : Nat}

def mul_right_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(Nat.mul(a, c), b), mul_right_comm(a, b, c))

# Four-way regrouping of a product: (a * b) * (c * d) = (a * c) * (b * d), reversed to rewrite toward the simple side.
law mul_mul_mul_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  {Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) == Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) : Nat}

def mul_mul_mul_comm_sym(a, b, c, d):
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), Nat.mul(c, d)), Nat.mul(Nat.mul(a, c), Nat.mul(b, d)), mul_mul_mul_comm(a, b, c, d))

# Zero to a positive power is zero: 0^(n+1) = 0, reversed to rewrite toward the simple side.
law zero_pow_sym:
  for -n: Nat
  {0n == Nat.pow(0n, 1n+n) : Nat}

def zero_pow_sym(n):
  Equal.sym(Nat, Nat.pow(0n, 1n+n), 0n, zero_pow(n))

# A power of a product is the product of the powers: (a * b)^n = a^n * b^n, reversed to rewrite toward the simple side.
law mul_pow_sym:
  for +a: Nat
  for +b: Nat
  for n: Nat
  {Nat.mul(Nat.pow(a, n), Nat.pow(b, n)) == Nat.pow(Nat.mul(a, b), n) : Nat}

def mul_pow_sym(a, b, n):
  Equal.sym(Nat, Nat.pow(Nat.mul(a, b), n), Nat.mul(Nat.pow(a, n), Nat.pow(b, n)), mul_pow(a, b, n))

# Exponents multiply under repeated powers: a^(m * n) = (a^m)^n, reversed to rewrite toward the simple side.
law pow_mul_sym:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(Nat.pow(a, m), n) == Nat.pow(a, Nat.mul(m, n)) : Nat}

def pow_mul_sym(a, m, n):
  Equal.sym(Nat, Nat.pow(a, Nat.mul(m, n)), Nat.pow(Nat.pow(a, m), n), pow_mul(a, m, n))

# A common left summand cancels in a difference: (k + n) - (k + m) = n - m, reversed to rewrite toward the simple side.
law add_sub_add_left_sym:
  for k: Nat
  for -n: Nat
  for -m: Nat
  {Nat.sub(n, m) == Nat.sub(Nat.add(k, n), Nat.add(k, m)) : Nat}

def add_sub_add_left_sym(k, n, m):
  Equal.sym(Nat, Nat.sub(Nat.add(k, n), Nat.add(k, m)), Nat.sub(n, m), add_sub_add_left(k, n, m))

# A common right summand cancels in a difference: (n + k) - (m + k) = n - m, reversed to rewrite toward the simple side.
law add_sub_add_right_sym:
  for n: Nat
  for k: Nat
  for m: Nat
  {Nat.sub(n, m) == Nat.sub(Nat.add(n, k), Nat.add(m, k)) : Nat}

def add_sub_add_right_sym(n, k, m):
  Equal.sym(Nat, Nat.sub(Nat.add(n, k), Nat.add(m, k)), Nat.sub(n, m), add_sub_add_right(n, k, m))

# Multiplication distributes over subtraction on the right: (n - m) * k = n * k - m * k, reversed to rewrite toward the simple side.
law sub_mul_sym:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(Nat.mul(n, k), Nat.mul(m, k)) == Nat.mul(Nat.sub(n, m), k) : Nat}

def sub_mul_sym(n, m, k):
  Equal.sym(Nat, Nat.mul(Nat.sub(n, m), k), Nat.sub(Nat.mul(n, k), Nat.mul(m, k)), sub_mul(n, m, k))

# Multiplication distributes over subtraction on the left: n * (m - k) = n * m - n * k, reversed to rewrite toward the simple side.
law mul_sub_sym:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(Nat.mul(n, m), Nat.mul(n, k)) == Nat.mul(n, Nat.sub(m, k)) : Nat}

def mul_sub_sym(n, m, k):
  Equal.sym(Nat, Nat.mul(n, Nat.sub(m, k)), Nat.sub(Nat.mul(n, m), Nat.mul(n, k)), mul_sub(n, m, k))

# A number is at most the minimum exactly when it is at most both: a <= min b c tests as a <= b and a <= c (Mathlib's le_min_iff; the implication is le_min_of_le_of_le), reversed to rewrite toward the simple side.
law le_min_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.and(Nat.is_le(a, b), Nat.is_le(a, c)) == Nat.is_le(a, Nat.min(b, c)) : Bool}

def le_min_sym(a, b, c):
  Equal.sym(Bool, Nat.is_le(a, Nat.min(b, c)), Bool.and(Nat.is_le(a, b), Nat.is_le(a, c)), le_min(a, b, c))

# The maximum is at most c exactly when both arguments are: max a b <= c tests as a <= c and b <= c (Mathlib's max_le_iff; the implication is max_le_of_le_of_le), reversed to rewrite toward the simple side.
law max_le_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.and(Nat.is_le(a, c), Nat.is_le(b, c)) == Nat.is_le(Nat.max(a, b), c) : Bool}

def max_le_sym(a, b, c):
  Equal.sym(Bool, Nat.is_le(Nat.max(a, b), c), Bool.and(Nat.is_le(a, c), Nat.is_le(b, c)), max_le(a, b, c))

# Below a successor means at most: m < n + 1 tests as m <= n, reversed to rewrite toward the simple side.
law lt_succ_iff_sym:
  for m: Nat
  for n: Nat
  {Nat.is_le(m, n) == Nat.is_lt(m, 1n+n) : Bool}

def lt_succ_iff_sym(m, n):
  Equal.sym(Bool, Nat.is_lt(m, 1n+n), Nat.is_le(m, n), lt_succ_iff(m, n))

# At most means below or equal: a <= b tests as a < b or a = b, reversed to rewrite toward the simple side.
law le_iff_lt_or_eq_sym:
  for a: Nat
  for b: Nat
  {Bool.or(Nat.is_lt(a, b), Nat.is_eq(a, b)) == Nat.is_le(a, b) : Bool}

def le_iff_lt_or_eq_sym(a, b):
  Equal.sym(Bool, Nat.is_le(a, b), Bool.or(Nat.is_lt(a, b), Nat.is_eq(a, b)), le_iff_lt_or_eq(a, b))

# Below means at most and different: a < b tests as a <= b and not a = b, reversed to rewrite toward the simple side.
law lt_iff_le_and_ne_sym:
  for a: Nat
  for b: Nat
  {Bool.and(Nat.is_le(a, b), Bool.not(Nat.is_eq(a, b))) == Nat.is_lt(a, b) : Bool}

def lt_iff_le_and_ne_sym(a, b):
  Equal.sym(Bool, Nat.is_lt(a, b), Bool.and(Nat.is_le(a, b), Bool.not(Nat.is_eq(a, b))), lt_iff_le_and_ne(a, b))

# Adding the same amount on the left does not change the strict order test: a < b tests as k + a < k + b, reversed to rewrite toward the simple side.
law add_lt_add_iff_left_sym:
  for k: Nat
  for -a: Nat
  for -b: Nat
  {Nat.is_lt(Nat.add(k, a), Nat.add(k, b)) == Nat.is_lt(a, b) : Bool}

def add_lt_add_iff_left_sym(k, a, b):
  Equal.sym(Bool, Nat.is_lt(a, b), Nat.is_lt(Nat.add(k, a), Nat.add(k, b)), add_lt_add_iff_left(k, a, b))

# Adding the same amount on the right does not change the strict order test: a < b tests as a + k < b + k, reversed to rewrite toward the simple side.
law add_lt_add_iff_right_sym:
  for a: Nat
  for b: Nat
  for k: Nat
  {Nat.is_lt(Nat.add(a, k), Nat.add(b, k)) == Nat.is_lt(a, b) : Bool}

def add_lt_add_iff_right_sym(a, b, k):
  Equal.sym(Bool, Nat.is_lt(a, b), Nat.is_lt(Nat.add(a, k), Nat.add(b, k)), add_lt_add_iff_right(a, b, k))

# Minimum distributes over maximum on the left: min a (max b c) = max (min a b) (min a c), reversed to rewrite toward the simple side.
law min_max_distrib_left_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(Nat.min(a, b), Nat.min(a, c)) == Nat.min(a, Nat.max(b, c)) : Nat}

def min_max_distrib_left_sym(a, b, c):
  Equal.sym(Nat, Nat.min(a, Nat.max(b, c)), Nat.max(Nat.min(a, b), Nat.min(a, c)), min_max_distrib_left(a, b, c))

# Maximum distributes over minimum on the left: max a (min b c) = min (max a b) (max a c), reversed to rewrite toward the simple side.
law max_min_distrib_left_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(Nat.max(a, b), Nat.max(a, c)) == Nat.max(a, Nat.min(b, c)) : Nat}

def max_min_distrib_left_sym(a, b, c):
  Equal.sym(Nat, Nat.max(a, Nat.min(b, c)), Nat.min(Nat.max(a, b), Nat.max(a, c)), max_min_distrib_left(a, b, c))

# A common left summand leaves the minimum: min (a + b) (a + c) = a + min b c, reversed to rewrite toward the simple side.
law min_add_add_left_sym:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(a, Nat.min(b, c)) == Nat.min(Nat.add(a, b), Nat.add(a, c)) : Nat}

def min_add_add_left_sym(a, b, c):
  Equal.sym(Nat, Nat.min(Nat.add(a, b), Nat.add(a, c)), Nat.add(a, Nat.min(b, c)), min_add_add_left(a, b, c))

# A common right summand leaves the minimum: min (a + c) (b + c) = min a b + c, reversed to rewrite toward the simple side.
law min_add_add_right_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.min(a, b), c) == Nat.min(Nat.add(a, c), Nat.add(b, c)) : Nat}

def min_add_add_right_sym(a, b, c):
  Equal.sym(Nat, Nat.min(Nat.add(a, c), Nat.add(b, c)), Nat.add(Nat.min(a, b), c), min_add_add_right(a, b, c))

# A common left summand leaves the maximum: max (a + b) (a + c) = a + max b c, reversed to rewrite toward the simple side.
law max_add_add_left_sym:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(a, Nat.max(b, c)) == Nat.max(Nat.add(a, b), Nat.add(a, c)) : Nat}

def max_add_add_left_sym(a, b, c):
  Equal.sym(Nat, Nat.max(Nat.add(a, b), Nat.add(a, c)), Nat.add(a, Nat.max(b, c)), max_add_add_left(a, b, c))

# A common right summand leaves the maximum: max (a + c) (b + c) = max a b + c, reversed to rewrite toward the simple side.
law max_add_add_right_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.max(a, b), c) == Nat.max(Nat.add(a, c), Nat.add(b, c)) : Nat}

def max_add_add_right_sym(a, b, c):
  Equal.sym(Nat, Nat.max(Nat.add(a, c), Nat.add(b, c)), Nat.add(Nat.max(a, b), c), max_add_add_right(a, b, c))

# The minimum is below c exactly when one argument is: min a b < c tests as a < c or b < c, reversed to rewrite toward the simple side.
law min_lt_iff_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.or(Nat.is_lt(a, c), Nat.is_lt(b, c)) == Nat.is_lt(Nat.min(a, b), c) : Bool}

def min_lt_iff_sym(a, b, c):
  Equal.sym(Bool, Nat.is_lt(Nat.min(a, b), c), Bool.or(Nat.is_lt(a, c), Nat.is_lt(b, c)), min_lt_iff(a, b, c))

# A number is below the minimum exactly when it is below both: a < min b c tests as a < b and a < c, reversed to rewrite toward the simple side.
law lt_min_iff_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.and(Nat.is_lt(a, b), Nat.is_lt(a, c)) == Nat.is_lt(a, Nat.min(b, c)) : Bool}

def lt_min_iff_sym(a, b, c):
  Equal.sym(Bool, Nat.is_lt(a, Nat.min(b, c)), Bool.and(Nat.is_lt(a, b), Nat.is_lt(a, c)), lt_min_iff(a, b, c))

# The maximum is below c exactly when both arguments are: max a b < c tests as a < c and b < c, reversed to rewrite toward the simple side.
law max_lt_iff_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.and(Nat.is_lt(a, c), Nat.is_lt(b, c)) == Nat.is_lt(Nat.max(a, b), c) : Bool}

def max_lt_iff_sym(a, b, c):
  Equal.sym(Bool, Nat.is_lt(Nat.max(a, b), c), Bool.and(Nat.is_lt(a, c), Nat.is_lt(b, c)), max_lt_iff(a, b, c))

# A number is at most the maximum exactly when it is at most one argument: a <= max b c tests as a <= b or a <= c, reversed to rewrite toward the simple side.
law le_max_iff_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Bool.or(Nat.is_le(a, b), Nat.is_le(a, c)) == Nat.is_le(a, Nat.max(b, c)) : Bool}

def le_max_iff_sym(a, b, c):
  Equal.sym(Bool, Nat.is_le(a, Nat.max(b, c)), Bool.or(Nat.is_le(a, b), Nat.is_le(a, c)), le_max_iff(a, b, c))

# Adding a multiple of a positive divisor adds to the quotient: (x + z * (1 + b)) / (1 + b) = x / (1 + b) + z, reversed to rewrite toward the simple side.
law add_mul_div_right_sym:
  for x: Nat
  for z: Nat
  for b: Nat
  {Nat.add(Nat.div(x, 1n+b), z) == Nat.div(Nat.add(x, Nat.mul(z, 1n+b)), 1n+b) : Nat}

def add_mul_div_right_sym(x, z, b):
  Equal.sym(Nat, Nat.div(Nat.add(x, Nat.mul(z, 1n+b)), 1n+b), Nat.add(Nat.div(x, 1n+b), z), add_mul_div_right(x, z, b))

# Adding a multiple of a positive divisor adds to the quotient: (x + (1 + b) * z) / (1 + b) = x / (1 + b) + z, reversed to rewrite toward the simple side.
law add_mul_div_left_sym:
  for x: Nat
  for z: Nat
  for b: Nat
  {Nat.add(Nat.div(x, 1n+b), z) == Nat.div(Nat.add(x, Nat.mul(1n+b, z)), 1n+b) : Nat}

def add_mul_div_left_sym(x, z, b):
  Equal.sym(Nat, Nat.div(Nat.add(x, Nat.mul(1n+b, z)), 1n+b), Nat.add(Nat.div(x, 1n+b), z), add_mul_div_left(x, z, b))

# Adding a multiple of the divisor keeps the remainder: (a + c * b) % b = a % b, reversed to rewrite toward the simple side.
law add_mul_mod_self_right_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mod(a, b) == Nat.mod(Nat.add(a, Nat.mul(c, b)), b) : Nat}

def add_mul_mod_self_right_sym(a, b, c):
  Equal.sym(Nat, Nat.mod(Nat.add(a, Nat.mul(c, b)), b), Nat.mod(a, b), add_mul_mod_self_right(a, b, c))

# Adding a multiple of the divisor keeps the remainder: (a + b * c) % b = a % b, reversed to rewrite toward the simple side.
law add_mul_mod_self_left_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mod(a, b) == Nat.mod(Nat.add(a, Nat.mul(b, c)), b) : Nat}

def add_mul_mod_self_left_sym(a, b, c):
  Equal.sym(Nat, Nat.mod(Nat.add(a, Nat.mul(b, c)), b), Nat.mod(a, b), add_mul_mod_self_left(a, b, c))

# A remainder modulo two is zero or one, reversed to rewrite toward the simple side.
law mod_two_eq_zero_or_one_sym:
  for n: Nat
  {True{} == Bool.or(Nat.is_eq(Nat.mod(n, 2n), 0n), Nat.is_eq(Nat.mod(n, 2n), 1n)) : Bool}

def mod_two_eq_zero_or_one_sym(n):
  Equal.sym(Bool, Bool.or(Nat.is_eq(Nat.mod(n, 2n), 0n), Nat.is_eq(Nat.mod(n, 2n), 1n)), True{}, mod_two_eq_zero_or_one(n))

# The divisor times the quotient plus the remainder is the dividend: b * (a / b) + a % b = a, reversed to rewrite toward the simple side.
law div_add_mod_sym:
  for a: Nat
  for b: Nat
  {a == Nat.add(Nat.mul(b, Nat.div(a, b)), Nat.mod(a, b)) : Nat}

def div_add_mod_sym(a, b):
  Equal.sym(Nat, Nat.add(Nat.mul(b, Nat.div(a, b)), Nat.mod(a, b)), a, div_add_mod(a, b))

# Two times n is n + n, reversed to rewrite toward the simple side.
law two_mul_sym:
  for n: Nat
  {Nat.add(n, n) == Nat.mul(2n, n) : Nat}

def two_mul_sym(n):
  Equal.sym(Nat, Nat.mul(2n, n), Nat.add(n, n), two_mul(n))

# Doubling is multiplying by two: double n = 2 * n, reversed to rewrite toward the simple side.
law double_eq_two_mul_sym:
  for n: Nat
  {Nat.mul(2n, n) == Nat.double(n) : Nat}

def double_eq_two_mul_sym(n):
  Equal.sym(Nat, Nat.double(n), Nat.mul(2n, n), double_eq_two_mul(n))

# Doubling distributes over addition: double (a + b) = double a + double b, reversed to rewrite toward the simple side.
law double_add_sym:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.double(a), Nat.double(b)) == Nat.double(Nat.add(a, b)) : Nat}

def double_add_sym(a, b):
  Equal.sym(Nat, Nat.double(Nat.add(a, b)), Nat.add(Nat.double(a), Nat.double(b)), double_add(a, b))

# Doubling a product doubles its left factor: double (a * b) = double a * b, reversed to rewrite toward the simple side.
law double_mul_sym:
  for a: Nat
  for b: Nat
  {Nat.mul(Nat.double(a), b) == Nat.double(Nat.mul(a, b)) : Nat}

def double_mul_sym(a, b):
  Equal.sym(Nat, Nat.double(Nat.mul(a, b)), Nat.mul(Nat.double(a), b), double_mul(a, b))

# Multiplying by a doubled factor doubles the product: a * double b = double (a * b), reversed to rewrite toward the simple side.
law mul_double_sym:
  for a: Nat
  for b: Nat
  {Nat.double(Nat.mul(a, b)) == Nat.mul(a, Nat.double(b)) : Nat}

def mul_double_sym(a, b):
  Equal.sym(Nat, Nat.mul(a, Nat.double(b)), Nat.double(Nat.mul(a, b)), mul_double(a, b))

# Doubling distributes over truncated subtraction: double (a - b) = double a - double b, reversed to rewrite toward the simple side.
law double_sub_sym:
  for a: Nat
  for b: Nat
  {Nat.sub(Nat.double(a), Nat.double(b)) == Nat.double(Nat.sub(a, b)) : Nat}

def double_sub_sym(a, b):
  Equal.sym(Nat, Nat.double(Nat.sub(a, b)), Nat.sub(Nat.double(a), Nat.double(b)), double_sub(a, b))

# Twice the half plus the parity is the number: double (n / 2) + n % 2 = n, reversed to rewrite toward the simple side.
law double_div_two_add_mod_two_sym:
  for n: Nat
  {n == Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)) : Nat}

def double_div_two_add_mod_two_sym(n):
  Equal.sym(Nat, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), n, double_div_two_add_mod_two(n))

# Adding the same amount on the right does not change the order test: a <= b tests as a + k <= b + k, reversed to rewrite toward the simple side.
law add_le_add_iff_right_sym:
  for a: Nat
  for b: Nat
  for k: Nat
  {Nat.is_le(Nat.add(a, k), Nat.add(b, k)) == Nat.is_le(a, b) : Bool}

def add_le_add_iff_right_sym(a, b, k):
  Equal.sym(Bool, Nat.is_le(a, b), Nat.is_le(Nat.add(a, k), Nat.add(b, k)), add_le_add_iff_right(a, b, k))

# Adding the same amount on the left does not change the equality test: a = b tests as k + a = k + b, reversed to rewrite toward the simple side.
law add_left_cancel_iff_sym:
  for k: Nat
  for -a: Nat
  for -b: Nat
  {Nat.is_eq(Nat.add(k, a), Nat.add(k, b)) == Nat.is_eq(a, b) : Bool}

def add_left_cancel_iff_sym(k, a, b):
  Equal.sym(Bool, Nat.is_eq(a, b), Nat.is_eq(Nat.add(k, a), Nat.add(k, b)), add_left_cancel_iff(k, a, b))

# Adding the same amount on the right does not change the equality test: a = b tests as a + k = b + k, reversed to rewrite toward the simple side.
law add_right_cancel_iff_sym:
  for a: Nat
  for b: Nat
  for k: Nat
  {Nat.is_eq(Nat.add(a, k), Nat.add(b, k)) == Nat.is_eq(a, b) : Bool}

def add_right_cancel_iff_sym(a, b, k):
  Equal.sym(Bool, Nat.is_eq(a, b), Nat.is_eq(Nat.add(a, k), Nat.add(b, k)), add_right_cancel_iff(a, b, k))

# Multiplying n by two gives n + n, reversed to rewrite toward the simple side.
law mul_two_sym:
  for n: Nat
  {Nat.add(n, n) == Nat.mul(n, 2n) : Nat}

def mul_two_sym(n):
  Equal.sym(Nat, Nat.mul(n, 2n), Nat.add(n, n), mul_two(n))

# Squaring n gives n times n, reversed to rewrite toward the simple side.
law pow_two_sym:
  for n: Nat
  {Nat.mul(n, n) == Nat.pow(n, 2n) : Nat}

def pow_two_sym(n):
  Equal.sym(Nat, Nat.pow(n, 2n), Nat.mul(n, n), pow_two(n))

# The minimum of two numbers is at most their maximum, reversed to rewrite toward the simple side.
law min_le_max_sym:
  for a: Nat
  for b: Nat
  {True{} == Nat.is_le(Nat.min(a, b), Nat.max(a, b)) : Bool}

def min_le_max_sym(a, b):
  Equal.sym(Bool, Nat.is_le(Nat.min(a, b), Nat.max(a, b)), True{}, min_le_max(a, b))
