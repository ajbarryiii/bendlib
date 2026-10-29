# bend-mathlib/u32.bend: machine words as naturals; Word(n) and U32 operations agree with Nat arithmetic
# (compare, add, sub, inc, not, min, max, from_nat, div).
import Base
import ./nat.bend as MNat

def internal_succ_double_lt(a: Nat, b: Nat, h: MNat.lt(a, b)) -> MNat.lt(1n+Nat.double(a), Nat.double(b)):
  match a b:
    case 0n 0n:
      Empty.absurd(MNat.lt(1n, 0n), MNat.internal_false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd(MNat.lt(3n+Nat.double(p), 0n), MNat.internal_false_ne_true(h))
    case 1n+p 1n+q:
      internal_succ_double_lt(p, q, h)

# A word's value is below two to the width: to_nat w < 2^n.
law word_to_nat_lt:
  for n: Nat
  for w: Word(n)
  MNat.lt(Word.to_nat(n, w), Nat.pow(2n, n))

def word_to_nat_lt(n, w):
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{False{}, t}:
          +t = t
          %MNat.two_pow_succ_sym(p) : MNat.lt(Nat.double(Word.to_nat(p, t)), _)
          MNat.double_lt_double(Word.to_nat(p, t), Nat.pow(2n, p), word_to_nat_lt(p, t))
        case WCon{True{}, t}:
          +t = t
          %MNat.two_pow_succ_sym(p) : MNat.lt(1n+Nat.double(Word.to_nat(p, t)), _)
          internal_succ_double_lt(Word.to_nat(p, t), Nat.pow(2n, p), word_to_nat_lt(p, t))

# The zero word is the natural zero: to_nat (zero n) = 0.
law word_to_nat_zero:
  for n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}

def word_to_nat_zero(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => Nat.double(x), Word.to_nat(p, Word.zero(p)), 0n, word_to_nat_zero(p))

# Distinct words have distinct values: to_nat a = to_nat b implies a = b.
law word_to_nat_inj:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

def word_to_nat_inj(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, at, bt, word_to_nat_inj(p, at, bt, MNat.double_inj(Word.to_nat(p, at), Word.to_nat(p, bt), e)))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, at, bt, word_to_nat_inj(p, at, bt, MNat.double_inj(Word.to_nat(p, at), Word.to_nat(p, bt), MNat.succ_inj(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), e))))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)}, MNat.double_ne_succ_double(Word.to_nat(p, at), Word.to_nat(p, bt))(e))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)}, MNat.double_ne_succ_double(Word.to_nat(p, bt), Word.to_nat(p, at))(Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), e)))

def internal_bv(b: Bool) -> Nat:
  Bool.pick(Nat, b, 1n, 0n)

def internal_to_nat_con(-p: Nat, b: Bool, -t: Word(p)) -> {Nat.add(internal_bv(b), Nat.double(Word.to_nat(p, t))) == Word.to_nat(1n+p, WCon{b, t}) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_cmp_bits(x: Nat, y: Nat, ab: Bool, bb: Bool) -> {Word.cmp.fin(ab, bb, Nat.cmp(x, y)) == Nat.cmp(Nat.add(internal_bv(ab), Nat.double(x)), Nat.add(internal_bv(bb), Nat.double(y))) : Cmp}:
  match x y:
    case 0n 0n:
      match ab bb:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match ab bb:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match ab bb:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 1n+q:
      match ab bb:
        case False{} False{}:
          internal_cmp_bits(p, q, False{}, False{})
        case False{} True{}:
          internal_cmp_bits(p, q, False{}, True{})
        case True{} False{}:
          internal_cmp_bits(p, q, True{}, False{})
        case True{} True{}:
          internal_cmp_bits(p, q, True{}, True{})

# Comparing words compares their values: cmp a b = cmp (to_nat a) (to_nat b).
law word_cmp_to_nat:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

def word_cmp_to_nat(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %internal_to_nat_con(p, ab, at) : {Word.cmp.fin(ab, bb, Word.cmp(p, at, bt)) == Nat.cmp(_, Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
          %internal_to_nat_con(p, bb, bt) : {Word.cmp.fin(ab, bb, Word.cmp(p, at, bt)) == Nat.cmp(Nat.add(internal_bv(ab), Nat.double(Word.to_nat(p, at))), _) : Cmp}
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), word_cmp_to_nat(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == Nat.cmp(Nat.add(internal_bv(ab), Nat.double(Word.to_nat(p, at))), Nat.add(internal_bv(bb), Nat.double(Word.to_nat(p, bt)))) : Cmp}
          internal_cmp_bits(Word.to_nat(p, at), Word.to_nat(p, bt), ab, bb)

# One plus a word plus its complement is two to the width: 1 + to_nat (not w) + to_nat w = 2^n.
law word_not_add:
  for n: Nat
  for w: Word(n)
  {1n+Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)) == Nat.pow(2n, n) : Nat}

def word_not_add(n, w):
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          -u = Word.to_nat(p, Word.not(p, t))
          -x = Word.to_nat(p, t)
          %MNat.two_pow_succ_sym(p) : {2n+Nat.add(Nat.double(u), Nat.double(x)) == _ : Nat}
          %word_not_add(p, t) : {2n+Nat.add(Nat.double(u), Nat.double(x)) == Nat.double(_) : Nat}
          %MNat.double_add(Word.to_nat(p, Word.not(p, t)), Word.to_nat(p, t)) : {2n+_ == 2n+Nat.double(Nat.add(u, x)) : Nat}
          {==}
        case WCon{True{}, +t}:
          -u = Word.to_nat(p, Word.not(p, t))
          -x = Word.to_nat(p, t)
          %MNat.add_succ_sym(Nat.double(Word.to_nat(p, Word.not(p, t))), Nat.double(Word.to_nat(p, t))) : {1n+_ == Nat.pow(2n, 1n+p) : Nat}
          %MNat.two_pow_succ_sym(p) : {2n+Nat.add(Nat.double(u), Nat.double(x)) == _ : Nat}
          %word_not_add(p, t) : {2n+Nat.add(Nat.double(u), Nat.double(x)) == Nat.double(_) : Nat}
          %MNat.double_add(Word.to_nat(p, Word.not(p, t)), Word.to_nat(p, t)) : {2n+_ == 2n+Nat.double(Nat.add(u, x)) : Nat}
          {==}

def internal_pick_pow(o: Bool, p: Nat) -> {Nat.double(Bool.pick(Nat, o, Nat.pow(2n, p), 0n)) == Bool.pick(Nat, o, Nat.pow(2n, 1n+p), 0n) : Nat}:
  match o:
    case False{}:
      {==}
    case True{}:
      MNat.two_pow_succ_sym(p)

def internal_carry(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{+bb, bt}:
          internal_carry(p, at, bt, Bool.and(bb, c))
        case WCon{True{}, at} WCon{+bb, bt}:
          internal_carry(p, at, bt, Bool.or(bb, c))

def internal_full_add(a: Bool, b: Bool, c: Bool) -> {Nat.add(Nat.add(internal_bv(a), internal_bv(b)), internal_bv(c)) == Nat.add(internal_bv(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))), Nat.double(internal_bv(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))) : Nat}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def internal_adc_nat(+s: Nat, +k: Nat, +a: Nat, +b: Nat, +c: Nat, +e: Nat, +q: Nat, +x: Nat, +y: Nat,
  ih: {Nat.add(e, q) == Nat.add(Nat.add(x, y), k) : Nat},
  fa: {Nat.add(Nat.add(a, b), c) == Nat.add(s, Nat.double(k)) : Nat})
  -> {Nat.add(Nat.add(s, Nat.double(e)), Nat.double(q)) == Nat.add(Nat.add(Nat.add(a, Nat.double(x)), Nat.add(b, Nat.double(y))), c) : Nat}:
  -d = Nat.double(Nat.add(x, y))
  -r = Nat.add(Nat.add(Nat.add(a, Nat.double(x)), Nat.add(b, Nat.double(y))), c)
  %MNat.add_assoc_sym(s, Nat.double(e), Nat.double(q)) : {_ == r : Nat}
  %MNat.double_add(e, q) : {Nat.add(s, _) == r : Nat}
  %Equal.sym(Nat, Nat.add(e, q), Nat.add(Nat.add(x, y), k), ih) : {Nat.add(s, Nat.double(_)) == r : Nat}
  %MNat.double_add_sym(Nat.add(x, y), k) : {Nat.add(s, _) == r : Nat}
  -l = Nat.add(s, Nat.add(d, Nat.double(k)))
  %MNat.add_add_add_comm(a, b, Nat.double(x), Nat.double(y)) : {l == Nat.add(_, c) : Nat}
  %MNat.double_add(x, y) : {l == Nat.add(Nat.add(Nat.add(a, b), _), c) : Nat}
  %MNat.add_right_comm_sym(Nat.add(a, b), Nat.double(Nat.add(x, y)), c) : {l == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(s, Nat.double(k)), fa) : {l == Nat.add(_, d) : Nat}
  %MNat.add_assoc_sym(s, Nat.double(k), Nat.double(Nat.add(x, y))) : {l == _ : Nat}
  %MNat.add_comm(Nat.double(Nat.add(x, y)), Nat.double(k)) : {l == Nat.add(s, _) : Nat}
  {==}

def internal_adc_core(n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Bool.pick(Nat, internal_carry(n, a, b, c), Nat.pow(2n, n), 0n)) == Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), internal_bv(c)) : Nat}:
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{+bb, +bt}:
          +c = c
          -e = Word.adc(p, at, bt, False{}, Bool.and(bb, c))
          -o = internal_carry(p, at, bt, Bool.and(bb, c))
          -r = Nat.add(Nat.add(Word.to_nat(1n+p, WCon{False{}, at}), Word.to_nat(1n+p, WCon{bb, bt})), internal_bv(c))
          %internal_to_nat_con(p, Bool.xor(bb, c), Word.adc(p, at, bt, False{}, Bool.and(bb, c))) : {Nat.add(_, Bool.pick(Nat, o, Nat.pow(2n, 1n+p), 0n)) == r : Nat}
          %internal_pick_pow(internal_carry(p, at, bt, Bool.and(bb, c)), p) : {Nat.add(Nat.add(internal_bv(Bool.xor(bb, c)), Nat.double(Word.to_nat(p, e))), _) == r : Nat}
          -l = Nat.add(Nat.add(internal_bv(Bool.xor(bb, c)), Nat.double(Word.to_nat(p, e))), Nat.double(Bool.pick(Nat, o, Nat.pow(2n, p), 0n)))
          %internal_to_nat_con(p, False{}, at) : {l == Nat.add(Nat.add(_, Word.to_nat(1n+p, WCon{bb, bt})), internal_bv(c)) : Nat}
          %internal_to_nat_con(p, bb, bt) : {l == Nat.add(Nat.add(Nat.add(internal_bv(False{}), Nat.double(Word.to_nat(p, at))), _), internal_bv(c)) : Nat}
          internal_adc_nat(internal_bv(Bool.xor(bb, c)), internal_bv(Bool.and(bb, c)), internal_bv(False{}), internal_bv(bb), internal_bv(c), Word.to_nat(p, Word.adc(p, at, bt, False{}, Bool.and(bb, c))), Bool.pick(Nat, internal_carry(p, at, bt, Bool.and(bb, c)), Nat.pow(2n, p), 0n), Word.to_nat(p, at), Word.to_nat(p, bt), internal_adc_core(p, at, bt, Bool.and(bb, c)), internal_full_add(False{}, bb, c))
        case WCon{True{}, +at} WCon{+bb, +bt}:
          +c = c
          -e = Word.adc(p, at, bt, False{}, Bool.or(bb, c))
          -o = internal_carry(p, at, bt, Bool.or(bb, c))
          -r = Nat.add(Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{bb, bt})), internal_bv(c))
          %internal_to_nat_con(p, Bool.not(Bool.xor(bb, c)), Word.adc(p, at, bt, False{}, Bool.or(bb, c))) : {Nat.add(_, Bool.pick(Nat, o, Nat.pow(2n, 1n+p), 0n)) == r : Nat}
          %internal_pick_pow(internal_carry(p, at, bt, Bool.or(bb, c)), p) : {Nat.add(Nat.add(internal_bv(Bool.not(Bool.xor(bb, c))), Nat.double(Word.to_nat(p, e))), _) == r : Nat}
          -l = Nat.add(Nat.add(internal_bv(Bool.not(Bool.xor(bb, c))), Nat.double(Word.to_nat(p, e))), Nat.double(Bool.pick(Nat, o, Nat.pow(2n, p), 0n)))
          %internal_to_nat_con(p, True{}, at) : {l == Nat.add(Nat.add(_, Word.to_nat(1n+p, WCon{bb, bt})), internal_bv(c)) : Nat}
          %internal_to_nat_con(p, bb, bt) : {l == Nat.add(Nat.add(Nat.add(internal_bv(True{}), Nat.double(Word.to_nat(p, at))), _), internal_bv(c)) : Nat}
          internal_adc_nat(internal_bv(Bool.not(Bool.xor(bb, c))), internal_bv(Bool.or(bb, c)), internal_bv(True{}), internal_bv(bb), internal_bv(c), Word.to_nat(p, Word.adc(p, at, bt, False{}, Bool.or(bb, c))), Bool.pick(Nat, internal_carry(p, at, bt, Bool.or(bb, c)), Nat.pow(2n, p), 0n), Word.to_nat(p, at), Word.to_nat(p, bt), internal_adc_core(p, at, bt, Bool.or(bb, c)), internal_full_add(True{}, bb, c))

def internal_lt_congl(-x: Nat, -y: Nat, -m: Nat, e: {x == y : Nat}, h: MNat.lt(x, m)) -> MNat.lt(y, m):
  %e : MNat.lt(_, m)
  h

def internal_le_congr(-m: Nat, -x: Nat, -y: Nat, e: {y == x : Nat}, h: MNat.le(m, y)) -> MNat.le(m, x):
  %e : MNat.le(m, _)
  h

def internal_fin_exact(+e: Nat, +s: Nat, +m: Nat, o: Bool, eq: {Nat.add(e, Bool.pick(Nat, o, m, 0n)) == s : Nat}, h: MNat.lt(s, m)) -> {e == s : Nat}:
  match o:
    case False{}:
      Equal.trans(Nat, e, Nat.add(e, 0n), s, MNat.add_zero_sym(e), eq)
    case True{}:
      +le = MNat.le_of_add_eq(m, e, s, Equal.trans(Nat, Nat.add(m, e), Nat.add(e, m), s, MNat.add_comm(m, e), eq))
      Empty.absurd({e == s : Nat}, MNat.lt_irrefl(s)(MNat.lt_of_lt_of_le(s, m, s, h, le)))

def internal_fin_wrap(+e: Nat, -s: Nat, +m: Nat, o: Bool, eq: {Nat.add(e, Bool.pick(Nat, o, m, 0n)) == s : Nat}, h: MNat.lt(e, m)) -> {e == Nat.mod(s, m) : Nat}:
  match o:
    case False{}:
      %eq : {e == Nat.mod(_, m) : Nat}
      %MNat.add_zero_sym(e) : {e == Nat.mod(_, m) : Nat}
      Equal.sym(Nat, Nat.mod(e, m), e, MNat.mod_eq_of_lt(e, m, h))
    case True{}:
      %eq : {e == Nat.mod(_, m) : Nat}
      %MNat.add_comm(m, e) : {e == Nat.mod(_, m) : Nat}
      %MNat.add_mod_left_sym(e, m) : {e == _ : Nat}
      Equal.sym(Nat, Nat.mod(e, m), e, MNat.mod_eq_of_lt(e, m, h))

def internal_fin_over(+e: Nat, +s: Nat, +m: Nat, o: Bool, eq: {Nat.add(e, Bool.pick(Nat, o, m, 0n)) == s : Nat}, h: MNat.lt(e, m), le: MNat.le(m, s)) -> {Nat.add(e, m) == s : Nat}:
  match o:
    case False{}:
      +es = Equal.trans(Nat, e, Nat.add(e, 0n), s, MNat.add_zero_sym(e), eq)
      Empty.absurd({Nat.add(e, m) == s : Nat}, MNat.lt_irrefl(m)(MNat.lt_of_le_of_lt(m, s, m, le, internal_lt_congl(e, s, m, es, h))))
    case True{}:
      eq

# The adder is exact below the overflow: a + b + carry-in < 2^n implies to_nat (adc a b False c) = a + b + carry-in.
law word_adc_exact:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  for h: MNat.lt(Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n))
  {Word.to_nat(n, Word.adc(n, a, b, False{}, c)) == Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)) : Nat}

def word_adc_exact(n, a, b, c, h):
  +n = n
  +a = a
  +b = b
  +c = c
  internal_fin_exact(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n), internal_carry(n, a, b, c), internal_adc_core(n, a, b, c), h)

# The adder drops exactly one 2^n on overflow: 2^n <= a + b + carry-in implies to_nat (adc a b False c) + 2^n = a + b + carry-in.
law word_adc_overflow:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  for h: MNat.le(Nat.pow(2n, n), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)))
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.pow(2n, n)) == Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)) : Nat}

def word_adc_overflow(n, a, b, c, h):
  +n = n
  +a = a
  +b = b
  +c = c
  internal_fin_over(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n), internal_carry(n, a, b, c), internal_adc_core(n, a, b, c), word_to_nat_lt(n, Word.adc(n, a, b, False{}, c)), h)

# The adder wraps modulo 2^n: to_nat (adc a b False c) = (a + b + carry-in) % 2^n.
law word_adc_wrap:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {Word.to_nat(n, Word.adc(n, a, b, False{}, c)) == Nat.mod(Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n)) : Nat}

def word_adc_wrap(n, a, b, c):
  +n = n
  +a = a
  +b = b
  +c = c
  internal_fin_wrap(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n), internal_carry(n, a, b, c), internal_adc_core(n, a, b, c), word_to_nat_lt(n, Word.adc(n, a, b, False{}, c)))

# Word addition is exact without overflow: a + b < 2^n implies to_nat (add a b) = a + b.
law word_add_exact:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: MNat.lt(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n))
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def word_add_exact(n, a, b, h):
  +n = n
  +a = a
  +b = b
  %MNat.add_zero(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : {Word.to_nat(n, Word.add(n, a, b)) == _ : Nat}
  word_adc_exact(n, a, b, False{}, internal_lt_congl(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), 0n), Nat.pow(2n, n), MNat.add_zero_sym(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), h))

# Word addition wraps modulo 2^n: to_nat (add a b) = (a + b) % 2^n.
law word_add_wrap:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.mod(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)) : Nat}

def word_add_wrap(n, a, b):
  +n = n
  +a = a
  +b = b
  %MNat.add_zero(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : {Word.to_nat(n, Word.add(n, a, b)) == Nat.mod(_, Nat.pow(2n, n)) : Nat}
  word_adc_wrap(n, a, b, False{})

def internal_inc_carry(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          False{}
        case WCon{True{}, t}:
          internal_inc_carry(p, t)

def internal_inc_core(n: Nat, w: Word(n)) -> {Nat.add(Word.to_nat(n, Word.inc(n, w)), Bool.pick(Nat, internal_inc_carry(n, w), Nat.pow(2n, n), 0n)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{False{}, t}:
          MNat.add_zero(1n+Nat.double(Word.to_nat(p, t)))
        case WCon{True{}, +t}:
          -x = Word.to_nat(p, t)
          %internal_pick_pow(internal_inc_carry(p, t), p) : {Nat.add(Nat.double(Word.to_nat(p, Word.inc(p, t))), _) == 2n+Nat.double(x) : Nat}
          %MNat.double_add(Word.to_nat(p, Word.inc(p, t)), Bool.pick(Nat, internal_inc_carry(p, t), Nat.pow(2n, p), 0n)) : {_ == 2n+Nat.double(x) : Nat}
          Equal.cong(Nat, Nat, z => Nat.double(z), Nat.add(Word.to_nat(p, Word.inc(p, t)), Bool.pick(Nat, internal_inc_carry(p, t), Nat.pow(2n, p), 0n)), 1n+Word.to_nat(p, t), internal_inc_core(p, t))

# Increment is exact without overflow: 1 + w < 2^n implies to_nat (inc w) = 1 + w.
law word_inc_exact:
  for n: Nat
  for w: Word(n)
  for h: MNat.lt(1n+Word.to_nat(n, w), Nat.pow(2n, n))
  {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}

def word_inc_exact(n, w, h):
  +n = n
  +w = w
  internal_fin_exact(Word.to_nat(n, Word.inc(n, w)), 1n+Word.to_nat(n, w), Nat.pow(2n, n), internal_inc_carry(n, w), internal_inc_core(n, w), h)

# Increment wraps modulo 2^n: to_nat (inc w) = (1 + w) % 2^n.
law word_inc_wrap:
  for n: Nat
  for w: Word(n)
  {Word.to_nat(n, Word.inc(n, w)) == Nat.mod(1n+Word.to_nat(n, w), Nat.pow(2n, n)) : Nat}

def word_inc_wrap(n, w):
  +n = n
  +w = w
  internal_fin_wrap(Word.to_nat(n, Word.inc(n, w)), 1n+Word.to_nat(n, w), Nat.pow(2n, n), internal_inc_carry(n, w), internal_inc_core(n, w), word_to_nat_lt(n, Word.inc(n, w)))

def internal_adc_not(n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Word.adc(n, a, b, True{}, c) == Word.adc(n, a, Word.not(n, b), False{}, c) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{+bb, +bt}:
          +c = c
          Equal.cong(Word(p), Word(1n+p), w => WCon{Bool.xor(Bool.not(bb), c), w}, Word.adc(p, at, bt, True{}, Bool.and(Bool.not(bb), c)), Word.adc(p, at, Word.not(p, bt), False{}, Bool.and(Bool.not(bb), c)), internal_adc_not(p, at, bt, Bool.and(Bool.not(bb), c)))
        case WCon{True{}, +at} WCon{+bb, +bt}:
          +c = c
          Equal.cong(Word(p), Word(1n+p), w => WCon{Bool.not(Bool.xor(Bool.not(bb), c)), w}, Word.adc(p, at, bt, True{}, Bool.or(Bool.not(bb), c)), Word.adc(p, at, Word.not(p, bt), False{}, Bool.or(Bool.not(bb), c)), internal_adc_not(p, at, bt, Bool.or(Bool.not(bb), c)))

def internal_sub_arith(+x: Nat, +y: Nat, +u: Nat, -m: Nat, h: MNat.le(y, x), c: {1n+Nat.add(u, y) == m : Nat}) -> {Nat.add(Nat.add(x, u), 1n) == Nat.add(Nat.sub(x, y), m) : Nat}:
  -d = Nat.sub(x, y)
  %c : {Nat.add(Nat.add(x, u), 1n) == Nat.add(d, _) : Nat}
  %MNat.add_sub_of_le(y, x, h) : {Nat.add(Nat.add(_, u), 1n) == Nat.add(d, 1n+Nat.add(u, y)) : Nat}
  -l = Nat.add(Nat.add(Nat.add(y, d), u), 1n)
  %MNat.add_succ_sym(Nat.sub(x, y), Nat.add(u, y)) : {l == _ : Nat}
  %MNat.add_comm(1n, Nat.add(Nat.add(y, Nat.sub(x, y)), u)) : {_ == 1n+Nat.add(d, Nat.add(u, y)) : Nat}
  -l2 = Nat.add(1n, Nat.add(Nat.add(y, d), u))
  %MNat.add_comm(y, u) : {l2 == 1n+Nat.add(d, _) : Nat}
  %MNat.add_left_comm(y, Nat.sub(x, y), u) : {l2 == 1n+_ : Nat}
  %MNat.add_assoc(y, Nat.sub(x, y), u) : {l2 == 1n+_ : Nat}
  {==}

# Word subtraction is exact without underflow: b <= a implies to_nat (sub a b) = a - b.
law word_sub_exact:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: MNat.le(Word.to_nat(n, b), Word.to_nat(n, a))
  {Word.to_nat(n, Word.sub(n, a, b)) == Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def word_sub_exact(n, a, b, h):
  +n = n
  +a = a
  +b = b
  -x = Word.to_nat(n, a)
  -y = Word.to_nat(n, b)
  -nb = Word.not(n, b)
  -e = Word.to_nat(n, Word.adc(n, a, nb, False{}, True{}))
  -s = Nat.add(Nat.add(x, Word.to_nat(n, nb)), 1n)
  -m = Nat.pow(2n, n)
  %Equal.sym(Word(n), Word.adc(n, a, b, True{}, True{}), Word.adc(n, a, Word.not(n, b), False{}, True{}), internal_adc_not(n, a, b, True{})) : {Word.to_nat(n, _) == Nat.sub(x, y) : Nat}
  +ar = internal_sub_arith(Word.to_nat(n, a), Word.to_nat(n, b), Word.to_nat(n, Word.not(n, b)), Nat.pow(2n, n), h, word_not_add(n, b))
  +le = internal_le_congr(Nat.pow(2n, n), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, Word.not(n, b))), 1n), Nat.add(Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)), Equal.sym(Nat, s, Nat.add(Nat.sub(x, y), m), ar), MNat.le_add_left(Nat.pow(2n, n), Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b))))
  +ov = internal_fin_over(Word.to_nat(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, Word.not(n, b))), 1n), Nat.pow(2n, n), internal_carry(n, a, Word.not(n, b), True{}), internal_adc_core(n, a, Word.not(n, b), True{}), word_to_nat_lt(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), le)
  MNat.add_right_cancel(Word.to_nat(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), Nat.pow(2n, n), Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b)), Equal.trans(Nat, Nat.add(e, m), s, Nat.add(Nat.sub(x, y), m), ov, ar))

def internal_sub_wrap_arith(+x: Nat, +y: Nat, +u: Nat, -m: Nat, c: {1n+Nat.add(u, y) == m : Nat}) -> {Nat.add(Nat.add(x, u), 1n) == Nat.add(x, Nat.sub(m, y)) : Nat}:
  %c : {Nat.add(Nat.add(x, u), 1n) == Nat.add(x, Nat.sub(_, y)) : Nat}
  %MNat.add_sub_cancel_sym(1n+u, y) : {Nat.add(Nat.add(x, u), 1n) == Nat.add(x, _) : Nat}
  %MNat.add_succ_sym(x, u) : {Nat.add(Nat.add(x, u), 1n) == _ : Nat}
  MNat.add_comm(Nat.add(x, u), 1n)

# Word subtraction wraps modulo 2^n: to_nat (sub a b) = (a + (2^n - b)) % 2^n.
law word_sub_wrap:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.to_nat(n, Word.sub(n, a, b)) == Nat.mod(Nat.add(Word.to_nat(n, a), Nat.sub(Nat.pow(2n, n), Word.to_nat(n, b))), Nat.pow(2n, n)) : Nat}

def word_sub_wrap(n, a, b):
  +n = n
  +a = a
  +b = b
  -x = Word.to_nat(n, a)
  -y = Word.to_nat(n, b)
  -u = Word.to_nat(n, Word.not(n, b))
  -m = Nat.pow(2n, n)
  %Equal.sym(Word(n), Word.adc(n, a, b, True{}, True{}), Word.adc(n, a, Word.not(n, b), False{}, True{}), internal_adc_not(n, a, b, True{})) : {Word.to_nat(n, _) == Nat.mod(Nat.add(x, Nat.sub(m, y)), m) : Nat}
  %internal_sub_wrap_arith(Word.to_nat(n, a), Word.to_nat(n, b), Word.to_nat(n, Word.not(n, b)), Nat.pow(2n, n), word_not_add(n, b)) : {Word.to_nat(n, Word.adc(n, a, Word.not(n, b), False{}, True{})) == Nat.mod(_, m) : Nat}
  word_adc_wrap(n, a, Word.not(n, b), True{})

def internal_bound(-s: Nat, -m: Nat, e: {Nat.pow(2n, 32n) == m : Nat}, h: MNat.lt(s, m)) -> MNat.lt(s, Nat.pow(2n, 32n)):
  %Equal.sym(Nat, Nat.pow(2n, 32n), m, e) : MNat.lt(s, _)
  h

def internal_u32_to_nat_lt(-m: Nat, a: U32, e: {Nat.pow(2n, 32n) == m : Nat}) -> MNat.lt(U32.to_nat(a), m):
  match a:
    case U32{w}:
      %e : MNat.lt(Word.to_nat(32n, w), _)
      word_to_nat_lt(32n, w)

# A U32's value is below 2^32.
law u32_to_nat_lt:
  for a: U32
  MNat.lt(U32.to_nat(a), Nat.pow(2n, 32n))

def u32_to_nat_lt(a):
  internal_u32_to_nat_lt(Nat.pow(2n, 32n), a, {==})

# Distinct U32s have distinct values: to_nat a = to_nat b implies a = b.
law u32_to_nat_inj:
  for a: U32
  for b: U32
  for e: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

def u32_to_nat_inj(a, b, e):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word_to_nat_inj(32n, x, y, e))

# Comparing U32s compares their values: cmp a b = cmp (to_nat a) (to_nat b).
law u32_cmp_to_nat:
  for a: U32
  for b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

def u32_cmp_to_nat(a, b):
  match a b:
    case U32{x} U32{y}:
      word_cmp_to_nat(32n, x, y)

# U32 equality tests the values: is_eq a b = is_eq (to_nat a) (to_nat b).
law u32_is_eq_to_nat:
  for a: U32
  for b: U32
  {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32_is_eq_to_nat(a, b):
  +a = a
  +b = b
  Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

# U32 disequality tests the values: is_ne a b = is_ne (to_nat a) (to_nat b).
law u32_is_ne_to_nat:
  for a: U32
  for b: U32
  {U32.is_ne(a, b) == Nat.is_ne(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32_is_ne_to_nat(a, b):
  +a = a
  +b = b
  Equal.cong(Cmp, Bool, k => Bool.not(Cmp.is_eq(k)), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

# The U32 strict order is the order of the values: is_lt a b = is_lt (to_nat a) (to_nat b).
law u32_is_lt_to_nat:
  for a: U32
  for b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32_is_lt_to_nat(a, b):
  +a = a
  +b = b
  Equal.cong(Cmp, Bool, k => Cmp.is_lt(k), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

# The U32 order is the order of the values: is_le a b = is_le (to_nat a) (to_nat b).
law u32_is_le_to_nat:
  for a: U32
  for b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32_is_le_to_nat(a, b):
  +a = a
  +b = b
  Equal.cong(Cmp, Bool, k => Cmp.is_le(k), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

# The reverse U32 strict order is that of the values: is_gt a b = is_gt (to_nat a) (to_nat b).
law u32_is_gt_to_nat:
  for a: U32
  for b: U32
  {U32.is_gt(a, b) == Nat.is_gt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32_is_gt_to_nat(a, b):
  +a = a
  +b = b
  Equal.cong(Cmp, Bool, k => Cmp.is_gt(k), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

# The reverse U32 order is that of the values: is_ge a b = is_ge (to_nat a) (to_nat b).
law u32_is_ge_to_nat:
  for a: U32
  for b: U32
  {U32.is_ge(a, b) == Nat.is_ge(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32_is_ge_to_nat(a, b):
  +a = a
  +b = b
  Equal.cong(Cmp, Bool, k => Cmp.is_ge(k), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

def internal_u32_add_exact(-m: Nat, a: U32, b: U32, e: {Nat.pow(2n, 32n) == m : Nat}, h: MNat.lt(Nat.add(U32.to_nat(a), U32.to_nat(b)), m)) -> {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      word_add_exact(32n, x, y, internal_bound(Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)), m, e, h))

# U32 addition is exact without overflow: a + b < 2^32 implies to_nat (a + b) = a + b.
law u32_add_exact:
  for a: U32
  for b: U32
  for h: MNat.lt(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n))
  {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u32_add_exact(a, b, h):
  internal_u32_add_exact(Nat.pow(2n, 32n), a, b, {==}, h)

def internal_u32_add_wrap(-m: Nat, a: U32, b: U32, e: {Nat.pow(2n, 32n) == m : Nat}) -> {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), m) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      %e : {Word.to_nat(32n, Word.add(32n, x, y)) == Nat.mod(Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)), _) : Nat}
      word_add_wrap(32n, x, y)

# U32 addition wraps modulo 2^32: to_nat (a + b) = (a + b) % 2^32.
law u32_add_wrap:
  for a: U32
  for b: U32
  {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)) : Nat}

def u32_add_wrap(a, b):
  internal_u32_add_wrap(Nat.pow(2n, 32n), a, b, {==})

# U32 subtraction is exact without underflow: b <= a implies to_nat (a - b) = a - b.
law u32_sub_exact:
  for a: U32
  for b: U32
  for h: MNat.le(U32.to_nat(b), U32.to_nat(a))
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u32_sub_exact(a, b, h):
  match a b:
    case U32{x} U32{y}:
      word_sub_exact(32n, x, y, h)

def internal_u32_sub_wrap(-m: Nat, a: U32, b: U32, e: {Nat.pow(2n, 32n) == m : Nat}) -> {U32.to_nat(U32.sub(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.sub(m, U32.to_nat(b))), m) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      %e : {Word.to_nat(32n, Word.sub(32n, x, y)) == Nat.mod(Nat.add(Word.to_nat(32n, x), Nat.sub(_, Word.to_nat(32n, y))), _) : Nat}
      word_sub_wrap(32n, x, y)

# U32 subtraction wraps modulo 2^32: to_nat (a - b) = (a + (2^32 - b)) % 2^32.
law u32_sub_wrap:
  for a: U32
  for b: U32
  {U32.to_nat(U32.sub(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.sub(Nat.pow(2n, 32n), U32.to_nat(b))), Nat.pow(2n, 32n)) : Nat}

def u32_sub_wrap(a, b):
  internal_u32_sub_wrap(Nat.pow(2n, 32n), a, b, {==})

def internal_u32_inc_exact(-m: Nat, a: U32, e: {Nat.pow(2n, 32n) == m : Nat}, h: MNat.lt(1n+U32.to_nat(a), m)) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a:
    case U32{+w}:
      word_inc_exact(32n, w, internal_bound(1n+Word.to_nat(32n, w), m, e, h))

# U32 increment is exact without overflow: 1 + a < 2^32 implies to_nat (inc a) = 1 + a.
law u32_inc_exact:
  for a: U32
  for h: MNat.lt(1n+U32.to_nat(a), Nat.pow(2n, 32n))
  {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}

def u32_inc_exact(a, h):
  internal_u32_inc_exact(Nat.pow(2n, 32n), a, {==}, h)

def internal_u32_inc_wrap(-m: Nat, a: U32, e: {Nat.pow(2n, 32n) == m : Nat}) -> {U32.to_nat(U32.inc(a)) == Nat.mod(1n+U32.to_nat(a), m) : Nat}:
  match a:
    case U32{+w}:
      %e : {Word.to_nat(32n, Word.inc(32n, w)) == Nat.mod(1n+Word.to_nat(32n, w), _) : Nat}
      word_inc_wrap(32n, w)

# U32 increment wraps modulo 2^32: to_nat (inc a) = (1 + a) % 2^32.
law u32_inc_wrap:
  for a: U32
  {U32.to_nat(U32.inc(a)) == Nat.mod(1n+U32.to_nat(a), Nat.pow(2n, 32n)) : Nat}

def u32_inc_wrap(a):
  internal_u32_inc_wrap(Nat.pow(2n, 32n), a, {==})

def internal_u32_to_nat_from_nat(+m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, k: Nat, h: MNat.lt(k, m)) -> {U32.to_nat(U32.from_nat(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      +h = h
      +ih = internal_u32_to_nat_from_nat(m, e, p, MNat.lt_trans(p, 1n+p, m, MNat.lt_succ_self(p), h))
      +hu = internal_lt_congl(1n+p, 1n+U32.to_nat(U32.from_nat(p)), m, Equal.cong(Nat, Nat, z => 1n+z, p, U32.to_nat(U32.from_nat(p)), Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, ih)), h)
      Equal.trans(Nat, U32.to_nat(U32.inc(U32.from_nat(p))), 1n+U32.to_nat(U32.from_nat(p)), 1n+p, internal_u32_inc_exact(m, U32.from_nat(p), e, hu), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(U32.from_nat(p)), p, ih))

# Converting a natural below 2^32 to U32 and back is the identity: k < 2^32 implies to_nat (from_nat k) = k.
law u32_to_nat_from_nat:
  for k: Nat
  for h: MNat.lt(k, Nat.pow(2n, 32n))
  {U32.to_nat(U32.from_nat(k)) == k : Nat}

def u32_to_nat_from_nat(k, h):
  internal_u32_to_nat_from_nat(Nat.pow(2n, 32n), {==}, k, h)

# Converting a U32 to a natural and back is the identity: from_nat (to_nat a) = a.
law u32_from_nat_to_nat:
  for a: U32
  {U32.from_nat(U32.to_nat(a)) == a : U32}

def u32_from_nat_to_nat(a):
  +a = a
  u32_to_nat_inj(U32.from_nat(U32.to_nat(a)), a, u32_to_nat_from_nat(U32.to_nat(a), u32_to_nat_lt(a)))

def internal_mod_succ_mod(+p: Nat, +m: Nat) -> {Nat.mod(1n+Nat.mod(p, m), m) == Nat.mod(1n+p, m) : Nat}:
  %MNat.mod_add_div(p, m) : {Nat.mod(1n+Nat.mod(p, m), m) == Nat.mod(1n+_, m) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(1n+Nat.mod(p, m), Nat.mul(m, Nat.div(p, m))), m), Nat.mod(1n+Nat.mod(p, m), m), MNat.add_mul_mod_self_left(1n+Nat.mod(p, m), m, Nat.div(p, m)))

def internal_u32_to_nat_from_nat_mod(+m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, k: Nat) -> {U32.to_nat(U32.from_nat(k)) == Nat.mod(k, m) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.mod(0n, m), 0n, MNat.zero_mod(m))
    case 1n++p:
      -u = U32.from_nat(p)
      Equal.trans(Nat, U32.to_nat(U32.inc(u)), Nat.mod(1n+U32.to_nat(u), m), Nat.mod(1n+p, m), internal_u32_inc_wrap(m, U32.from_nat(p), e), Equal.trans(Nat, Nat.mod(1n+U32.to_nat(u), m), Nat.mod(1n+Nat.mod(p, m), m), Nat.mod(1n+p, m), Equal.cong(Nat, Nat, z => Nat.mod(1n+z, m), U32.to_nat(u), Nat.mod(p, m), internal_u32_to_nat_from_nat_mod(m, e, p)), internal_mod_succ_mod(p, m)))

# Converting any natural to U32 and back reduces it modulo 2^32: to_nat (from_nat k) = k % 2^32.
law u32_to_nat_from_nat_mod:
  for k: Nat
  {U32.to_nat(U32.from_nat(k)) == Nat.mod(k, Nat.pow(2n, 32n)) : Nat}

def u32_to_nat_from_nat_mod(k):
  internal_u32_to_nat_from_nat_mod(Nat.pow(2n, 32n), {==}, k)

def internal_min_fin(+u: U32, +v: U32, c: Bool, e: {Nat.is_lt(U32.to_nat(u), U32.to_nat(v)) == c : Bool}) -> {U32.to_nat(Bool.pick(U32, c, u, v)) == Nat.min(U32.to_nat(u), U32.to_nat(v)) : Nat}:
  match c:
    case True{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(u), U32.to_nat(v)), U32.to_nat(u), MNat.min_eq_left(U32.to_nat(u), U32.to_nat(v), MNat.le_of_lt(U32.to_nat(u), U32.to_nat(v), e)))
    case False{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(u), U32.to_nat(v)), U32.to_nat(v), MNat.min_eq_right(U32.to_nat(u), U32.to_nat(v), MNat.le_of_not_lt(U32.to_nat(u), U32.to_nat(v), e)))

# The U32 minimum is the minimum of the values: to_nat (min a b) = min (to_nat a) (to_nat b).
law u32_min_to_nat:
  for a: U32
  for b: U32
  {U32.to_nat(U32.min(a, b)) == Nat.min(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u32_min_to_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      internal_min_fin(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), Equal.sym(Bool, U32.is_lt(U32{x}, U32{y}), Nat.is_lt(U32.to_nat(U32{x}), U32.to_nat(U32{y})), u32_is_lt_to_nat(U32{x}, U32{y})))

def internal_max_fin(+u: U32, +v: U32, c: Bool, e: {Nat.is_lt(U32.to_nat(u), U32.to_nat(v)) == c : Bool}) -> {U32.to_nat(Bool.pick(U32, c, v, u)) == Nat.max(U32.to_nat(u), U32.to_nat(v)) : Nat}:
  match c:
    case True{}:
      Equal.sym(Nat, Nat.max(U32.to_nat(u), U32.to_nat(v)), U32.to_nat(v), MNat.max_eq_right(U32.to_nat(u), U32.to_nat(v), MNat.le_of_lt(U32.to_nat(u), U32.to_nat(v), e)))
    case False{}:
      Equal.sym(Nat, Nat.max(U32.to_nat(u), U32.to_nat(v)), U32.to_nat(u), MNat.max_eq_left(U32.to_nat(u), U32.to_nat(v), MNat.le_of_not_lt(U32.to_nat(u), U32.to_nat(v), e)))

# The U32 maximum is the maximum of the values: to_nat (max a b) = max (to_nat a) (to_nat b).
law u32_max_to_nat:
  for a: U32
  for b: U32
  {U32.to_nat(U32.max(a, b)) == Nat.max(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u32_max_to_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      internal_max_fin(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), Equal.sym(Bool, U32.is_lt(U32{x}, U32{y}), Nat.is_lt(U32.to_nat(U32{x}), U32.to_nat(U32{y})), u32_is_lt_to_nat(U32{x}, U32{y})))

def internal_bit(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(n)
    case True{}:
      1n+Nat.double(n)

def internal_bit_con(-n: Nat, b: Bool, -w: Word(n)) -> {internal_bit(b, Word.to_nat(n, w)) == Word.to_nat(1n+n, WCon{b, w}) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_max_nat(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+Nat.double(internal_max_nat(p))

def internal_word_bound(+n: Nat, a: Word(n)) -> MNat.le(Word.to_nat(n, a), internal_max_nat(n)):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, +t}:
          MNat.le_trans(Nat.double(Word.to_nat(p, t)), Nat.double(internal_max_nat(p)), 1n+Nat.double(internal_max_nat(p)),
            MNat.double_le_double(Word.to_nat(p, t), internal_max_nat(p), internal_word_bound(p, t)),
            MNat.le_succ(Nat.double(internal_max_nat(p))))
        case WCon{True{}, +t}:
          MNat.double_le_double(Word.to_nat(p, t), internal_max_nat(p), internal_word_bound(p, t))

def internal_u32_word(a: U32) -> Word(32n):
  match a:
    case U32{w}:
      w

def internal_u32_word_nat(a: U32) -> {Word.to_nat(32n, internal_u32_word(a)) == U32.to_nat(a) : Nat}:
  match a:
    case U32{w}:
      {==}

def internal_bit_add(c: Bool, +x: Nat, +y: Nat) -> {internal_bit(c, Nat.add(x, y)) == Nat.add(internal_bit(c, x), Nat.double(y)) : Nat}:
  match c:
    case False{}:
      MNat.double_add(x, y)
    case True{}:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), MNat.double_add(x, y))

def internal_modulus(n: Nat) -> Nat:
  1n+internal_max_nat(n)

def internal_shift(+n: Nat, c: Bool, w: Word(n), r: Bool & Word(n)) -> Data:
  (hi, out) = r
  {internal_bit(c, Word.to_nat(n, w)) == Nat.add(Word.to_nat(n, out), Nat.mul(internal_bv(hi), internal_modulus(n))) : Nat}

def internal_shift_cons(+p: Nat, +c: Bool, +b: Bool, +w: Word(p), r: Bool & Word(p)) -> internal_shift(p, b, w, r) -> internal_shift(1n+p, c, WCon{b, w}, Word.shl.out.con(p, c, r)):
  (+hi, +out) = r
  h =>
    %internal_bit_con(p, b, w) : {internal_bit(c, _) == Nat.add(Word.to_nat(1n+p, WCon{c, out}), Nat.mul(internal_bv(hi), internal_modulus(1n+p))) : Nat}
    %internal_bit_con(p, c, out) : {internal_bit(c, internal_bit(b, Word.to_nat(p, w))) == Nat.add(_, Nat.mul(internal_bv(hi), internal_modulus(1n+p))) : Nat}
    +v = Word.to_nat(p, out)
    +k = Nat.mul(internal_bv(hi), internal_modulus(p))
    Equal.trans(Nat, internal_bit(c, internal_bit(b, Word.to_nat(p, w))), internal_bit(c, Nat.add(v, k)), Nat.add(internal_bit(c, v), Nat.mul(internal_bv(hi), internal_modulus(1n+p))),
      Equal.cong(Nat, Nat, z => internal_bit(c, z), internal_bit(b, Word.to_nat(p, w)), Nat.add(v, k), h),
      Equal.trans(Nat, internal_bit(c, Nat.add(v, k)), Nat.add(internal_bit(c, v), Nat.double(k)), Nat.add(internal_bit(c, v), Nat.mul(internal_bv(hi), internal_modulus(1n+p))),
        internal_bit_add(c, v, k),
        Equal.cong(Nat, Nat, z => Nat.add(internal_bit(c, v), z), Nat.double(k), Nat.mul(internal_bv(hi), internal_modulus(1n+p)),
          Equal.sym(Nat, Nat.mul(internal_bv(hi), Nat.double(internal_modulus(p))), Nat.double(k), MNat.mul_double(internal_bv(hi), internal_modulus(p))))))

def internal_shift_spec(+n: Nat, +c: Bool, +w: Word(n)) -> internal_shift(n, c, w, Word.shl.out(n, c, w)):
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          internal_shift_cons(p, c, b, t, Word.shl.out(p, b, t), internal_shift_spec(p, b, t))

def internal_add_modulus_not_le(+x: Nat, +m: Nat) -> {Nat.is_le(Nat.add(x, 1n+m), m) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(x, 1n+m), m), Nat.is_le(1n+Nat.add(x, m), m), False{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, m), Nat.add(x, 1n+m), 1n+Nat.add(x, m), MNat.add_succ(x, m)),
    MNat.not_le_of_lt(m, 1n+Nat.add(x, m), MNat.lt_of_le_of_lt(m, Nat.add(x, m), 1n+Nat.add(x, m), MNat.le_add_left(m, x), MNat.lt_succ_self(Nat.add(x, m)))))

def internal_shift_bounded(+n: Nat, +c: Bool, +w: Word(n), r: Bool & Word(n), h: internal_shift(n, c, w, r), bound: MNat.le(internal_bit(c, Word.to_nat(n, w)), internal_max_nat(n))) -> {Pair.fst(Bool, Word(n), r) == False{} : Bool} & {Word.to_nat(n, Pair.snd(Bool, Word(n), r)) == internal_bit(c, Word.to_nat(n, w)) : Nat}:
  match r:
    case Tuple{False{}, +out}:
      ({==}, Equal.sym(Nat, internal_bit(c, Word.to_nat(n, w)), Word.to_nat(n, out),
        Equal.trans(Nat, internal_bit(c, Word.to_nat(n, w)), Nat.add(Word.to_nat(n, out), 0n), Word.to_nat(n, out), h, MNat.add_zero(Word.to_nat(n, out)))))
    case Tuple{True{}, +out}:
      +v = Word.to_nat(n, out)
      +m = internal_max_nat(n)
      +hh = Equal.trans(Nat, internal_bit(c, Word.to_nat(n, w)), Nat.add(v, Nat.mul(1n, 1n+m)), Nat.add(v, 1n+m), h,
        Equal.cong(Nat, Nat, z => Nat.add(v, z), Nat.mul(1n, 1n+m), 1n+m, MNat.one_mul(1n+m)))
      Empty.absurd(({True{} == False{} : Bool} & {v == internal_bit(c, Word.to_nat(n, w)) : Nat}),
        MNat.internal_false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(Nat.add(v, 1n+m), m), True{},
          Equal.sym(Bool, Nat.is_le(Nat.add(v, 1n+m), m), False{}, internal_add_modulus_not_le(v, m)),
          Equal.trans(Bool, Nat.is_le(Nat.add(v, 1n+m), m), Nat.is_le(internal_bit(c, Word.to_nat(n, w)), m), True{},
            Equal.cong(Nat, Bool, z => Nat.is_le(z, m), Nat.add(v, 1n+m), internal_bit(c, Word.to_nat(n, w)), Equal.sym(Nat, internal_bit(c, Word.to_nat(n, w)), Nat.add(v, 1n+m), hh)), bound))))

def internal_bit_mono(c: Bool, +x: Nat, +y: Nat, h: MNat.le(x, y)) -> MNat.le(internal_bit(c, x), internal_bit(c, y)):
  match c:
    case False{}:
      MNat.double_le_double(x, y, h)
    case True{}:
      MNat.double_le_double(x, y, h)

def internal_max_nat_mono(+n: Nat, +m: Nat, h: MNat.le(n, m)) -> MNat.le(internal_max_nat(n), internal_max_nat(m)):
  match n m:
    case 0n _:
      MNat.zero_le(internal_max_nat(m))
    case 1n+p 0n:
      Empty.absurd(MNat.le(internal_max_nat(1n+p), 0n), MNat.internal_false_ne_true(h))
    case 1n++p 1n++q:
      MNat.double_le_double(internal_max_nat(p), internal_max_nat(q), internal_max_nat_mono(p, q, h))

def internal_bit_lt_double(c: Bool, +r: Nat, +b: Nat, h: MNat.lt(r, b)) -> MNat.lt(internal_bit(c, r), Nat.double(b)):
  match c:
    case False{}:
      MNat.double_lt_double(r, b, h)
    case True{}:
      internal_succ_double_lt(r, b, h)

def internal_sub_lt_double(+s: Nat, +b: Nat, ge: MNat.le(b, s), lt: MNat.lt(s, Nat.double(b))) -> MNat.lt(Nat.sub(s, b), b):
  %Equal.sym(Bool, Nat.is_lt(Nat.sub(s, b), b), Nat.is_lt(Nat.add(b, Nat.sub(s, b)), Nat.add(b, b)), MNat.add_lt_add_iff_left(b, Nat.sub(s, b), b)) : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, Nat.sub(s, b)), s, MNat.add_sub_of_le(b, s, ge)) : {Nat.is_lt(_, Nat.add(b, b)) == True{} : Bool}
  %MNat.double_eq_add(b) : {Nat.is_lt(s, _) == True{} : Bool}
  lt

def internal_bit_add_high(c: Bool, +x: Nat, +y: Nat) -> {Nat.add(Nat.double(x), internal_bit(c, y)) == internal_bit(c, Nat.add(x, y)) : Nat}:
  match c:
    case False{}:
      Equal.sym(Nat, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), MNat.double_add(x, y))
    case True{}:
      Equal.trans(Nat, Nat.add(Nat.double(x), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(x), Nat.double(y)), 1n+Nat.double(Nat.add(x, y)),
        MNat.add_succ(Nat.double(x), Nat.double(y)),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.double(x), Nat.double(y)), Nat.double(Nat.add(x, y)),
          Equal.sym(Nat, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), MNat.double_add(x, y))))

def internal_div_shift_eq(+q: Nat, +b: Nat, +r: Nat, +c: Bool) -> {Nat.add(Nat.mul(Nat.double(q), b), internal_bit(c, r)) == internal_bit(c, Nat.add(Nat.mul(q, b), r)) : Nat}:
  %MNat.double_mul(q, b) : {Nat.add(_, internal_bit(c, r)) == internal_bit(c, Nat.add(Nat.mul(q, b), r)) : Nat}
  internal_bit_add_high(c, Nat.mul(q, b), r)

def internal_div_spec(+m: Nat, a: Word(m), +b: U32, qr: Word(m) & U32) -> Type:
  (q, +r) = qr
  {Nat.add(Nat.mul(Word.to_nat(m, q), U32.to_nat(b)), U32.to_nat(r)) == Word.to_nat(m, a) : Nat} & MNat.lt(U32.to_nat(r), U32.to_nat(b))

def internal_div_rem_le(+m: Nat, +a: Word(m), +b: U32, qr: Word(m) & U32, v: internal_div_spec(m, a, b, qr)) -> MNat.le(U32.to_nat(Pair.snd(Word(m), U32, qr)), Word.to_nat(m, a)):
  (+q, +r) = qr
  (e, h) = v
  %e : {Nat.is_le(U32.to_nat(r), _) == True{} : Bool}
  MNat.le_add_left(U32.to_nat(r), Nat.mul(Word.to_nat(m, q), U32.to_nat(b)))

def internal_div_sub_eq(+q: Nat, +b: Nat, +s: Nat, h: MNat.le(b, s)) -> {Nat.add(Nat.mul(1n+q, b), Nat.sub(s, b)) == Nat.add(Nat.mul(q, b), s) : Nat}:
  +p = Nat.mul(q, b)
  +r = Nat.sub(s, b)
  Equal.trans(Nat, Nat.add(Nat.add(b, p), r), Nat.add(b, Nat.add(p, r)), Nat.add(p, s), MNat.add_assoc(b, p, r),
    Equal.trans(Nat, Nat.add(b, Nat.add(p, r)), Nat.add(p, Nat.add(b, r)), Nat.add(p, s), MNat.add_left_comm(b, p, r),
      Equal.cong(Nat, Nat, z => Nat.add(p, z), Nat.add(b, r), s, MNat.add_sub_of_le(b, s, h))))

def internal_u32_ge_nat(a: U32, b: U32) -> {U32.is_ge(a, b) == Nat.is_le(U32.to_nat(b), U32.to_nat(a)) : Bool}:
  +a = a
  +b = b
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b)) : {Cmp.is_ge(_) == Nat.is_le(U32.to_nat(b), U32.to_nat(a)) : Bool}
  MNat.is_ge_eq_is_le(U32.to_nat(a), U32.to_nat(b))

def internal_div_fin_spec(+p: Nat, +c: Bool, +a: Word(p), +b: U32, +q: Word(p), +s: U32, g: Bool, guard: {U32.is_ge(s, b) == g : Bool}, e: {Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), U32.to_nat(b)), U32.to_nat(s)) == internal_bit(c, Word.to_nat(p, a)) : Nat}, bound: MNat.lt(U32.to_nat(s), Nat.double(U32.to_nat(b)))) -> internal_div_spec(1n+p, WCon{c, a}, b, U32.divmod.go.fin(p, q, s, b, g)):
  match g:
    case False{}:
      (Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), U32.to_nat(b)), U32.to_nat(s)), internal_bit(c, Word.to_nat(p, a)), Word.to_nat(1n+p, WCon{c, a}), e, internal_bit_con(p, c, a)),
        MNat.lt_of_not_le(U32.to_nat(b), U32.to_nat(s),
          Equal.trans(Bool, Nat.is_le(U32.to_nat(b), U32.to_nat(s)), U32.is_ge(s, b), False{},
            Equal.sym(Bool, U32.is_ge(s, b), Nat.is_le(U32.to_nat(b), U32.to_nat(s)), internal_u32_ge_nat(s, b)), guard)))
    case True{}:
      +bv = U32.to_nat(b)
      +sv = U32.to_nat(s)
      +qv = Word.to_nat(p, q)
      +ge = Equal.trans(Bool, Nat.is_le(bv, sv), U32.is_ge(s, b), True{}, Equal.sym(Bool, U32.is_ge(s, b), Nat.is_le(bv, sv), internal_u32_ge_nat(s, b)), guard)
      +sub = u32_sub_exact(s, b, ge)
      (Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(qv), bv), U32.to_nat(U32.sub(s, b))), Nat.add(Nat.mul(1n+Nat.double(qv), bv), Nat.sub(sv, bv)), Word.to_nat(1n+p, WCon{c, a}),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(1n+Nat.double(qv), bv), z), U32.to_nat(U32.sub(s, b)), Nat.sub(sv, bv), sub),
        Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(qv), bv), Nat.sub(sv, bv)), Nat.add(Nat.mul(Nat.double(qv), bv), sv), Word.to_nat(1n+p, WCon{c, a}),
          internal_div_sub_eq(Nat.double(qv), bv, sv, ge),
          Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(qv), bv), sv), internal_bit(c, Word.to_nat(p, a)), Word.to_nat(1n+p, WCon{c, a}), e, internal_bit_con(p, c, a)))),
       Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(s, b)), bv), Nat.is_lt(Nat.sub(sv, bv), bv), True{},
         Equal.cong(Nat, Bool, z => Nat.is_lt(z, bv), U32.to_nat(U32.sub(s, b)), Nat.sub(sv, bv), sub), internal_sub_lt_double(sv, bv, ge, bound)))

def internal_shifted(c: Bool, r: U32, ts: Bool & Word(32n)) -> Type:
  (top, w) = ts
  {top == False{} : Bool} & {Word.to_nat(32n, w) == internal_bit(c, U32.to_nat(r)) : Nat}

def internal_div_shift_step(+p: Nat, +c: Bool, +a: Word(p), +b: U32, +q: Word(p), +r: U32, ts: Bool & Word(32n), shifted: internal_shifted(c, r, ts), v: internal_div_spec(p, a, b, (q, r))) -> internal_div_spec(1n+p, WCon{c, a}, b, U32.divmod.go.shl(p, q, b, ts)):
  match ts:
    case Tuple{False{}, +out}:
      (z, +se) = shifted
      (+e, hr) = v
      +qv = Word.to_nat(p, q)
      +bv = U32.to_nat(b)
      +rv = U32.to_nat(r)
      +sv = Word.to_nat(32n, out)
      internal_div_fin_spec(p, c, a, b, q, U32{out}, U32.is_ge(U32{out}, b), {==},
        Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(qv), bv), sv), Nat.add(Nat.mul(Nat.double(qv), bv), internal_bit(c, rv)), internal_bit(c, Word.to_nat(p, a)),
          Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.double(qv), bv), z), sv, internal_bit(c, rv), se),
          Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(qv), bv), internal_bit(c, rv)), internal_bit(c, Nat.add(Nat.mul(qv, bv), rv)), internal_bit(c, Word.to_nat(p, a)),
            internal_div_shift_eq(qv, bv, rv, c), Equal.cong(Nat, Nat, z => internal_bit(c, z), Nat.add(Nat.mul(qv, bv), rv), Word.to_nat(p, a), e))),
        Equal.trans(Bool, Nat.is_lt(sv, Nat.double(bv)), Nat.is_lt(internal_bit(c, rv), Nat.double(bv)), True{},
          Equal.cong(Nat, Bool, z => Nat.is_lt(z, Nat.double(bv)), sv, internal_bit(c, rv), se), internal_bit_lt_double(c, rv, bv, hr)))
    case Tuple{True{}, out}:
      (h, e) = shifted
      Empty.absurd(internal_div_spec(1n+p, WCon{c, a}, b, U32.divmod.go.shl(p, q, b, (True{}, out))),
        MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, h)))

# The dividend prefix bounds the shift even when twice the divisor exceeds 2^32.
def internal_div_shift_bound(+p: Nat, +c: Bool, +a: Word(p), +b: U32, +q: Word(p), +r: U32, width: MNat.le(1n+p, 32n), v: internal_div_spec(p, a, b, (q, r))) -> MNat.le(internal_bit(c, U32.to_nat(r)), internal_max_nat(32n)):
  MNat.le_trans(internal_bit(c, U32.to_nat(r)), internal_bit(c, Word.to_nat(p, a)), internal_max_nat(32n),
    internal_bit_mono(c, U32.to_nat(r), Word.to_nat(p, a), internal_div_rem_le(p, a, b, (q, r), v)),
    MNat.le_trans(internal_bit(c, Word.to_nat(p, a)), internal_max_nat(1n+p), internal_max_nat(32n),
      Equal.trans(Bool, Nat.is_le(internal_bit(c, Word.to_nat(p, a)), internal_max_nat(1n+p)), Nat.is_le(Word.to_nat(1n+p, WCon{c, a}), internal_max_nat(1n+p)), True{},
        Equal.cong(Nat, Bool, z => Nat.is_le(z, internal_max_nat(1n+p)), internal_bit(c, Word.to_nat(p, a)), Word.to_nat(1n+p, WCon{c, a}), internal_bit_con(p, c, a)),
        internal_word_bound(1n+p, WCon{c, a})),
      internal_max_nat_mono(1n+p, 32n, width)))

# F31: keep the closed width-32 bound abstract in dependent matches.
def internal_rec_word(+p: Nat, +c: Bool, +b: U32, +q: Word(p), r: U32) -> {U32.divmod.go.shl(p, q, b, Word.shl.out(32n, c, internal_u32_word(r))) == U32.divmod.go.rec(p, c, b, (q, r)) : Word(1n+p) & U32}:
  match r:
    case U32{w}:
      {==}

def internal_shift_bound_word(+c: Bool, +r: U32, +limit: Nat, h: MNat.le(internal_bit(c, U32.to_nat(r)), limit)) -> MNat.le(internal_bit(c, Word.to_nat(32n, internal_u32_word(r))), limit):
  Equal.trans(Bool, Nat.is_le(internal_bit(c, Word.to_nat(32n, internal_u32_word(r))), limit), Nat.is_le(internal_bit(c, U32.to_nat(r)), limit), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(internal_bit(c, z), limit), Word.to_nat(32n, internal_u32_word(r)), U32.to_nat(r), internal_u32_word_nat(r)), h)

def internal_shifted_from_word(+c: Bool, +r: U32, ts: Bool & Word(32n), v: {Pair.fst(Bool, Word(32n), ts) == False{} : Bool} & {Word.to_nat(32n, Pair.snd(Bool, Word(32n), ts)) == internal_bit(c, Word.to_nat(32n, internal_u32_word(r))) : Nat}) -> internal_shifted(c, r, ts):
  match ts:
    case Tuple{top, +out}:
      (z, e) = v
      (z, Equal.trans(Nat, Word.to_nat(32n, out), internal_bit(c, Word.to_nat(32n, internal_u32_word(r))), internal_bit(c, U32.to_nat(r)), e,
        Equal.cong(Nat, Nat, x => internal_bit(c, x), Word.to_nat(32n, internal_u32_word(r)), U32.to_nat(r), internal_u32_word_nat(r))))

def internal_div_rec_spec(+p: Nat, +c: Bool, +a: Word(p), +b: U32, qr: Word(p) & U32, width: MNat.le(1n+p, 32n), v: internal_div_spec(p, a, b, qr)) -> internal_div_spec(1n+p, WCon{c, a}, b, U32.divmod.go.rec(p, c, b, qr)):
  match qr:
    case Tuple{+q, +r}:
      (+e, +hr) = v
      %internal_rec_word(p, c, b, q, r) : internal_div_spec(1n+p, WCon{c, a}, b, _)
      internal_div_shift_step(p, c, a, b, q, r, Word.shl.out(32n, c, internal_u32_word(r)),
        internal_shifted_from_word(c, r, Word.shl.out(32n, c, internal_u32_word(r)),
          internal_shift_bounded(32n, c, internal_u32_word(r), Word.shl.out(32n, c, internal_u32_word(r)), internal_shift_spec(32n, c, internal_u32_word(r)),
            internal_shift_bound_word(c, r, internal_max_nat(32n), internal_div_shift_bound(p, c, a, b, q, r, width, (e, hr))))), (e, hr))

def internal_divmod_spec(+m: Nat, +a: Word(m), +b: U32, +width: MNat.le(m, 32n), positive: MNat.lt(0n, U32.to_nat(b))) -> internal_div_spec(m, a, b, U32.divmod.go(m, a, b)):
  match m a:
    case 0n WNil{}:
      ({==}, positive)
    case 1n+p WCon{+c, +hi}:
      internal_div_rec_spec(p, c, hi, b, U32.divmod.go(p, hi, b), width,
        internal_divmod_spec(p, hi, b, MNat.le_trans(p, 1n+p, 32n, MNat.le_succ(p), width), positive))

def internal_u32_zero_nat(a: U32) -> {U32.is_zero(a) == Nat.is_eq(U32.to_nat(a), 0n) : Bool}:
  +a = a
  Equal.cong(Cmp, Bool, Cmp.is_eq, U32.cmp(a, 0), Nat.cmp(U32.to_nat(a), 0n), u32_cmp_to_nat(a, 0))

def internal_div_from_spec(+q: Nat, +r: Nat, +a: Nat, b: Nat, e: {Nat.add(Nat.mul(q, b), r) == a : Nat}, hr: MNat.lt(r, b), positive: MNat.lt(0n, b)) -> {q == Nat.div(a, b) : Nat}:
  match b:
    case 0n:
      Empty.absurd({q == Nat.div(a, 0n) : Nat}, MNat.internal_false_ne_true(positive))
    case 1n++bp:
      %e : {q == Nat.div(_, 1n+bp) : Nat}
      %MNat.add_comm(r, Nat.mul(q, 1n+bp)) : {q == Nat.div(_, 1n+bp) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(r, Nat.mul(q, 1n+bp)), 1n+bp), Nat.add(Nat.div(r, 1n+bp), q), MNat.add_mul_div_right(r, q, bp)) : {q == _ : Nat}
      %Equal.sym(Nat, Nat.div(r, 1n+bp), 0n, MNat.div_eq_zero_of_le(r, bp, MNat.le_of_lt_succ(r, bp, hr))) : {q == Nat.add(_, q) : Nat}
      {==}

def internal_div_nat_result(+a: Word(32n), +b: U32, qr: Word(32n) & U32, positive: MNat.lt(0n, U32.to_nat(b)), v: internal_div_spec(32n, a, b, qr)) -> {U32.to_nat(U32.div.fin(qr)) == Nat.div(Word.to_nat(32n, a), U32.to_nat(b)) : Nat}:
  (+q, +r) = qr
  (e, hr) = v
  internal_div_from_spec(Word.to_nat(32n, q), U32.to_nat(r), Word.to_nat(32n, a), U32.to_nat(b), e, hr, positive)

def internal_div_word(a: U32, b: U32) -> {U32.div.if(internal_u32_word(a), b, U32.is_zero(b)) == U32.div(a, b) : U32}:
  match a b:
    case U32{x} U32{y}:
      {==}

def internal_positive_of_zero_false(n: Nat, h: {Nat.is_eq(n, 0n) == False{} : Bool}) -> MNat.lt(0n, n):
  match n:
    case 0n:
      Empty.absurd({False{} == True{} : Bool}, MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+p:
      {==}

def internal_u32_positive_of_nonzero(+a: U32, h: {U32.is_zero(a) == False{} : Bool}) -> MNat.lt(0n, U32.to_nat(a)):
  internal_positive_of_zero_false(U32.to_nat(a), Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), 0n), U32.is_zero(a), False{},
    Equal.sym(Bool, U32.is_zero(a), Nat.is_eq(U32.to_nat(a), 0n), internal_u32_zero_nat(a)), h))

def internal_to_nat_div_if(z: Bool, +a: U32, +b: U32, e: {U32.is_zero(b) == z : Bool}) -> {U32.to_nat(U32.div.if(internal_u32_word(a), b, z)) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match z:
    case True{}:
      +zero = MNat.eq_of_is_eq(U32.to_nat(b), 0n,
        Equal.trans(Bool, Nat.is_eq(U32.to_nat(b), 0n), U32.is_zero(b), True{},
          Equal.sym(Bool, U32.is_zero(b), Nat.is_eq(U32.to_nat(b), 0n), internal_u32_zero_nat(b)), e))
      %Equal.sym(Nat, U32.to_nat(b), 0n, zero) : {U32.to_nat(0) == Nat.div(U32.to_nat(a), _) : Nat}
      {==}
    case False{}:
      +positive = internal_u32_positive_of_nonzero(b, e)
      %internal_u32_word_nat(a) : {U32.to_nat(U32.div.fin(U32.divmod.go(32n, internal_u32_word(a), b))) == Nat.div(_, U32.to_nat(b)) : Nat}
      internal_div_nat_result(internal_u32_word(a), b, U32.divmod.go(32n, internal_u32_word(a), b), positive,
        internal_divmod_spec(32n, internal_u32_word(a), b, MNat.le_refl(32n), positive))

# U32 division agrees with natural division, including the zero-divisor quotient of zero.
law u32_to_nat_div:
  for +a: U32
  for +b: U32
  {U32.to_nat(U32.div(a, b)) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}

def u32_to_nat_div(a, b):
  %internal_div_word(a, b) : {U32.to_nat(_) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}
  internal_to_nat_div_if(U32.is_zero(b), a, b, {==})

def internal_u32_div_antitone_nat(+a: U32, +s: U32, +t: U32, +st: MNat.le(U32.to_nat(s), U32.to_nat(t)), +positive: MNat.lt(0n, U32.to_nat(s))) -> MNat.le(U32.to_nat(U32.div(a, t)), U32.to_nat(U32.div(a, s))):
  %Equal.sym(Nat, U32.to_nat(U32.div(a, t)), Nat.div(U32.to_nat(a), U32.to_nat(t)), u32_to_nat_div(a, t)) : {Nat.is_le(_, U32.to_nat(U32.div(a, s))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.div(a, s)), Nat.div(U32.to_nat(a), U32.to_nat(s)), u32_to_nat_div(a, s)) : {Nat.is_le(Nat.div(U32.to_nat(a), U32.to_nat(t)), _) == True{} : Bool}
  MNat.div_antitone(U32.to_nat(a), U32.to_nat(s), U32.to_nat(t), st, positive)

# Increasing a positive U32 divisor cannot increase the quotient: 0 < s <= t implies a / t <= a / s.
law u32_div_antitone:
  for +a: U32
  for +s: U32
  for +t: U32
  for st: {U32.is_le(s, t) == True{} : Bool}
  for positive: {U32.is_lt(0, s) == True{} : Bool}
  {U32.is_le(U32.div(a, t), U32.div(a, s)) == True{} : Bool}

def u32_div_antitone(a, s, t, st, positive):
  %Equal.sym(Bool, U32.is_le(U32.div(a, t), U32.div(a, s)), Nat.is_le(U32.to_nat(U32.div(a, t)), U32.to_nat(U32.div(a, s))), u32_is_le_to_nat(U32.div(a, t), U32.div(a, s))) : {_ == True{} : Bool}
  internal_u32_div_antitone_nat(a, s, t,
    Equal.trans(Bool, Nat.is_le(U32.to_nat(s), U32.to_nat(t)), U32.is_le(s, t), True{},
      Equal.sym(Bool, U32.is_le(s, t), Nat.is_le(U32.to_nat(s), U32.to_nat(t)), u32_is_le_to_nat(s, t)), st),
    Equal.trans(Bool, Nat.is_lt(0n, U32.to_nat(s)), U32.is_lt(0, s), True{},
      Equal.sym(Bool, U32.is_lt(0, s), Nat.is_lt(0n, U32.to_nat(s)), u32_is_lt_to_nat(0, s)), positive))

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# The zero word is the natural zero: to_nat (zero n) = 0, reversed to rewrite toward the simple side.
law word_to_nat_zero_sym:
  for n: Nat
  {0n == Word.to_nat(n, Word.zero(n)) : Nat}

def word_to_nat_zero_sym(n):
  Equal.sym(Nat, Word.to_nat(n, Word.zero(n)), 0n, word_to_nat_zero(n))

# Comparing words compares their values: cmp a b = cmp (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law word_cmp_to_nat_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) == Word.cmp(n, a, b) : Cmp}

def word_cmp_to_nat_sym(n, a, b):
  Equal.sym(Cmp, Word.cmp(n, a, b), Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)), word_cmp_to_nat(n, a, b))

# One plus a word plus its complement is two to the width: 1 + to_nat (not w) + to_nat w = 2^n, reversed to rewrite toward the simple side.
law word_not_add_sym:
  for n: Nat
  for w: Word(n)
  {Nat.pow(2n, n) == 1n+Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)) : Nat}

def word_not_add_sym(n, w):
  Equal.sym(Nat, 1n+Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)), Nat.pow(2n, n), word_not_add(n, w))

# The adder is exact below the overflow: a + b + carry-in < 2^n implies to_nat (adc a b False c) = a + b + carry-in, reversed to rewrite toward the simple side.
law word_adc_exact_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  for h: MNat.lt(Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n))
  {Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)) == Word.to_nat(n, Word.adc(n, a, b, False{}, c)) : Nat}

def word_adc_exact_sym(n, a, b, c, h):
  Equal.sym(Nat, Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), word_adc_exact(n, a, b, c, h))

# The adder drops exactly one 2^n on overflow: 2^n <= a + b + carry-in implies to_nat (adc a b False c) + 2^n = a + b + carry-in, reversed to rewrite toward the simple side.
law word_adc_overflow_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  for h: MNat.le(Nat.pow(2n, n), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)))
  {Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)) == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.pow(2n, n)) : Nat}

def word_adc_overflow_sym(n, a, b, c, h):
  Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.pow(2n, n)), Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), word_adc_overflow(n, a, b, c, h))

# The adder wraps modulo 2^n: to_nat (adc a b False c) = (a + b + carry-in) % 2^n, reversed to rewrite toward the simple side.
law word_adc_wrap_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {Nat.mod(Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n)) == Word.to_nat(n, Word.adc(n, a, b, False{}, c)) : Nat}

def word_adc_wrap_sym(n, a, b, c):
  Equal.sym(Nat, Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.mod(Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Bool.pick(Nat, c, 1n, 0n)), Nat.pow(2n, n)), word_adc_wrap(n, a, b, c))

# Word addition is exact without overflow: a + b < 2^n implies to_nat (add a b) = a + b, reversed to rewrite toward the simple side.
law word_add_exact_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: MNat.lt(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n))
  {Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) == Word.to_nat(n, Word.add(n, a, b)) : Nat}

def word_add_exact_sym(n, a, b, h):
  Equal.sym(Nat, Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), word_add_exact(n, a, b, h))

# Word addition wraps modulo 2^n: to_nat (add a b) = (a + b) % 2^n, reversed to rewrite toward the simple side.
law word_add_wrap_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Nat.mod(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)) == Word.to_nat(n, Word.add(n, a, b)) : Nat}

def word_add_wrap_sym(n, a, b):
  Equal.sym(Nat, Word.to_nat(n, Word.add(n, a, b)), Nat.mod(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)), word_add_wrap(n, a, b))

# Increment is exact without overflow: 1 + w < 2^n implies to_nat (inc w) = 1 + w, reversed to rewrite toward the simple side.
law word_inc_exact_sym:
  for n: Nat
  for w: Word(n)
  for h: MNat.lt(1n+Word.to_nat(n, w), Nat.pow(2n, n))
  {1n+Word.to_nat(n, w) == Word.to_nat(n, Word.inc(n, w)) : Nat}

def word_inc_exact_sym(n, w, h):
  Equal.sym(Nat, Word.to_nat(n, Word.inc(n, w)), 1n+Word.to_nat(n, w), word_inc_exact(n, w, h))

# Increment wraps modulo 2^n: to_nat (inc w) = (1 + w) % 2^n, reversed to rewrite toward the simple side.
law word_inc_wrap_sym:
  for n: Nat
  for w: Word(n)
  {Nat.mod(1n+Word.to_nat(n, w), Nat.pow(2n, n)) == Word.to_nat(n, Word.inc(n, w)) : Nat}

def word_inc_wrap_sym(n, w):
  Equal.sym(Nat, Word.to_nat(n, Word.inc(n, w)), Nat.mod(1n+Word.to_nat(n, w), Nat.pow(2n, n)), word_inc_wrap(n, w))

# Word subtraction is exact without underflow: b <= a implies to_nat (sub a b) = a - b, reversed to rewrite toward the simple side.
law word_sub_exact_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: MNat.le(Word.to_nat(n, b), Word.to_nat(n, a))
  {Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b)) == Word.to_nat(n, Word.sub(n, a, b)) : Nat}

def word_sub_exact_sym(n, a, b, h):
  Equal.sym(Nat, Word.to_nat(n, Word.sub(n, a, b)), Nat.sub(Word.to_nat(n, a), Word.to_nat(n, b)), word_sub_exact(n, a, b, h))

# Word subtraction wraps modulo 2^n: to_nat (sub a b) = (a + (2^n - b)) % 2^n, reversed to rewrite toward the simple side.
law word_sub_wrap_sym:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Nat.mod(Nat.add(Word.to_nat(n, a), Nat.sub(Nat.pow(2n, n), Word.to_nat(n, b))), Nat.pow(2n, n)) == Word.to_nat(n, Word.sub(n, a, b)) : Nat}

def word_sub_wrap_sym(n, a, b):
  Equal.sym(Nat, Word.to_nat(n, Word.sub(n, a, b)), Nat.mod(Nat.add(Word.to_nat(n, a), Nat.sub(Nat.pow(2n, n), Word.to_nat(n, b))), Nat.pow(2n, n)), word_sub_wrap(n, a, b))

# Comparing U32s compares their values: cmp a b = cmp (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_cmp_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.cmp(U32.to_nat(a), U32.to_nat(b)) == U32.cmp(a, b) : Cmp}

def u32_cmp_to_nat_sym(a, b):
  Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_cmp_to_nat(a, b))

# U32 equality tests the values: is_eq a b = is_eq (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_is_eq_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == U32.is_eq(a, b) : Bool}

def u32_is_eq_to_nat_sym(a, b):
  Equal.sym(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), u32_is_eq_to_nat(a, b))

# U32 disequality tests the values: is_ne a b = is_ne (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_is_ne_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.is_ne(U32.to_nat(a), U32.to_nat(b)) == U32.is_ne(a, b) : Bool}

def u32_is_ne_to_nat_sym(a, b):
  Equal.sym(Bool, U32.is_ne(a, b), Nat.is_ne(U32.to_nat(a), U32.to_nat(b)), u32_is_ne_to_nat(a, b))

# The U32 strict order is the order of the values: is_lt a b = is_lt (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_is_lt_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == U32.is_lt(a, b) : Bool}

def u32_is_lt_to_nat_sym(a, b):
  Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), u32_is_lt_to_nat(a, b))

# The U32 order is the order of the values: is_le a b = is_le (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_is_le_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == U32.is_le(a, b) : Bool}

def u32_is_le_to_nat_sym(a, b):
  Equal.sym(Bool, U32.is_le(a, b), Nat.is_le(U32.to_nat(a), U32.to_nat(b)), u32_is_le_to_nat(a, b))

# The reverse U32 strict order is that of the values: is_gt a b = is_gt (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_is_gt_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.is_gt(U32.to_nat(a), U32.to_nat(b)) == U32.is_gt(a, b) : Bool}

def u32_is_gt_to_nat_sym(a, b):
  Equal.sym(Bool, U32.is_gt(a, b), Nat.is_gt(U32.to_nat(a), U32.to_nat(b)), u32_is_gt_to_nat(a, b))

# The reverse U32 order is that of the values: is_ge a b = is_ge (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_is_ge_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.is_ge(U32.to_nat(a), U32.to_nat(b)) == U32.is_ge(a, b) : Bool}

def u32_is_ge_to_nat_sym(a, b):
  Equal.sym(Bool, U32.is_ge(a, b), Nat.is_ge(U32.to_nat(a), U32.to_nat(b)), u32_is_ge_to_nat(a, b))

# U32 addition is exact without overflow: a + b < 2^32 implies to_nat (a + b) = a + b, reversed to rewrite toward the simple side.
law u32_add_exact_sym:
  for a: U32
  for b: U32
  for h: MNat.lt(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n))
  {Nat.add(U32.to_nat(a), U32.to_nat(b)) == U32.to_nat(U32.add(a, b)) : Nat}

def u32_add_exact_sym(a, b, h):
  Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b)), u32_add_exact(a, b, h))

# U32 addition wraps modulo 2^32: to_nat (a + b) = (a + b) % 2^32, reversed to rewrite toward the simple side.
law u32_add_wrap_sym:
  for a: U32
  for b: U32
  {Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)) == U32.to_nat(U32.add(a, b)) : Nat}

def u32_add_wrap_sym(a, b):
  Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.pow(2n, 32n)), u32_add_wrap(a, b))

# U32 subtraction is exact without underflow: b <= a implies to_nat (a - b) = a - b, reversed to rewrite toward the simple side.
law u32_sub_exact_sym:
  for a: U32
  for b: U32
  for h: MNat.le(U32.to_nat(b), U32.to_nat(a))
  {Nat.sub(U32.to_nat(a), U32.to_nat(b)) == U32.to_nat(U32.sub(a, b)) : Nat}

def u32_sub_exact_sym(a, b, h):
  Equal.sym(Nat, U32.to_nat(U32.sub(a, b)), Nat.sub(U32.to_nat(a), U32.to_nat(b)), u32_sub_exact(a, b, h))

# U32 subtraction wraps modulo 2^32: to_nat (a - b) = (a + (2^32 - b)) % 2^32, reversed to rewrite toward the simple side.
law u32_sub_wrap_sym:
  for a: U32
  for b: U32
  {Nat.mod(Nat.add(U32.to_nat(a), Nat.sub(Nat.pow(2n, 32n), U32.to_nat(b))), Nat.pow(2n, 32n)) == U32.to_nat(U32.sub(a, b)) : Nat}

def u32_sub_wrap_sym(a, b):
  Equal.sym(Nat, U32.to_nat(U32.sub(a, b)), Nat.mod(Nat.add(U32.to_nat(a), Nat.sub(Nat.pow(2n, 32n), U32.to_nat(b))), Nat.pow(2n, 32n)), u32_sub_wrap(a, b))

# U32 increment is exact without overflow: 1 + a < 2^32 implies to_nat (inc a) = 1 + a, reversed to rewrite toward the simple side.
law u32_inc_exact_sym:
  for a: U32
  for h: MNat.lt(1n+U32.to_nat(a), Nat.pow(2n, 32n))
  {1n+U32.to_nat(a) == U32.to_nat(U32.inc(a)) : Nat}

def u32_inc_exact_sym(a, h):
  Equal.sym(Nat, U32.to_nat(U32.inc(a)), 1n+U32.to_nat(a), u32_inc_exact(a, h))

# U32 increment wraps modulo 2^32: to_nat (inc a) = (1 + a) % 2^32, reversed to rewrite toward the simple side.
law u32_inc_wrap_sym:
  for a: U32
  {Nat.mod(1n+U32.to_nat(a), Nat.pow(2n, 32n)) == U32.to_nat(U32.inc(a)) : Nat}

def u32_inc_wrap_sym(a):
  Equal.sym(Nat, U32.to_nat(U32.inc(a)), Nat.mod(1n+U32.to_nat(a), Nat.pow(2n, 32n)), u32_inc_wrap(a))

# Converting a natural below 2^32 to U32 and back is the identity: k < 2^32 implies to_nat (from_nat k) = k, reversed to rewrite toward the simple side.
law u32_to_nat_from_nat_sym:
  for k: Nat
  for h: MNat.lt(k, Nat.pow(2n, 32n))
  {k == U32.to_nat(U32.from_nat(k)) : Nat}

def u32_to_nat_from_nat_sym(k, h):
  Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, u32_to_nat_from_nat(k, h))

# Converting a U32 to a natural and back is the identity: from_nat (to_nat a) = a, reversed to rewrite toward the simple side.
law u32_from_nat_to_nat_sym:
  for a: U32
  {a == U32.from_nat(U32.to_nat(a)) : U32}

def u32_from_nat_to_nat_sym(a):
  Equal.sym(U32, U32.from_nat(U32.to_nat(a)), a, u32_from_nat_to_nat(a))

# Converting any natural to U32 and back reduces it modulo 2^32: to_nat (from_nat k) = k % 2^32, reversed to rewrite toward the simple side.
law u32_to_nat_from_nat_mod_sym:
  for k: Nat
  {Nat.mod(k, Nat.pow(2n, 32n)) == U32.to_nat(U32.from_nat(k)) : Nat}

def u32_to_nat_from_nat_mod_sym(k):
  Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), Nat.mod(k, Nat.pow(2n, 32n)), u32_to_nat_from_nat_mod(k))

# The U32 minimum is the minimum of the values: to_nat (min a b) = min (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_min_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.min(U32.to_nat(a), U32.to_nat(b)) == U32.to_nat(U32.min(a, b)) : Nat}

def u32_min_to_nat_sym(a, b):
  Equal.sym(Nat, U32.to_nat(U32.min(a, b)), Nat.min(U32.to_nat(a), U32.to_nat(b)), u32_min_to_nat(a, b))

# The U32 maximum is the maximum of the values: to_nat (max a b) = max (to_nat a) (to_nat b), reversed to rewrite toward the simple side.
law u32_max_to_nat_sym:
  for a: U32
  for b: U32
  {Nat.max(U32.to_nat(a), U32.to_nat(b)) == U32.to_nat(U32.max(a, b)) : Nat}

def u32_max_to_nat_sym(a, b):
  Equal.sym(Nat, U32.to_nat(U32.max(a, b)), Nat.max(U32.to_nat(a), U32.to_nat(b)), u32_max_to_nat(a, b))

# U32 division agrees with natural division, including the zero-divisor quotient of zero, reversed to rewrite toward the simple side.
law u32_to_nat_div_sym:
  for +a: U32
  for +b: U32
  {Nat.div(U32.to_nat(a), U32.to_nat(b)) == U32.to_nat(U32.div(a, b)) : Nat}

def u32_to_nat_div_sym(a, b):
  Equal.sym(Nat, U32.to_nat(U32.div(a, b)), Nat.div(U32.to_nat(a), U32.to_nat(b)), u32_to_nat_div(a, b))
