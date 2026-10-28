# bend-mathlib/u32.bend: machine words as naturals; Word(n) and U32 operations agree with Nat arithmetic
# (compare, add, sub, inc, not, min, max, from_nat).
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
