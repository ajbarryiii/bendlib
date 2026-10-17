# bend-mathlib/string.bend: String append, reverse and length, and comparison.
# Comparison descends String.eq -> String.order -> String.cmp -> Char.cmp -> U32.cmp -> Word.cmp.
import Base
import ./nat.bend as MNat
import ./bool.bend as MBool

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def internal_append_nil(a: String) -> {a == String.append(a, SNil{}) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_append_nil(t) : {SCon{h, t} == SCon{h, _} : String}
      {==}

# The empty string is a right identity for append: a ++ "" = a.
law append_nil:
  for a: String
  {String.append(a, SNil{}) == a : String}

def append_nil(a):
  Equal.sym(String, a, String.append(a, SNil{}), internal_append_nil(a))

# The empty string is a left identity for append: "" ++ a = a.
law nil_append:
  for -a: String
  {String.append(SNil{}, a) == a : String}

def nil_append(a):
  {==}

def internal_append_assoc(a: String, -b: String, -c: String) -> {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_append_assoc(t, b, c) : {SCon{h, String.append(t, String.append(b, c))} == SCon{h, _} : String}
      {==}

# Append is associative: (a ++ b) ++ c = a ++ (b ++ c).
law append_assoc:
  for a: String
  for -b: String
  for -c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def append_assoc(a, b, c):
  Equal.sym(String, String.append(a, String.append(b, c)), String.append(String.append(a, b), c), internal_append_assoc(a, b, c))

def internal_length_append(a: String, -b: String) -> {Nat.add(String.length(a), String.length(b)) == String.length(String.append(a, b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_length_append(t, b) : {1n+Nat.add(String.length(t), String.length(b)) == 1n+_ : Nat}
      {==}

# The length of an append is the sum of the lengths.
law length_append:
  for a: String
  for -b: String
  {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}

def length_append(a, b):
  Equal.sym(Nat, Nat.add(String.length(a), String.length(b)), String.length(String.append(a, b)), internal_length_append(a, b))

def internal_reverse_go_spec(s: String, +acc: String) -> {String.append(String.reverse(s), acc) == String.reverse.go(s, acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_reverse_go_spec(t, SCon{h, SNil{}}) : {String.append(_, acc) == String.reverse.go(t, SCon{h, acc}) : String}
      %internal_append_assoc(String.reverse(t), SCon{h, SNil{}}, acc) : {_ == String.reverse.go(t, SCon{h, acc}) : String}
      %internal_reverse_go_spec(t, SCon{h, acc}) : {String.append(String.reverse(t), SCon{h, acc}) == _ : String}
      {==}

# The reverse accumulator loop appends the reversed string to the accumulator.
law reverse_go_spec:
  for s: String
  for acc: String
  {String.reverse.go(s, acc) == String.append(String.reverse(s), acc) : String}

def reverse_go_spec(s, acc):
  Equal.sym(String, String.append(String.reverse(s), acc), String.reverse.go(s, acc), internal_reverse_go_spec(s, acc))

def internal_reverse_append(a: String, +b: String) -> {String.append(String.reverse(b), String.reverse(a)) == String.reverse(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      %internal_append_nil(String.reverse(b)) : {_ == String.reverse(b) : String}
      {==}
    case SCon{+h, +t}:
      %internal_reverse_go_spec(t, SCon{h, SNil{}}) : {String.append(String.reverse(b), _) == String.reverse.go(String.append(t, b), SCon{h, SNil{}}) : String}
      %internal_reverse_go_spec(String.append(t, b), SCon{h, SNil{}}) : {String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})) == _ : String}
      %internal_reverse_append(t, b) : {String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})) == String.append(_, SCon{h, SNil{}}) : String}
      %internal_append_assoc(String.reverse(b), String.reverse(t), SCon{h, SNil{}}) : {String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})) == _ : String}
      {==}

# Reversing an append reverses and swaps the parts: reverse (a ++ b) = reverse b ++ reverse a.
law reverse_append:
  for a: String
  for b: String
  {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}

def reverse_append(a, b):
  Equal.sym(String, String.append(String.reverse(b), String.reverse(a)), String.reverse(String.append(a, b)), internal_reverse_append(a, b))

def internal_reverse_reverse(a: String) -> {a == String.reverse(String.reverse(a)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_reverse_go_spec(t, SCon{h, SNil{}}) : {SCon{h, t} == String.reverse.go(_, SNil{}) : String}
      %internal_reverse_append(String.reverse(t), SCon{h, SNil{}}) : {SCon{h, t} == _ : String}
      %internal_reverse_reverse(t) : {SCon{h, t} == String.append(String.reverse(SCon{h, SNil{}}), _) : String}
      {==}

# Reversing twice gives the string back.
law reverse_reverse:
  for a: String
  {String.reverse(String.reverse(a)) == a : String}

def reverse_reverse(a):
  Equal.sym(String, a, String.reverse(String.reverse(a)), internal_reverse_reverse(a))

def internal_word_cmp_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{ab, at}:
          %internal_word_cmp_refl(p, at) : {EQ{} == Word.cmp.fin(ab, ab, _) : Cmp}
          %Equal.sym(Cmp, Bool.cmp(ab, ab), EQ{}, MBool.cmp_refl(ab)) : {EQ{} == _ : Cmp}
          {==}

def internal_u32_cmp_refl(x: U32) -> {EQ{} == U32.cmp(x, x) : Cmp}:
  match x:
    case U32{w}:
      %internal_word_cmp_refl(32n, w) : {EQ{} == _ : Cmp}
      {==}

# Comparing a U32 with itself gives EQ.
law u32_cmp_refl:
  for x: U32
  {U32.cmp(x, x) == EQ{} : Cmp}

def u32_cmp_refl(x):
  Equal.sym(Cmp, EQ{}, U32.cmp(x, x), internal_u32_cmp_refl(x))

def internal_char_cmp_refl(c: Char) -> {((c, c), EQ{}) == Char.cmp(c, c) : (Char & Char) & Cmp}:
  match c:
    case Chr{x}:
      %internal_u32_cmp_refl(x) : {((Chr{x}, Chr{x}), EQ{}) == ((Chr{x}, Chr{x}), _) : (Char & Char) & Cmp}
      {==}

# Comparing a character with itself gives EQ and hands both back.
law char_cmp_refl:
  for c: Char
  {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}

def char_cmp_refl(c):
  Equal.sym((Char & Char) & Cmp, ((c, c), EQ{}), Char.cmp(c, c), internal_char_cmp_refl(c))

def internal_cmp_refl(s: String) -> {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %internal_u32_cmp_refl(x) : {((SCon{Chr{x}, t}, SCon{Chr{x}, t}), EQ{}) == String.cmp.fin(t, t, ((Chr{x}, Chr{x}), _)) : (String & String) & Cmp}
          %internal_cmp_refl(t) : {((SCon{Chr{x}, t}, SCon{Chr{x}, t}), EQ{}) == String.cmp.rec(Chr{x}, Chr{x}, _) : (String & String) & Cmp}
          {==}

# Comparing a string with itself gives EQ and hands both back.
law cmp_refl:
  for s: String
  {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}

def cmp_refl(s):
  Equal.sym((String & String) & Cmp, ((s, s), EQ{}), String.cmp(s, s), internal_cmp_refl(s))

# Proofs about String.eq unfold String.order only through this (PLAN F39).
def internal_order_cmp(+a: String, +b: String) -> {Pair.snd(String & String, Cmp, String.cmp(a, b)) == String.order(a, b) : Cmp}:
  {==}

def internal_eq_true_cmp(+a: String, +b: String, h: {String.eq(a, b) == True{} : Bool}) -> {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(a, b))) == True{} : Bool}:
  %Equal.sym(Cmp, Pair.snd(String & String, Cmp, String.cmp(a, b)), String.order(a, b), internal_order_cmp(a, b)) : {Cmp.is_eq(_) == True{} : Bool}
  h

def internal_cmp_true_eq(+a: String, +b: String, h: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(a, b))) == True{} : Bool}) -> {String.eq(a, b) == True{} : Bool}:
  %internal_order_cmp(a, b) : {Cmp.is_eq(_) == True{} : Bool}
  h

# Every string is equal to itself under String.eq.
law eq_refl:
  for s: String
  {String.eq(s, s) == True{} : Bool}

def eq_refl(s):
  +s = s
  %internal_order_cmp(s, s) : {Cmp.is_eq(_) == True{} : Bool}
  %internal_cmp_refl(s) : {Cmp.is_eq(Pair.snd(String & String, Cmp, _)) == True{} : Bool}
  {==}

def internal_fin_head(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {ab == bb : Bool}:
  match c:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, internal_false_ne_true(h))
    case EQ{}:
      MBool.eq_of_cmp_eq(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, internal_false_ne_true(h))

def internal_fin_tail(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, internal_false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, internal_false_ne_true(h))

def internal_word_eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %internal_fin_head(ab, bb, Word.cmp(p, at, bt), h) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %internal_word_eq(p, at, bt, internal_fin_tail(ab, bb, Word.cmp(p, at, bt), h)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# Two U32s that U32.is_eq calls equal are equal.
law u32_eq_of_is_eq:
  for a: U32
  for b: U32
  for h: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def u32_eq_of_is_eq(a, b, h):
  match a b:
    case U32{x} U32{y}:
      %internal_word_eq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

# Two characters that Char.is_eq calls equal are equal.
law char_eq_of_is_eq:
  for a: Char
  for b: Char
  for h: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

def char_eq_of_is_eq(a, b, h):
  match a b:
    case Chr{x} Chr{y}:
      %u32_eq_of_is_eq(x, y, h) : {Chr{x} == Chr{_} : Char}
      {==}

def internal_rec_is_eq(h1: Char, h2: Char, rr: (String & String) & Cmp) -> {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, rr))) == Cmp.is_eq(Pair.snd(String & String, Cmp, rr)) : Bool}:
  match rr:
    case ((a, b), c):
      {==}

def internal_is_eq_of(c: Cmp, +d: Cmp, e: {c == d : Cmp}, h: {Cmp.is_eq(c) == True{} : Bool}) -> {Cmp.is_eq(d) == True{} : Bool}:
  %e : {Cmp.is_eq(_) == True{} : Bool}
  h

def internal_step(+x: U32, +y: U32, +t1: String, +t2: String, c: Cmp, ec: {c == U32.cmp(x, y) : Cmp}, h: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c)))) == True{} : Bool}, ih: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))) == True{} : Bool} -> {t1 == t2 : String}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, internal_false_ne_true(h))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, internal_false_ne_true(h))
    case EQ{}:
      %u32_eq_of_is_eq(x, y, internal_is_eq_of(EQ{}, U32.cmp(x, y), ec, {==})) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %ih(Equal.trans(Bool, Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))), Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2)))), True{}, Equal.sym(Bool, Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2)))), Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))), internal_rec_is_eq(Chr{x}, Chr{y}, String.cmp(t1, t2))), h)) : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# Two strings that String.eq calls equal are equal.
law eq_of_eq_true:
  for a: String
  for b: String
  for h: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def eq_of_eq_true(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{x, t}:
      Empty.absurd({SNil{} == SCon{x, t} : String}, internal_false_ne_true(h))
    case SCon{x, t} SNil{}:
      Empty.absurd({SCon{x, t} == SNil{} : String}, internal_false_ne_true(h))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      internal_step(x, y, t1, t2, U32.cmp(x, y), {==}, internal_eq_true_cmp(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}, h), hh => eq_of_eq_true(t1, t2, internal_cmp_true_eq(t1, t2, hh)))

def internal_length_reverse_go(s: String, -acc: String) -> {Nat.add(String.length(s), String.length(acc)) == String.length(String.reverse.go(s, acc)) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, +t}:
      %MNat.add_succ(String.length(t), String.length(acc)) : {_ == String.length(String.reverse.go(t, SCon{h, acc})) : Nat}
      internal_length_reverse_go(t, SCon{h, acc})

# Reversing preserves the length.
law length_reverse:
  for s: String
  {String.length(String.reverse(s)) == String.length(s) : Nat}

def length_reverse(s):
  +s = s
  Equal.trans(Nat, String.length(String.reverse(s)), Nat.add(String.length(s), 0n), String.length(s), Equal.sym(Nat, Nat.add(String.length(s), 0n), String.length(String.reverse(s)), internal_length_reverse_go(s, SNil{})), MNat.add_zero(String.length(s)))

# Reversing the empty string gives the empty string.
law reverse_nil:
  {String.reverse(SNil{}) == SNil{} : String}

def reverse_nil():
  {==}

# Reversing a one-character string gives it back.
law reverse_singleton:
  for -c: Char
  {String.reverse(SCon{c, SNil{}}) == SCon{c, SNil{}} : String}

def reverse_singleton(c):
  {==}

# A string is empty exactly when its length is zero.
law is_empty_iff_length_eq_zero:
  for s: String
  {String.is_empty(s) == Nat.is_eq(String.length(s), 0n) : Bool}

def is_empty_iff_length_eq_zero(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# An append is empty exactly when both parts are.
law is_empty_append:
  for a: String
  for -b: String
  {String.is_empty(String.append(a, b)) == Bool.and(String.is_empty(a), String.is_empty(b)) : Bool}

def is_empty_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def internal_is_empty_reverse_go(s: String, -c: Char, -acc: String) -> {String.is_empty(String.reverse.go(s, SCon{c, acc})) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      internal_is_empty_reverse_go(t, h, SCon{c, acc})

# The reverse is empty exactly when the string is.
law is_empty_reverse:
  for s: String
  {String.is_empty(String.reverse(s)) == String.is_empty(s) : Bool}

def is_empty_reverse(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      internal_is_empty_reverse_go(t, h, SNil{})

# Taking n characters and appending the rest after dropping n gives the string back.
law take_append_drop:
  for s: String
  for n: Nat
  {String.append(String.take(s, n), String.drop(s, n)) == s : String}

def take_append_drop(s, n):
  match s n:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, t} 1n+p:
      %take_append_drop(t, p) : {SCon{h, String.append(String.take(t, p), String.drop(t, p))} == SCon{h, _} : String}
      {==}

# Taking n characters leaves min(n, length) of them.
law length_take:
  for s: String
  for n: Nat
  {String.length(String.take(s, n)) == Nat.min(n, String.length(s)) : Nat}

def length_take(s, n):
  match s n:
    case SNil{} _:
      Equal.sym(Nat, Nat.min(n, 0n), 0n, MNat.min_zero(n))
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %length_take(t, p) : {1n+String.length(String.take(t, p)) == 1n+_ : Nat}
      {==}

# Dropping n characters leaves length - n of them.
law length_drop:
  for s: String
  for n: Nat
  {String.length(String.drop(s, n)) == Nat.sub(String.length(s), n) : Nat}

def length_drop(s, n):
  match s n:
    case SNil{} _:
      Equal.sym(Nat, Nat.sub(0n, n), 0n, MNat.zero_sub(n))
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      length_drop(t, p)

# Converting a character list to a string and back gives the list.
law to_list_from_list:
  for cs: List<&2, Char>
  {String.to_list(String.from_list(cs)) == cs : List<&2, Char>}

def to_list_from_list(cs):
  match cs:
    case Nil{}:
      {==}
    case +h <> t:
      %to_list_from_list(t) : {h <> String.to_list(String.from_list(t)) == h <> _ : List<&2, Char>}
      {==}

# Converting a string to a character list and back gives the string.
law from_list_to_list:
  for s: String
  {String.from_list(String.to_list(s)) == s : String}

def from_list_to_list(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %from_list_to_list(t) : {SCon{h, String.from_list(String.to_list(t))} == SCon{h, _} : String}
      {==}

# The characters of an append are the characters of each part, appended.
law to_list_append:
  for a: String
  for -b: String
  {String.to_list(String.append(a, b)) == List.append(&2, Char, String.to_list(a), String.to_list(b)) : List<&2, Char>}

def to_list_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %to_list_append(t, b) : {h <> String.to_list(String.append(t, b)) == h <> _ : List<&2, Char>}
      {==}

# A string has as many characters as its character list.
law length_to_list:
  for s: String
  {List.length(&2, Char, String.to_list(s)) == String.length(s) : Nat}

def length_to_list(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %length_to_list(t) : {1n+List.length(&2, Char, String.to_list(t)) == 1n+_ : Nat}
      {==}

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# The empty string is a right identity for append: a ++ "" = a, reversed to rewrite toward the simple side.
law append_nil_sym:
  for a: String
  {a == String.append(a, SNil{}) : String}

def append_nil_sym(a):
  Equal.sym(String, String.append(a, SNil{}), a, append_nil(a))

# The empty string is a left identity for append: "" ++ a = a, reversed to rewrite toward the simple side.
law nil_append_sym:
  for -a: String
  {a == String.append(SNil{}, a) : String}

def nil_append_sym(a):
  Equal.sym(String, String.append(SNil{}, a), a, nil_append(a))

# Append is associative: (a ++ b) ++ c = a ++ (b ++ c), reversed to rewrite toward the simple side.
law append_assoc_sym:
  for a: String
  for -b: String
  for -c: String
  {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}

def append_assoc_sym(a, b, c):
  Equal.sym(String, String.append(String.append(a, b), c), String.append(a, String.append(b, c)), append_assoc(a, b, c))

# The length of an append is the sum of the lengths, reversed to rewrite toward the simple side.
law length_append_sym:
  for a: String
  for -b: String
  {Nat.add(String.length(a), String.length(b)) == String.length(String.append(a, b)) : Nat}

def length_append_sym(a, b):
  Equal.sym(Nat, String.length(String.append(a, b)), Nat.add(String.length(a), String.length(b)), length_append(a, b))

# The reverse accumulator loop appends the reversed string to the accumulator, reversed to rewrite toward the simple side.
law reverse_go_spec_sym:
  for s: String
  for acc: String
  {String.append(String.reverse(s), acc) == String.reverse.go(s, acc) : String}

def reverse_go_spec_sym(s, acc):
  Equal.sym(String, String.reverse.go(s, acc), String.append(String.reverse(s), acc), reverse_go_spec(s, acc))

# Reversing an append reverses and swaps the parts: reverse (a ++ b) = reverse b ++ reverse a, reversed to rewrite toward the simple side.
law reverse_append_sym:
  for a: String
  for b: String
  {String.append(String.reverse(b), String.reverse(a)) == String.reverse(String.append(a, b)) : String}

def reverse_append_sym(a, b):
  Equal.sym(String, String.reverse(String.append(a, b)), String.append(String.reverse(b), String.reverse(a)), reverse_append(a, b))

# Reversing twice gives the string back, reversed to rewrite toward the simple side.
law reverse_reverse_sym:
  for a: String
  {a == String.reverse(String.reverse(a)) : String}

def reverse_reverse_sym(a):
  Equal.sym(String, String.reverse(String.reverse(a)), a, reverse_reverse(a))

# Comparing a U32 with itself gives EQ, reversed to rewrite toward the simple side.
law u32_cmp_refl_sym:
  for x: U32
  {EQ{} == U32.cmp(x, x) : Cmp}

def u32_cmp_refl_sym(x):
  Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_cmp_refl(x))

# Comparing a character with itself gives EQ and hands both back, reversed to rewrite toward the simple side.
law char_cmp_refl_sym:
  for c: Char
  {((c, c), EQ{}) == Char.cmp(c, c) : (Char & Char) & Cmp}

def char_cmp_refl_sym(c):
  Equal.sym((Char & Char) & Cmp, Char.cmp(c, c), ((c, c), EQ{}), char_cmp_refl(c))

# Comparing a string with itself gives EQ and hands both back, reversed to rewrite toward the simple side.
law cmp_refl_sym:
  for s: String
  {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}

def cmp_refl_sym(s):
  Equal.sym((String & String) & Cmp, String.cmp(s, s), ((s, s), EQ{}), cmp_refl(s))

# Every string is equal to itself under String.eq, reversed to rewrite toward the simple side.
law eq_refl_sym:
  for s: String
  {True{} == String.eq(s, s) : Bool}

def eq_refl_sym(s):
  Equal.sym(Bool, String.eq(s, s), True{}, eq_refl(s))

# Reversing preserves the length, reversed to rewrite toward the simple side.
law length_reverse_sym:
  for s: String
  {String.length(s) == String.length(String.reverse(s)) : Nat}

def length_reverse_sym(s):
  Equal.sym(Nat, String.length(String.reverse(s)), String.length(s), length_reverse(s))

# Reversing the empty string gives the empty string, reversed to rewrite toward the simple side.
law reverse_nil_sym:
  {SNil{} == String.reverse(SNil{}) : String}

def reverse_nil_sym():
  Equal.sym(String, String.reverse(SNil{}), SNil{}, reverse_nil())

# Reversing a one-character string gives it back, reversed to rewrite toward the simple side.
law reverse_singleton_sym:
  for -c: Char
  {SCon{c, SNil{}} == String.reverse(SCon{c, SNil{}}) : String}

def reverse_singleton_sym(c):
  Equal.sym(String, String.reverse(SCon{c, SNil{}}), SCon{c, SNil{}}, reverse_singleton(c))

# A string is empty exactly when its length is zero, reversed to rewrite toward the simple side.
law is_empty_iff_length_eq_zero_sym:
  for s: String
  {Nat.is_eq(String.length(s), 0n) == String.is_empty(s) : Bool}

def is_empty_iff_length_eq_zero_sym(s):
  Equal.sym(Bool, String.is_empty(s), Nat.is_eq(String.length(s), 0n), is_empty_iff_length_eq_zero(s))

# An append is empty exactly when both parts are, reversed to rewrite toward the simple side.
law is_empty_append_sym:
  for a: String
  for -b: String
  {Bool.and(String.is_empty(a), String.is_empty(b)) == String.is_empty(String.append(a, b)) : Bool}

def is_empty_append_sym(a, b):
  Equal.sym(Bool, String.is_empty(String.append(a, b)), Bool.and(String.is_empty(a), String.is_empty(b)), is_empty_append(a, b))

# The reverse is empty exactly when the string is, reversed to rewrite toward the simple side.
law is_empty_reverse_sym:
  for s: String
  {String.is_empty(s) == String.is_empty(String.reverse(s)) : Bool}

def is_empty_reverse_sym(s):
  Equal.sym(Bool, String.is_empty(String.reverse(s)), String.is_empty(s), is_empty_reverse(s))

# Taking n characters and appending the rest after dropping n gives the string back, reversed to rewrite toward the simple side.
law take_append_drop_sym:
  for s: String
  for n: Nat
  {s == String.append(String.take(s, n), String.drop(s, n)) : String}

def take_append_drop_sym(s, n):
  Equal.sym(String, String.append(String.take(s, n), String.drop(s, n)), s, take_append_drop(s, n))

# Taking n characters leaves min(n, length) of them, reversed to rewrite toward the simple side.
law length_take_sym:
  for s: String
  for n: Nat
  {Nat.min(n, String.length(s)) == String.length(String.take(s, n)) : Nat}

def length_take_sym(s, n):
  Equal.sym(Nat, String.length(String.take(s, n)), Nat.min(n, String.length(s)), length_take(s, n))

# Dropping n characters leaves length - n of them, reversed to rewrite toward the simple side.
law length_drop_sym:
  for s: String
  for n: Nat
  {Nat.sub(String.length(s), n) == String.length(String.drop(s, n)) : Nat}

def length_drop_sym(s, n):
  Equal.sym(Nat, String.length(String.drop(s, n)), Nat.sub(String.length(s), n), length_drop(s, n))

# Converting a character list to a string and back gives the list, reversed to rewrite toward the simple side.
law to_list_from_list_sym:
  for cs: List<&2, Char>
  {cs == String.to_list(String.from_list(cs)) : List<&2, Char>}

def to_list_from_list_sym(cs):
  Equal.sym(List<&2, Char>, String.to_list(String.from_list(cs)), cs, to_list_from_list(cs))

# Converting a string to a character list and back gives the string, reversed to rewrite toward the simple side.
law from_list_to_list_sym:
  for s: String
  {s == String.from_list(String.to_list(s)) : String}

def from_list_to_list_sym(s):
  Equal.sym(String, String.from_list(String.to_list(s)), s, from_list_to_list(s))

# The characters of an append are the characters of each part, appended, reversed to rewrite toward the simple side.
law to_list_append_sym:
  for a: String
  for -b: String
  {List.append(&2, Char, String.to_list(a), String.to_list(b)) == String.to_list(String.append(a, b)) : List<&2, Char>}

def to_list_append_sym(a, b):
  Equal.sym(List<&2, Char>, String.to_list(String.append(a, b)), List.append(&2, Char, String.to_list(a), String.to_list(b)), to_list_append(a, b))

# A string has as many characters as its character list, reversed to rewrite toward the simple side.
law length_to_list_sym:
  for s: String
  {String.length(s) == List.length(&2, Char, String.to_list(s)) : Nat}

def length_to_list_sym(s):
  Equal.sym(Nat, List.length(&2, Char, String.to_list(s)), String.length(s), length_to_list(s))
