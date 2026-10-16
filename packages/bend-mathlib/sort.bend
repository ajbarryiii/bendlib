# bend-mathlib/sort.bend: insertion and merge sort proved sorted over perm.bend's value defs (generic ~le).
import Base
import ./nat.bend as MNat
import ./list.bend as MList
import ./perm.bend as MPerm

def internal_sorted_single(~A: Data, ~le: A -> A -> Bool, +x: A) -> MList.sorted_by(~A, ~le, x <> Nil{}):
  {==}

def internal_sorted_cons_cons_intro(~A: Data, ~le: A -> A -> Bool, +x: A, +y: A, +t: List<&2, A>, hxy: {le(x, y) == True{} : Bool}, hyt: MList.sorted_by(~A, ~le, y <> t)) -> MList.sorted_by(~A, ~le, x <> y <> t):
  %MList.internal_sorted_cons_true(~A, ~le, x, y, List.zip(&2, A, &2, A, y <> t, t), hxy) : {_ == True{} : Bool}
  hyt

def internal_sorted_le_step(~A: Data, ~le: A -> A -> Bool, -x: A, +y: A, +t: List<&2, A>, b: Bool, e: {le(x, y) == b : Bool}, h: MList.sorted_by(~A, ~le, x <> y <> t)) -> {le(x, y) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({le(x, y) == True{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), (x, y) <> List.zip(&2, A, &2, A, y <> t, t)), True{}, MList.internal_sorted_cons_false(~A, ~le, x, y, List.zip(&2, A, &2, A, y <> t, t), e), h)))

def internal_sorted_tail_step(~A: Data, ~le: A -> A -> Bool, -x: A, +y: A, +t: List<&2, A>, b: Bool, e: {le(x, y) == b : Bool}, h: MList.sorted_by(~A, ~le, x <> y <> t)) -> MList.sorted_by(~A, ~le, y <> t):
  match b:
    case True{}:
      Equal.trans(Bool, List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, y <> t, t)), List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), (x, y) <> List.zip(&2, A, &2, A, y <> t, t)), True{}, MList.internal_sorted_cons_true(~A, ~le, x, y, List.zip(&2, A, &2, A, y <> t, t), e), h)
    case False{}:
      Empty.absurd(MList.sorted_by(~A, ~le, y <> t), MNat.internal_false_ne_true(Equal.trans(Bool, False{}, List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), (x, y) <> List.zip(&2, A, &2, A, y <> t, t)), True{}, MList.internal_sorted_cons_false(~A, ~le, x, y, List.zip(&2, A, &2, A, y <> t, t), e), h)))

def internal_sorted_cons_cons_elim_le(~A: Data, ~le: A -> A -> Bool, +x: A, +y: A, +t: List<&2, A>, h: MList.sorted_by(~A, ~le, x <> y <> t)) -> {le(x, y) == True{} : Bool}:
  internal_sorted_le_step(~A, ~le, x, y, t, le(x, y), {==}, h)

def internal_sorted_cons_cons_elim_tail(~A: Data, ~le: A -> A -> Bool, +x: A, +y: A, +t: List<&2, A>, h: MList.sorted_by(~A, ~le, x <> y <> t)) -> MList.sorted_by(~A, ~le, y <> t):
  internal_sorted_tail_step(~A, ~le, x, y, t, le(x, y), {==}, h)

def internal_sorted_tail(~A: Data, ~le: A -> A -> Bool, +x: A, +xs: List<&2, A>, h: MList.sorted_by(~A, ~le, x <> xs)) -> MList.sorted_by(~A, ~le, xs):
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      internal_sorted_cons_cons_elim_tail(~A, ~le, x, y, t, h)

def internal_le_flip_nat(x: Nat, y: Nat, e: {Nat.is_le(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({True{} == True{} : Bool}, MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, e)))
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, e)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      internal_le_flip_nat(p, q, e)

def internal_le_trans_nat(x: Nat, y: Nat, z: Nat, xy: {Nat.is_le(x, y) == True{} : Bool}, yz: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  MNat.le_trans(x, y, z, xy, yz)

def internal_cons_ins_step(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, b: Bool, +y: A, +x: A, +z: A, +u: List<&2, A>, e: {le(x, z) == b : Bool}, hyx: {le(y, x) == True{} : Bool}, +h: MList.sorted_by(~A, ~le, y <> z <> u), k: {le(z, x) == True{} : Bool} -> MList.sorted_by(~A, ~le, z <> MPerm.insert_by(~A, ~le, x, u))) -> MList.sorted_by(~A, ~le, y <> Bool.pick(List<&2, A>, b, x <> z <> u, z <> MPerm.insert_by(~A, ~le, x, u))):
  match b:
    case True{}:
      internal_sorted_cons_cons_intro(~A, ~le, y, x, z <> u, hyx, internal_sorted_cons_cons_intro(~A, ~le, x, z, u, e, internal_sorted_cons_cons_elim_tail(~A, ~le, y, z, u, h)))
    case False{}:
      internal_sorted_cons_cons_intro(~A, ~le, y, z, MPerm.insert_by(~A, ~le, x, u), internal_sorted_cons_cons_elim_le(~A, ~le, y, z, u, h), k(le_total(x, z, e)))

def internal_sorted_cons_ins(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +t: List<&2, A>, +y: A, +x: A, hyx: {le(y, x) == True{} : Bool}, +h: MList.sorted_by(~A, ~le, y <> t)) -> MList.sorted_by(~A, ~le, y <> MPerm.insert_by(~A, ~le, x, t)):
  match t:
    case Nil{}:
      internal_sorted_cons_cons_intro(~A, ~le, y, x, Nil{}, hyx, internal_sorted_single(~A, ~le, x))
    case +z <> +u:
      internal_cons_ins_step(~A, ~le, ~le_total, le(x, z), y, x, z, u, {==}, hyx, h, hzx => internal_sorted_cons_ins(~A, ~le, ~le_total, u, z, x, hzx, internal_sorted_cons_cons_elim_tail(~A, ~le, y, z, u, h)))

def internal_insert_step(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, b: Bool, +x: A, +y: A, +t: List<&2, A>, e: {le(x, y) == b : Bool}, +h: MList.sorted_by(~A, ~le, y <> t)) -> MList.sorted_by(~A, ~le, Bool.pick(List<&2, A>, b, x <> y <> t, y <> MPerm.insert_by(~A, ~le, x, t))):
  match b:
    case True{}:
      internal_sorted_cons_cons_intro(~A, ~le, x, y, t, e, h)
    case False{}:
      internal_sorted_cons_ins(~A, ~le, ~le_total, t, y, x, le_total(x, y, e), h)

# Inserting into a sorted list keeps it sorted, for a total comparator.
def insert_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +x: A, +xs: List<&2, A>, +h: MList.sorted_by(~A, ~le, xs)) -> MList.sorted_by(~A, ~le, MPerm.insert_by(~A, ~le, x, xs)):
  match xs:
    case Nil{}:
      internal_sorted_single(~A, ~le, x)
    case +y <> t:
      internal_insert_step(~A, ~le, ~le_total, le(x, y), x, y, t, {==}, h)

# Insertion sort returns a sorted list.
def isort_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +xs: List<&2, A>) -> MList.sorted_by(~A, ~le, MPerm.isort_by(~A, ~le, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      insert_by_sorted(~A, ~le, ~le_total, x, MPerm.isort_by(~A, ~le, t), isort_by_sorted(~A, ~le, ~le_total, t))

# Insertion sort returns a sorted Nat list.
def isort_by_sorted_nat(+xs: List<&2, Nat>) -> MList.sorted_by(~Nat, ~Nat.is_le, MPerm.isort_by(~Nat, ~Nat.is_le, xs)):
  isort_by_sorted(~Nat, ~Nat.is_le, ~internal_le_flip_nat, xs)

# A recursion, not List.all with a lambda over lo, which --verdict cannot translate (PLAN F38).
def internal_all_ge(~A: Data, ~le: A -> A -> Bool, +lo: A, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(le(lo, h), internal_all_ge(~A, ~le, lo, t))

def internal_least(~A: Data, ~le: A -> A -> Bool, +lo: A, +xs: List<&2, A>) -> Data:
  {internal_all_ge(~A, ~le, lo, xs) == True{} : Bool}

def internal_least_intro(~A: Data, ~le: A -> A -> Bool, +lo: A, +h: A, +t: List<&2, A>, hh: {le(lo, h) == True{} : Bool}, ht: internal_least(~A, ~le, lo, t)) -> internal_least(~A, ~le, lo, h <> t):
  %Equal.sym(Bool, le(lo, h), True{}, hh) : {Bool.and(_, internal_all_ge(~A, ~le, lo, t)) == True{} : Bool}
  ht

def internal_least_cons_le(~A: Data, ~le: A -> A -> Bool, +lo: A, +h: A, +t: List<&2, A>, hh: internal_least(~A, ~le, lo, h <> t)) -> {le(lo, h) == True{} : Bool}:
  MList.internal_and_left(le(lo, h), internal_all_ge(~A, ~le, lo, t), hh)

def internal_least_cons_tail(~A: Data, ~le: A -> A -> Bool, +lo: A, +h: A, +t: List<&2, A>, hh: internal_least(~A, ~le, lo, h <> t)) -> internal_least(~A, ~le, lo, t):
  MList.internal_and_right(le(lo, h), internal_all_ge(~A, ~le, lo, t), hh)

def internal_least_trans(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +b: A, +xs: List<&2, A>, +hab: {le(a, b) == True{} : Bool}, +hb: internal_least(~A, ~le, b, xs)) -> internal_least(~A, ~le, a, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      internal_least_intro(~A, ~le, a, h, t, le_trans(a, b, h, hab, internal_least_cons_le(~A, ~le, b, h, t, hb)), internal_least_trans(~A, ~le, ~le_trans, a, b, t, hab, internal_least_cons_tail(~A, ~le, b, h, t, hb)))

def internal_sorted_least_head(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +x: A, +h: MList.sorted_by(~A, ~le, x <> xs)) -> internal_least(~A, ~le, x, xs):
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      internal_least_intro(~A, ~le, x, y, t, internal_sorted_cons_cons_elim_le(~A, ~le, x, y, t, h), internal_least_trans(~A, ~le, ~le_trans, x, y, t, internal_sorted_cons_cons_elim_le(~A, ~le, x, y, t, h), internal_sorted_least_head(~A, ~le, ~le_trans, t, y, internal_sorted_cons_cons_elim_tail(~A, ~le, x, y, t, h))))

def internal_sorted_cons_of_least(~A: Data, ~le: A -> A -> Bool, +lo: A, +m: List<&2, A>, hl: internal_least(~A, ~le, lo, m), hm: MList.sorted_by(~A, ~le, m)) -> MList.sorted_by(~A, ~le, lo <> m):
  match m:
    case Nil{}:
      {==}
    case +z <> +t:
      internal_sorted_cons_cons_intro(~A, ~le, lo, z, t, internal_least_cons_le(~A, ~le, lo, z, t, hl), hm)

def internal_least_merge_pick(~A: Data, ~le: A -> A -> Bool, +lo: A, b: Bool, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, hx: internal_least(~A, ~le, lo, x <> xt), hy: internal_least(~A, ~le, lo, y <> yt), hm1: internal_least(~A, ~le, lo, MPerm.merge_by(~A, ~le, xt, y <> yt)), hm2: internal_least(~A, ~le, lo, MPerm.merge_by(~A, ~le, x <> xt, yt))) -> internal_least(~A, ~le, lo, Bool.pick(List<&2, A>, b, x <> MPerm.merge_by(~A, ~le, xt, y <> yt), y <> MPerm.merge_by(~A, ~le, x <> xt, yt))):
  match b:
    case True{}:
      internal_least_intro(~A, ~le, lo, x, MPerm.merge_by(~A, ~le, xt, y <> yt), internal_least_cons_le(~A, ~le, lo, x, xt, hx), hm1)
    case False{}:
      internal_least_intro(~A, ~le, lo, y, MPerm.merge_by(~A, ~le, x <> xt, yt), internal_least_cons_le(~A, ~le, lo, y, yt, hy), hm2)

def internal_least_merge(~A: Data, ~le: A -> A -> Bool, +lo: A, +xs: List<&2, A>, +ys: List<&2, A>, +hx: internal_least(~A, ~le, lo, xs), +hy: internal_least(~A, ~le, lo, ys)) -> internal_least(~A, ~le, lo, MPerm.merge_by(~A, ~le, xs, ys)):
  match xs ys:
    case Nil{} _:
      hy
    case +x <> +xt Nil{}:
      hx
    case +x <> +xt +y <> +yt:
      internal_least_merge_pick(~A, ~le, lo, le(x, y), x, xt, y, yt, hx, hy, internal_least_merge(~A, ~le, lo, xt, y <> yt, internal_least_cons_tail(~A, ~le, lo, x, xt, hx), hy), internal_least_merge(~A, ~le, lo, x <> xt, yt, hx, internal_least_cons_tail(~A, ~le, lo, y, yt, hy)))

def internal_merge_sorted_pick(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, b: Bool, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, +e: {le(x, y) == b : Bool}, hx: MList.sorted_by(~A, ~le, x <> xt), hy: MList.sorted_by(~A, ~le, y <> yt), hm1: MList.sorted_by(~A, ~le, MPerm.merge_by(~A, ~le, xt, y <> yt)), hm2: MList.sorted_by(~A, ~le, MPerm.merge_by(~A, ~le, x <> xt, yt))) -> MList.sorted_by(~A, ~le, Bool.pick(List<&2, A>, b, x <> MPerm.merge_by(~A, ~le, xt, y <> yt), y <> MPerm.merge_by(~A, ~le, x <> xt, yt))):
  match b:
    case True{}:
      internal_sorted_cons_of_least(~A, ~le, x, MPerm.merge_by(~A, ~le, xt, y <> yt), internal_least_merge(~A, ~le, x, xt, y <> yt, internal_sorted_least_head(~A, ~le, ~le_trans, xt, x, hx), internal_least_intro(~A, ~le, x, y, yt, e, internal_least_trans(~A, ~le, ~le_trans, x, y, yt, e, internal_sorted_least_head(~A, ~le, ~le_trans, yt, y, hy)))), hm1)
    case False{}:
      internal_sorted_cons_of_least(~A, ~le, y, MPerm.merge_by(~A, ~le, x <> xt, yt), internal_least_merge(~A, ~le, y, x <> xt, yt, internal_least_intro(~A, ~le, y, x, xt, le_total(x, y, e), internal_least_trans(~A, ~le, ~le_trans, y, x, xt, le_total(x, y, e), internal_sorted_least_head(~A, ~le, ~le_trans, xt, x, hx))), internal_sorted_least_head(~A, ~le, ~le_trans, yt, y, hy)), hm2)

# Merging two sorted lists is sorted (needs transitivity, and totality for the un-taken branch).
def merge_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +xs: List<&2, A>, +ys: List<&2, A>, +hx: MList.sorted_by(~A, ~le, xs), +hy: MList.sorted_by(~A, ~le, ys)) -> MList.sorted_by(~A, ~le, MPerm.merge_by(~A, ~le, xs, ys)):
  match xs ys:
    case Nil{} _:
      hy
    case +x <> +xt Nil{}:
      hx
    case +x <> +xt +y <> +yt:
      internal_merge_sorted_pick(~A, ~le, ~le_trans, ~le_total, le(x, y), x, xt, y, yt, {==}, hx, hy, merge_by_sorted(~A, ~le, ~le_trans, ~le_total, xt, y <> yt, internal_sorted_tail(~A, ~le, x, xt, hx), hy), merge_by_sorted(~A, ~le, ~le_trans, ~le_total, x <> xt, yt, hx, internal_sorted_tail(~A, ~le, y, yt, hy)))

# Merging two sorted Nat lists gives a sorted list.
def merge_by_sorted_nat(+xs: List<&2, Nat>, +ys: List<&2, Nat>, hx: MList.sorted_by(~Nat, ~Nat.is_le, xs), hy: MList.sorted_by(~Nat, ~Nat.is_le, ys)) -> MList.sorted_by(~Nat, ~Nat.is_le, MPerm.merge_by(~Nat, ~Nat.is_le, xs, ys)):
  merge_by_sorted(~Nat, ~Nat.is_le, ~internal_le_trans_nat, ~internal_le_flip_nat, xs, ys, hx, hy)

def internal_length_zero(~A: Data, +xs: List<&2, A>, e: {List.length(&2, A, xs) == 0n : Nat}) -> {xs == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Empty.absurd({x <> t == Nil{} : List<&2, A>}, MNat.zero_ne_succ(List.length(&2, A, t), Equal.sym(Nat, List.length(&2, A, x <> t), 0n, e)))

def internal_sorted_short(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, h: MNat.le(List.length(&2, A, xs), 1n)) -> MList.sorted_by(~A, ~le, xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match t:
        case Nil{}:
          internal_sorted_single(~A, ~le, x)
        case +y <> +u:
          %Equal.sym(List<&2, A>, t, Nil{}, internal_length_zero(~A, t, MNat.le_zero_eq(List.length(&2, A, t), MNat.le_of_succ_le_succ(List.length(&2, A, t), 0n, h)))) : {MList.sorted_by(~A, ~le, x <> _) : Data}
          internal_sorted_single(~A, ~le, x)

def internal_length_evens_le(~A: Data, +xs: List<&2, A>) -> {Nat.is_le(List.length(&2, A, MPerm.evens(A, xs)), List.length(&2, A, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match r:
        case Nil{}:
          {==}
        case +y <> +t:
          MNat.succ_le_succ(List.length(&2, A, MPerm.evens(A, t)), 1n+List.length(&2, A, t), MNat.le_trans(List.length(&2, A, MPerm.evens(A, t)), List.length(&2, A, t), 1n+List.length(&2, A, t), internal_length_evens_le(~A, t), MNat.le_succ(List.length(&2, A, t))))

def internal_length_odds_le(~A: Data, +xs: List<&2, A>) -> {Nat.is_le(List.length(&2, A, MPerm.odds(A, xs)), List.length(&2, A, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match r:
        case Nil{}:
          {==}
        case +y <> +t:
          MNat.succ_le_succ(List.length(&2, A, MPerm.odds(A, t)), 1n+List.length(&2, A, t), MNat.le_trans(List.length(&2, A, MPerm.odds(A, t)), List.length(&2, A, t), 1n+List.length(&2, A, t), internal_length_odds_le(~A, t), MNat.le_succ(List.length(&2, A, t))))

def internal_least_evens(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +lo: A, +h: internal_least(~A, ~le, lo, xs)) -> internal_least(~A, ~le, lo, MPerm.evens(A, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match r:
        case Nil{}:
          h
        case +y <> +t:
          internal_least_intro(~A, ~le, lo, x, MPerm.evens(A, t), internal_least_cons_le(~A, ~le, lo, x, r, h), internal_least_evens(~A, ~le, t, lo, internal_least_cons_tail(~A, ~le, lo, y, t, internal_least_cons_tail(~A, ~le, lo, x, r, h))))

def internal_least_odds(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +lo: A, +h: internal_least(~A, ~le, lo, xs)) -> internal_least(~A, ~le, lo, MPerm.odds(A, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match r:
        case Nil{}:
          {==}
        case +y <> +t:
          internal_least_intro(~A, ~le, lo, y, MPerm.odds(A, t), internal_least_cons_le(~A, ~le, lo, y, t, internal_least_cons_tail(~A, ~le, lo, x, r, h)), internal_least_odds(~A, ~le, t, lo, internal_least_cons_tail(~A, ~le, lo, y, t, internal_least_cons_tail(~A, ~le, lo, x, r, h))))

def internal_evens_sorted(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +h: MList.sorted_by(~A, ~le, xs)) -> MList.sorted_by(~A, ~le, MPerm.evens(A, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match r:
        case Nil{}:
          h
        case +y <> +t:
          internal_sorted_cons_of_least(~A, ~le, x, MPerm.evens(A, t), internal_least_evens(~A, ~le, t, x, internal_least_cons_tail(~A, ~le, x, y, t, internal_sorted_least_head(~A, ~le, ~le_trans, y <> t, x, h))), internal_evens_sorted(~A, ~le, ~le_trans, t, internal_sorted_tail(~A, ~le, y, t, internal_sorted_cons_cons_elim_tail(~A, ~le, x, y, t, h))))

def internal_odds_sorted(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +h: MList.sorted_by(~A, ~le, xs)) -> MList.sorted_by(~A, ~le, MPerm.odds(A, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match r:
        case Nil{}:
          {==}
        case +y <> +t:
          internal_sorted_cons_of_least(~A, ~le, y, MPerm.odds(A, t), internal_least_odds(~A, ~le, t, y, internal_sorted_least_head(~A, ~le, ~le_trans, t, y, internal_sorted_cons_cons_elim_tail(~A, ~le, x, y, t, h))), internal_odds_sorted(~A, ~le, ~le_trans, t, internal_sorted_tail(~A, ~le, y, t, internal_sorted_cons_cons_elim_tail(~A, ~le, x, y, t, h))))

# Merge sort returns a sorted list once the fuel reaches the input length (invariant: length <= fuel+1).
def msort_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, fuel: Nat, +xs: List<&2, A>, +h: {Nat.is_le(List.length(&2, A, xs), 1n+fuel) == True{} : Bool}) -> MList.sorted_by(~A, ~le, MPerm.msort_by(~A, ~le, fuel, xs)):
  match fuel:
    case 0n:
      internal_sorted_short(~A, ~le, xs, h)
    case 1n++f:
      match xs:
        case Nil{}:
          merge_by_sorted(~A, ~le, ~le_trans, ~le_total, MPerm.msort_by(~A, ~le, f, MPerm.evens(A, xs)), MPerm.msort_by(~A, ~le, f, MPerm.odds(A, xs)), msort_by_sorted(~A, ~le, ~le_trans, ~le_total, f, MPerm.evens(A, xs), MNat.zero_le(1n+f)), msort_by_sorted(~A, ~le, ~le_trans, ~le_total, f, MPerm.odds(A, xs), MNat.zero_le(1n+f)))
        case +x <> +r:
          match r:
            case Nil{}:
              merge_by_sorted(~A, ~le, ~le_trans, ~le_total, MPerm.msort_by(~A, ~le, f, MPerm.evens(A, x <> r)), MPerm.msort_by(~A, ~le, f, MPerm.odds(A, x <> r)), msort_by_sorted(~A, ~le, ~le_trans, ~le_total, f, MPerm.evens(A, x <> r), MNat.le_add_right(1n, f)), msort_by_sorted(~A, ~le, ~le_trans, ~le_total, f, MPerm.odds(A, x <> r), MNat.zero_le(1n+f)))
            case +y <> +t:
              merge_by_sorted(~A, ~le, ~le_trans, ~le_total, MPerm.msort_by(~A, ~le, f, MPerm.evens(A, x <> y <> t)), MPerm.msort_by(~A, ~le, f, MPerm.odds(A, x <> y <> t)), msort_by_sorted(~A, ~le, ~le_trans, ~le_total, f, MPerm.evens(A, x <> y <> t), MNat.succ_le_succ(List.length(&2, A, MPerm.evens(A, t)), f, MNat.le_trans(List.length(&2, A, MPerm.evens(A, t)), List.length(&2, A, t), f, internal_length_evens_le(~A, t), MNat.le_of_succ_le_succ(List.length(&2, A, t), f, MNat.le_of_succ_le_succ(1n+List.length(&2, A, t), 1n+f, h))))), msort_by_sorted(~A, ~le, ~le_trans, ~le_total, f, MPerm.odds(A, x <> y <> t), MNat.succ_le_succ(List.length(&2, A, MPerm.odds(A, t)), f, MNat.le_trans(List.length(&2, A, MPerm.odds(A, t)), List.length(&2, A, t), f, internal_length_odds_le(~A, t), MNat.le_of_succ_le_succ(List.length(&2, A, t), f, MNat.le_of_succ_le_succ(1n+List.length(&2, A, t), 1n+f, h))))))

# Merge sort of the full-length fuel sorts its input.
def sort_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +xs: List<&2, A>) -> MList.sorted_by(~A, ~le, MPerm.sort_by(~A, ~le, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      msort_by_sorted(~A, ~le, ~le_trans, ~le_total, 1n+List.length(&2, A, t), x <> t, MNat.le_succ(1n+List.length(&2, A, t)))

# Merge sort with fuel = length returns a sorted Nat list (h always holds; sort_by_sorted_nat needs no h).
def msort_by_sorted_nat(+xs: List<&2, Nat>, +h: {Nat.is_le(List.length(&2, Nat, xs), 1n+List.length(&2, Nat, xs)) == True{} : Bool}) -> MList.sorted_by(~Nat, ~Nat.is_le, MPerm.msort_by(~Nat, ~Nat.is_le, List.length(&2, Nat, xs), xs)):
  msort_by_sorted(~Nat, ~Nat.is_le, ~internal_le_trans_nat, ~internal_le_flip_nat, List.length(&2, Nat, xs), xs, h)

# Merge sort returns a sorted Nat list.
def sort_by_sorted_nat(+xs: List<&2, Nat>) -> MList.sorted_by(~Nat, ~Nat.is_le, MPerm.sort_by(~Nat, ~Nat.is_le, xs)):
  sort_by_sorted(~Nat, ~Nat.is_le, ~internal_le_trans_nat, ~internal_le_flip_nat, xs)
