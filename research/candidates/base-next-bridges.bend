# Proofs of string.bend's String.order bridge lemmas for Base after 2.0.37 (PLAN F39), checked at bend e5527d5.
# They replace the {==} body of internal_order_cmp when the pin moves past #1459.
import Base

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
