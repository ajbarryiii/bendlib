import Base
import ./sub.bend as Sub

type Box is Data:
  Box{value: Nat}

def own_le(x: Nat, y: Nat) -> Bool:
  Nat.is_le(x, y)

# A kernel predicate that matches and calls its own defs.
def kernel_pred(+xs: List<&2, Nat>) -> Data:
  match xs:
    case Nil{}:
      {True{} == True{} : Bool}
    case h <> t:
      {Bool.and(own_le(h, List.length(&2, Nat, t)), Sub.sub_le(h, List.length(&2, Nat, t))) == True{} : Bool}
