import Base
import ../../../../packages/bend-mathlib/nat.bend as MNat

# Every element passes a def of another module.
def bad_ref(+xs: List<&2, Nat>) -> Data:
  {List.all(~&2, ~Nat, ~MNat.le, xs) == True{} : Bool}
