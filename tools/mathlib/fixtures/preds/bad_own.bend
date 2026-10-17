import Base

def own_helper(x: Nat) -> Bool:
  Nat.is_le(x, 0n)

# Every element passes an own helper.
def bad_own(+xs: List<&2, Nat>) -> Data:
  {List.all(~&2, ~Nat, ~own_helper, xs) == True{} : Bool}
