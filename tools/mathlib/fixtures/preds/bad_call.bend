import Base

def helper(x: Nat) -> Bool:
  Nat.is_le(x, 0n)

# Every length passes a non-Base helper.
def bad_call(+xs: List<&2, Nat>) -> Data:
  {helper(List.length(&2, Nat, xs)) == True{} : Bool}
