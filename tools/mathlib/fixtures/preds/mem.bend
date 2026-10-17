import Base

# x occurs in xs under eq.
def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}
