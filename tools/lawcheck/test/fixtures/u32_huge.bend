import Base

law to_nat_le_self:
  for a: U32
  {Nat.is_le(U32.to_nat(a), U32.to_nat(a)) == True{} : Bool}
