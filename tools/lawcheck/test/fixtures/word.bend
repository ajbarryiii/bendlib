import Base

law zero_to_nat:
  for n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}

law add_comm3:
  for a: Word(3n)
  for b: Word(3n)
  {Word.add(3n, a, b) == Word.add(3n, b, a) : Word(3n)}

law not_complement:
  for n: Nat
  for w: Word(n)
  {Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))) == Nat.sub(Nat.pow(2n, n), 1n) : Nat}

law not_to_nat_bad:
  for n: Nat
  for w: Word(n)
  {Word.to_nat(n, Word.not(n, w)) == Word.to_nat(n, w) : Nat}

law not_not:
  for -n: Nat
  for w: Word(n)
  {Word.not(n, Word.not(n, w)) == w : Word(n)}

law add_exact:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: {Nat.is_lt(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.pow(2n, n)) == True{} : Bool}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law add_exact_bad:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law u32_not_not:
  for w: Word(32n)
  {U32.not(U32.not(U32{w})) == U32{w} : U32}

law u32_inc_bad:
  for w: Word(32n)
  {U32.inc(U32{w}) == U32{w} : U32}
