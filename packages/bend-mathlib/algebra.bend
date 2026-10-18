# bend-mathlib/algebra.bend: abstract associativity/commutativity theorems and their Nat/Bool/List instances.
import Base
import ./nat.bend as MNat
import ./bool.bend as MBool
import ./list.bend as MList

# Four-way reassociation from associativity alone.
law op_assoc4:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  {op(op(op(a, b), c), d) == op(a, op(b, op(c, d))) : A}

def op_assoc4(A, op, assoc, a, b, c, d):
  %assoc(a, b, op(c, d)) : {op(op(op(a, b), c), d) == _ : A}
  assoc(op(a, b), c, d)

# Left commutation from associativity and commutativity.
law op_left_comm:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(a, op(b, c)) == op(b, op(a, c)) : A}

def op_left_comm(A, op, assoc, comm, a, b, c):
  %assoc(a, b, c) : {_ == op(b, op(a, c)) : A}
  %Equal.sym(A, op(a, b), op(b, a), comm(a, b)) : {op(_, c) == op(b, op(a, c)) : A}
  assoc(b, a, c)

# Right commutation from associativity and commutativity.
law op_right_comm:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(op(a, b), c) == op(op(a, c), b) : A}

def op_right_comm(A, op, assoc, comm, a, b, c):
  %Equal.sym(A, op(op(a, b), c), op(a, op(b, c)), assoc(a, b, c)) : {_ == op(op(a, c), b) : A}
  %Equal.sym(A, op(op(a, c), b), op(a, op(c, b)), assoc(a, c, b)) : {op(a, op(b, c)) == _ : A}
  %Equal.sym(A, op(c, b), op(b, c), comm(c, b)) : {op(a, op(b, c)) == op(a, _) : A}
  {==}

# Middle-four interchange from associativity and commutativity.
law op_four:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  {op(op(a, b), op(c, d)) == op(op(a, c), op(b, d)) : A}

def op_four(A, op, assoc, comm, a, b, c, d):
  %Equal.sym(A, op(op(a, b), op(c, d)), op(a, op(b, op(c, d))), assoc(a, b, op(c, d))) : {_ == op(op(a, c), op(b, d)) : A}
  %Equal.sym(A, op(op(a, c), op(b, d)), op(a, op(c, op(b, d))), assoc(a, c, op(b, d))) : {op(a, op(b, op(c, d))) == _ : A}
  %op_left_comm(A, op, assoc, comm, b, c, d) : {op(a, op(b, op(c, d))) == op(a, _) : A}
  {==}

# Three-way commutation from commutativity alone.
law op_comm3:
  for ~A: Data
  for ~op: A -> A -> A
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(op(a, b), c) == op(c, op(b, a)) : A}

def op_comm3(A, op, comm, a, b, c):
  %Equal.sym(A, op(op(a, b), c), op(c, op(a, b)), comm(op(a, b), c)) : {_ == op(c, op(b, a)) : A}
  %Equal.sym(A, op(b, a), op(a, b), comm(b, a)) : {op(c, op(a, b)) == op(c, _) : A}
  {==}

def internal_nat_add_assoc(x: Nat, y: Nat, z: Nat) -> {Nat.add(Nat.add(x, y), z) == Nat.add(x, Nat.add(y, z)) : Nat}:
  MNat.add_assoc(x, y, z)

def internal_nat_add_comm(x: Nat, y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  MNat.add_comm(x, y)

def internal_nat_zero_add(x: Nat) -> {Nat.add(0n, x) == x : Nat}:
  MNat.zero_add(x)

def internal_nat_mul(x: Nat, y: Nat) -> Nat:
  Nat.mul(x, y)

def internal_nat_mul_assoc(x: Nat, y: Nat, z: Nat) -> {Nat.mul(Nat.mul(x, y), z) == Nat.mul(x, Nat.mul(y, z)) : Nat}:
  MNat.mul_assoc(x, y, z)

def internal_nat_mul_comm(x: Nat, y: Nat) -> {Nat.mul(x, y) == Nat.mul(y, x) : Nat}:
  MNat.mul_comm(x, y)

def internal_bool_and_assoc(x: Bool, y: Bool, z: Bool) -> {Bool.and(Bool.and(x, y), z) == Bool.and(x, Bool.and(y, z)) : Bool}:
  MBool.and_assoc(x, y, z)

def internal_bool_and_comm(x: Bool, y: Bool) -> {Bool.and(x, y) == Bool.and(y, x) : Bool}:
  MBool.and_comm(x, y)

def internal_bool_or_assoc(x: Bool, y: Bool, z: Bool) -> {Bool.or(Bool.or(x, y), z) == Bool.or(x, Bool.or(y, z)) : Bool}:
  MBool.or_assoc(x, y, z)

def internal_bool_or_comm(x: Bool, y: Bool) -> {Bool.or(x, y) == Bool.or(y, x) : Bool}:
  MBool.or_comm(x, y)

def internal_list_nat_append_assoc(x: List<&2, Nat>, y: List<&2, Nat>, z: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, x, y), z) == List.append(&2, Nat, x, List.append(&2, Nat, y, z)) : List<&2, Nat>}:
  MList.append_assoc(&2, Nat, x, y, z)

# Nat addition is left-commutative (the same statement as MNat.add_left_comm).
law nat_add_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def nat_add_left_comm(a, b, c):
  op_left_comm(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, a, b, c)

# Nat addition is right-commutative (the same statement as MNat.add_right_comm).
law nat_add_right_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def nat_add_right_comm(a, b, c):
  op_right_comm(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, a, b, c)

# Nat addition's middle-four interchange (the same statement as MNat.add_add_add_comm).
law nat_add_four:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def nat_add_four(a, b, c, d):
  op_four(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, a, b, c, d)

# Nat multiplication is left-commutative (the same statement as MNat.mul_left_comm).
law nat_mul_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}

def nat_mul_left_comm(a, b, c):
  op_left_comm(~Nat, ~internal_nat_mul, ~internal_nat_mul_assoc, ~internal_nat_mul_comm, a, b, c)

# Nat multiplication is right-commutative (the same statement as MNat.mul_right_comm).
law nat_mul_right_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(Nat.mul(a, c), b) : Nat}

def nat_mul_right_comm(a, b, c):
  op_right_comm(~Nat, ~internal_nat_mul, ~internal_nat_mul_assoc, ~internal_nat_mul_comm, a, b, c)

# Nat multiplication's middle-four interchange (the same statement as MNat.mul_mul_mul_comm).
law nat_mul_four:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}

def nat_mul_four(a, b, c, d):
  op_four(~Nat, ~internal_nat_mul, ~internal_nat_mul_assoc, ~internal_nat_mul_comm, a, b, c, d)

# Bool and is left-commutative.
law bool_and_left_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}

def bool_and_left_comm(a, b, c):
  op_left_comm(~Bool, ~Bool.and, ~internal_bool_and_assoc, ~internal_bool_and_comm, a, b, c)

# Bool and is right-commutative.
law bool_and_right_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(Bool.and(a, c), b) : Bool}

def bool_and_right_comm(a, b, c):
  op_right_comm(~Bool, ~Bool.and, ~internal_bool_and_assoc, ~internal_bool_and_comm, a, b, c)

# Bool or is left-commutative.
law bool_or_left_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}

def bool_or_left_comm(a, b, c):
  op_left_comm(~Bool, ~Bool.or, ~internal_bool_or_assoc, ~internal_bool_or_comm, a, b, c)

# Bool or is right-commutative.
law bool_or_right_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(Bool.or(a, c), b) : Bool}

def bool_or_right_comm(a, b, c):
  op_right_comm(~Bool, ~Bool.or, ~internal_bool_or_assoc, ~internal_bool_or_comm, a, b, c)

# Four-way reassociation for List append over Nat.
law list_nat_append_assoc4:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +c: List<&2, Nat>
  for +d: List<&2, Nat>
  {List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, a, b), c), d) == List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d))) : List<&2, Nat>}

def list_nat_append_assoc4(a, b, c, d):
  op_assoc4(~List<&2, Nat>, ~List.append(&2, Nat), ~internal_list_nat_append_assoc, a, b, c, d)

def internal_foldl_foldr(~B: Data, ~op: B -> B -> B, ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}, ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}, ~z: B, ~id: @x: B -> {op(z, x) == x : B}, +xs: List<&2, B>, +acc: B) -> {List.foldl(&2, B, B, op, xs, acc) == op(acc, List.foldr(&2, B, B, op, xs, z)) : B}:
  match xs:
    case Nil{}:
      Equal.sym(B, op(acc, z), acc, Equal.trans(B, op(acc, z), op(z, acc), acc, comm(acc, z), id(acc)))
    case +h <> +t:
      %Equal.sym(B, List.foldl(&2, B, B, op, t, op(acc, h)), op(op(acc, h), List.foldr(&2, B, B, op, t, z)), internal_foldl_foldr(~B, ~op, ~assoc, ~comm, ~z, ~id, t, op(acc, h))) : {_ == op(acc, op(h, List.foldr(&2, B, B, op, t, z))) : B}
      assoc(acc, h, List.foldr(&2, B, B, op, t, z))

# Folding left equals folding right for an associative, commutative operation with a left identity (foldl_eq_foldr needs no identity).
law foldl_op_eq_foldr_op:
  for ~B: Data
  for ~op: B -> B -> B
  for ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}
  for ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}
  for ~z: B
  for ~id: @x: B -> {op(z, x) == x : B}
  for +xs: List<&2, B>
  {List.foldl(&2, B, B, op, xs, z) == List.foldr(&2, B, B, op, xs, z) : B}

def foldl_op_eq_foldr_op(B, op, assoc, comm, z, id, xs):
  %Equal.sym(B, List.foldl(&2, B, B, op, xs, z), op(z, List.foldr(&2, B, B, op, xs, z)), internal_foldl_foldr(~B, ~op, ~assoc, ~comm, ~z, ~id, xs, z)) : {_ == List.foldr(&2, B, B, op, xs, z) : B}
  id(List.foldr(&2, B, B, op, xs, z))

# A Nat call: --verdict takes a ~ constant's model from a call of its law (PLAN F38).
def internal_nat_foldl_op_eq_foldr_op(+xs: List<&2, Nat>) -> {List.foldl(&2, Nat, Nat, Nat.add, xs, 0n) == List.foldr(&2, Nat, Nat, Nat.add, xs, 0n) : Nat}:
  foldl_op_eq_foldr_op(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, ~0n, ~internal_nat_zero_add, xs)

def internal_foldl_assoc(~B: Data, ~op: B -> B -> B, ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}, +xs: List<&2, B>, +a: B, +b: B) -> {List.foldl(&2, B, B, op, xs, op(a, b)) == op(a, List.foldl(&2, B, B, op, xs, b)) : B}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(B, op(op(a, b), h), op(a, op(b, h)), assoc(a, b, h)) : {List.foldl(&2, B, B, op, t, _) == op(a, List.foldl(&2, B, B, op, t, op(b, h))) : B}
      internal_foldl_assoc(~B, ~op, ~assoc, t, a, op(b, h))

def internal_foldl_eq_foldr(~B: Data, ~op: B -> B -> B, ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}, ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}, +z: B, +xs: List<&2, B>) -> {List.foldl(&2, B, B, op, xs, z) == List.foldr(&2, B, B, op, xs, z) : B}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %comm(h, z) : {List.foldl(&2, B, B, op, t, _) == op(h, List.foldr(&2, B, B, op, t, z)) : B}
      %Equal.sym(B, List.foldl(&2, B, B, op, t, op(h, z)), op(h, List.foldl(&2, B, B, op, t, z)), internal_foldl_assoc(~B, ~op, ~assoc, t, h, z)) : {_ == op(h, List.foldr(&2, B, B, op, t, z)) : B}
      %internal_foldl_eq_foldr(~B, ~op, ~assoc, ~comm, z, t) : {op(h, List.foldl(&2, B, B, op, t, z)) == op(h, _) : B}
      {==}

# Folding left equals folding right for an associative, commutative operation (Mathlib's List.foldl_eq_foldr).
law foldl_eq_foldr:
  for ~B: Data
  for ~op: B -> B -> B
  for ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}
  for ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}
  for +z: B
  for +xs: List<&2, B>
  {List.foldl(&2, B, B, op, xs, z) == List.foldr(&2, B, B, op, xs, z) : B}

def foldl_eq_foldr(B, op, assoc, comm, z, xs):
  internal_foldl_eq_foldr(~B, ~op, ~assoc, ~comm, z, xs)

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Four-way reassociation from associativity alone, reversed to rewrite toward the simple side.
law op_assoc4_sym:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  {op(a, op(b, op(c, d))) == op(op(op(a, b), c), d) : A}

def op_assoc4_sym(A, op, assoc, a, b, c, d):
  Equal.sym(A, op(op(op(a, b), c), d), op(a, op(b, op(c, d))), op_assoc4(~A, ~op, ~assoc, a, b, c, d))

# Left commutation from associativity and commutativity, reversed to rewrite toward the simple side.
law op_left_comm_sym:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(b, op(a, c)) == op(a, op(b, c)) : A}

def op_left_comm_sym(A, op, assoc, comm, a, b, c):
  Equal.sym(A, op(a, op(b, c)), op(b, op(a, c)), op_left_comm(~A, ~op, ~assoc, ~comm, a, b, c))

# Right commutation from associativity and commutativity, reversed to rewrite toward the simple side.
law op_right_comm_sym:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(op(a, c), b) == op(op(a, b), c) : A}

def op_right_comm_sym(A, op, assoc, comm, a, b, c):
  Equal.sym(A, op(op(a, b), c), op(op(a, c), b), op_right_comm(~A, ~op, ~assoc, ~comm, a, b, c))

# Middle-four interchange from associativity and commutativity, reversed to rewrite toward the simple side.
law op_four_sym:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  {op(op(a, c), op(b, d)) == op(op(a, b), op(c, d)) : A}

def op_four_sym(A, op, assoc, comm, a, b, c, d):
  Equal.sym(A, op(op(a, b), op(c, d)), op(op(a, c), op(b, d)), op_four(~A, ~op, ~assoc, ~comm, a, b, c, d))

# Three-way commutation from commutativity alone, reversed to rewrite toward the simple side.
law op_comm3_sym:
  for ~A: Data
  for ~op: A -> A -> A
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(c, op(b, a)) == op(op(a, b), c) : A}

def op_comm3_sym(A, op, comm, a, b, c):
  Equal.sym(A, op(op(a, b), c), op(c, op(b, a)), op_comm3(~A, ~op, ~comm, a, b, c))

# Nat addition is left-commutative (the same statement as MNat.add_left_comm), reversed to rewrite toward the simple side.
law nat_add_left_comm_sym:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}

def nat_add_left_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(b, Nat.add(a, c)), nat_add_left_comm(a, b, c))

# Nat addition is right-commutative (the same statement as MNat.add_right_comm), reversed to rewrite toward the simple side.
law nat_add_right_comm_sym:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(a, b), c) : Nat}

def nat_add_right_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a, c), b), nat_add_right_comm(a, b, c))

# Nat addition's middle-four interchange (the same statement as MNat.add_add_add_comm), reversed to rewrite toward the simple side.
law nat_add_four_sym:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}

def nat_add_four_sym(a, b, c, d):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(Nat.add(a, c), Nat.add(b, d)), nat_add_four(a, b, c, d))

# Nat multiplication is left-commutative (the same statement as MNat.mul_left_comm), reversed to rewrite toward the simple side.
law nat_mul_left_comm_sym:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(b, Nat.mul(a, c)) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def nat_mul_left_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(a, Nat.mul(b, c)), Nat.mul(b, Nat.mul(a, c)), nat_mul_left_comm(a, b, c))

# Nat multiplication is right-commutative (the same statement as MNat.mul_right_comm), reversed to rewrite toward the simple side.
law nat_mul_right_comm_sym:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, c), b) == Nat.mul(Nat.mul(a, b), c) : Nat}

def nat_mul_right_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(Nat.mul(a, c), b), nat_mul_right_comm(a, b, c))

# Nat multiplication's middle-four interchange (the same statement as MNat.mul_mul_mul_comm), reversed to rewrite toward the simple side.
law nat_mul_four_sym:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) == Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) : Nat}

def nat_mul_four_sym(a, b, c, d):
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), Nat.mul(c, d)), Nat.mul(Nat.mul(a, c), Nat.mul(b, d)), nat_mul_four(a, b, c, d))

# Bool and is left-commutative, reversed to rewrite toward the simple side.
law bool_and_left_comm_sym:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(b, Bool.and(a, c)) == Bool.and(a, Bool.and(b, c)) : Bool}

def bool_and_left_comm_sym(a, b, c):
  Equal.sym(Bool, Bool.and(a, Bool.and(b, c)), Bool.and(b, Bool.and(a, c)), bool_and_left_comm(a, b, c))

# Bool and is right-commutative, reversed to rewrite toward the simple side.
law bool_and_right_comm_sym:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, c), b) == Bool.and(Bool.and(a, b), c) : Bool}

def bool_and_right_comm_sym(a, b, c):
  Equal.sym(Bool, Bool.and(Bool.and(a, b), c), Bool.and(Bool.and(a, c), b), bool_and_right_comm(a, b, c))

# Bool or is left-commutative, reversed to rewrite toward the simple side.
law bool_or_left_comm_sym:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(b, Bool.or(a, c)) == Bool.or(a, Bool.or(b, c)) : Bool}

def bool_or_left_comm_sym(a, b, c):
  Equal.sym(Bool, Bool.or(a, Bool.or(b, c)), Bool.or(b, Bool.or(a, c)), bool_or_left_comm(a, b, c))

# Bool or is right-commutative, reversed to rewrite toward the simple side.
law bool_or_right_comm_sym:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(Bool.or(a, c), b) == Bool.or(Bool.or(a, b), c) : Bool}

def bool_or_right_comm_sym(a, b, c):
  Equal.sym(Bool, Bool.or(Bool.or(a, b), c), Bool.or(Bool.or(a, c), b), bool_or_right_comm(a, b, c))

# Four-way reassociation for List append over Nat, reversed to rewrite toward the simple side.
law list_nat_append_assoc4_sym:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +c: List<&2, Nat>
  for +d: List<&2, Nat>
  {List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d))) == List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, a, b), c), d) : List<&2, Nat>}

def list_nat_append_assoc4_sym(a, b, c, d):
  Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, a, b), c), d), List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d))), list_nat_append_assoc4(a, b, c, d))

# Folding left equals folding right for an associative, commutative operation with a left identity (foldl_eq_foldr needs no identity), reversed to rewrite toward the simple side.
law foldl_op_eq_foldr_op_sym:
  for ~B: Data
  for ~op: B -> B -> B
  for ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}
  for ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}
  for ~z: B
  for ~id: @x: B -> {op(z, x) == x : B}
  for +xs: List<&2, B>
  {List.foldr(&2, B, B, op, xs, z) == List.foldl(&2, B, B, op, xs, z) : B}

def foldl_op_eq_foldr_op_sym(B, op, assoc, comm, z, id, xs):
  Equal.sym(B, List.foldl(&2, B, B, op, xs, z), List.foldr(&2, B, B, op, xs, z), foldl_op_eq_foldr_op(~B, ~op, ~assoc, ~comm, ~z, ~id, xs))

# Folding left equals folding right for an associative, commutative operation (Mathlib's List.foldl_eq_foldr), reversed to rewrite toward the simple side.
law foldl_eq_foldr_sym:
  for ~B: Data
  for ~op: B -> B -> B
  for ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}
  for ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}
  for +z: B
  for +xs: List<&2, B>
  {List.foldr(&2, B, B, op, xs, z) == List.foldl(&2, B, B, op, xs, z) : B}

def foldl_eq_foldr_sym(B, op, assoc, comm, z, xs):
  Equal.sym(B, List.foldl(&2, B, B, op, xs, z), List.foldr(&2, B, B, op, xs, z), foldl_eq_foldr(~B, ~op, ~assoc, ~comm, z, xs))

# Calls of the twins, as the calls above the generated section make of their laws (PLAN F38).
def internal_nat_foldl_op_eq_foldr_op_sym(+xs: List<&2, Nat>) -> {List.foldr(&2, Nat, Nat, Nat.add, xs, 0n) == List.foldl(&2, Nat, Nat, Nat.add, xs, 0n) : Nat}:
  foldl_op_eq_foldr_op_sym(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, ~0n, ~internal_nat_zero_add, xs)
