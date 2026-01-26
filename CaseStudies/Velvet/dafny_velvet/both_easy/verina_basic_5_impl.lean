import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-
Problem Description:
  multiply: Multiply two integers.
  Natural language breakdown:
  1. The input consists of two integers a and b.
  2. The output is an integer representing the arithmetic product of a and b.
  3. There are no restrictions on inputs (they may be negative, zero, or positive).
  4. The result is uniquely determined by integer multiplication.
-/

section Specs
-- No helper functions are needed: Int has built-in multiplication via `Int.instMul`.

abbrev precondition (a : Int) (b : Int) : Prop :=
  True

abbrev postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result = a * b
end Specs

section Impl
method multiply (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  let prod := a * b
  return prod
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct multiply by
  loom_solve <;> (try simp at *; expose_names)
end Proof
