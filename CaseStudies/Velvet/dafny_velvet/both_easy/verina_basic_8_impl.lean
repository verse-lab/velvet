import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    myMin: Determine the minimum of two integers.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must be less than or equal to a, and less than or equal to b.
    4. The result must be one of the inputs (either a or b).
    5. When a = b, returning either one is allowed (they are equal).
-/

section Specs
-- No helper functions are necessary: we can specify the minimum using order and equality.

abbrev precondition (a : Int) (b : Int) : Prop :=
  True

abbrev postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ (result = a ∨ result = b)
end Specs

section Impl
method myMin (a : Int) (b : Int) return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
    if a <= b then
      return a
    else
      return b
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct myMin by
  loom_solve <;> (try simp at *; expose_names)
end Proof
