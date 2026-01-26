import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. Input n is a natural number (hence non-negative by type).
    2. The last digit in base 10 is the remainder when dividing n by 10.
    3. The result must be a natural number between 0 and 9 inclusive.
    4. The returned digit must satisfy: result = n % 10.
-/

section Specs
-- Preconditions: no additional requirements because n : Nat is already non-negative.
abbrev precondition (n : Nat) : Prop :=
  True

-- Postconditions:
-- 1) result is exactly the remainder mod 10
-- 2) result is a decimal digit (0..9), captured by result < 10
-- Note: the bound is redundant given result = n % 10, but kept for readability.
abbrev postcondition (n : Nat) (result : Nat) : Prop :=
  result = n % 10 ∧ result < 10
end Specs

section Impl
method lastDigit (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    let d := n % 10
    return d
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct lastDigit by
  -- loom_solve <;> (try simp at *; expose_names)

prove_correct lastDigit by
  loom_solve <;> (try simp at *; expose_names)
end Proof
