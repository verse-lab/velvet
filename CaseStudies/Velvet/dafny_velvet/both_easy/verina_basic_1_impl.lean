import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasOppositeSign: determine whether two integers have opposite signs.

    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. Zero is considered neither positive nor negative.
    3. Two integers have opposite signs exactly when one is strictly positive
       and the other is strictly negative.
    4. Equivalently, both must be nonzero and their signs (via Int.sign)
       must be different and opposite.
    5. Int.sign x = 1 if x > 0; Int.sign x = -1 if x < 0; Int.sign x = 0 if x = 0.
    6. The method should return true iff a and b have opposite signs.
    7. It should return false if both are nonnegative, both are nonpositive,
       or if at least one is zero.

    We formalize this using inequalities on Int.
-/

section Specs

abbrev hasOppositeSignSpec (a: Int) (b: Int) : Prop :=
  (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)

end Specs
section Impl
method hasOppositeSign (a: Int) (b: Int)
  return (result: Bool)
  ensures result = true ↔ hasOppositeSignSpec a b
  do
  if a > 0 ∧ b < 0 then
    return true
  else if a < 0 ∧ b > 0 then
    return true
  else
    return false
end Impl

section Proof

prove_correct hasOppositeSign by
  loom_solve <;> (simp at *; expose_names)

end Proof
