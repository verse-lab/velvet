import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    verina_basic_6: Minimum of three integers

    Natural language breakdown:
    1. The input consists of three integers a, b, and c.
    2. The function returns an integer result intended to be the minimum among a, b, and c.
    3. The result must be less than or equal to each input: result ≤ a, result ≤ b, and result ≤ c.
    4. The result must be one of the inputs: result = a or result = b or result = c.
    5. There are no rejected inputs; all Int inputs are valid.
-/

section Specs
-- No rejected inputs.
-- IMPORTANT: SpecDSL requires parameter names and order to match exactly between
-- precondition and the corresponding prefix of postcondition.
abbrev precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

abbrev postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  (result ≤ a ∧ result ≤ b ∧ result ≤ c) ∧
  (result = a ∨ result = b ∨ result = c)
end Specs

section Impl
method minOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
    let mut m := a
    if b <= m then
      m := b
    else
      pure ()
    if c <= m then
      m := c
    else
      pure ()
    return m
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct minOfThree by
  loom_solve <;> (try simp at *; expose_names)
end Proof
