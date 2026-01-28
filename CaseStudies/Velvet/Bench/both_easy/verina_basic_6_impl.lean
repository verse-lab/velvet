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
section Impl
method minOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  ensures result ≤ a
  ensures result ≤ b
  ensures result ≤ c
  ensures result = a ∨ result = b ∨ result = c
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
  loom_solve
end Proof
