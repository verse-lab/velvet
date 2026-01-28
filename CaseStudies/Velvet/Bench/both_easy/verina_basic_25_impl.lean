import CaseStudies.Velvet.Std
import Mathlib.Tactic
import Batteries.Lean.Float

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumAndAverage: compute the sum and average of the first n natural numbers.
    Natural language breakdown:
    1. Input n is a natural number.
    2. The sum is the sum of all natural numbers from 0 to n inclusive.
    3. The sum satisfies Gauss' identity: 2 * sum = n * (n + 1).
    4. The output sum is returned as an Int and must be nonnegative.
    5. The average is a Float intended to represent sum / n.
    6. Although the narrative says n is positive, the tests include n = 0.
    7. For n = 0, the output is defined by the tests as (0, 0.0).
    8. For n > 0, the average is defined using Float division of the converted sum by Float.ofNat n.
-/

section Specs
-- Helper: closed-form Gauss sum as a Nat (this is specification-level, non-recursive).
-- We use Nat arithmetic; for n=0 this yields 0.
abbrev gaussSumNat (n : Nat) : Nat :=
  n * (n + 1) / 2

-- Precondition: allow all n to match provided tests (including n = 0).
abbrev precondition (n : Nat) : Prop :=
  True

-- Postcondition:
-- 1) result.1 is exactly the Gauss sum (as an Int).
-- 2) result.2 is the average:
--    - if n = 0, it is 0.0 (per tests)
--    - if n > 0, it is Float.ofInt result.1 / Float.ofNat n
-- This fully determines the output for every n.
abbrev postcondition (n : Nat) (result : Int × Float) : Prop :=
  result.1 = Int.ofNat (gaussSumNat n) ∧
  (n = 0 → result.2 = 0.0) ∧
  (n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n))
end Specs

section Impl
method sumAndAverage (n: Nat) return (result: Int × Float)
  require precondition n
  ensures postcondition n result
  do
    let sumNat : Nat := gaussSumNat n
    let sumInt : Int := Int.ofNat sumNat

    if n = 0 then
      return (sumInt, 0.0)
    else
      let avg : Float := (Float.ofInt sumInt) / (Float.ofNat n)
      return (sumInt, avg)
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct sumAndAverage by
  loom_solve <;> (try simp at *; expose_names)
end Proof
