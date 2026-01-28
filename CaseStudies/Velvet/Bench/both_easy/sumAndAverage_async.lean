import CaseStudies.Velvet.Std
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

def gaussSumNat (n : Nat) : Nat :=
  n * (n + 1) / 2

section Impl
method sumAndAverage (n: Nat) return (result: Int × Float)
  ensures result.1 = Int.ofNat (gaussSumNat n)
  ensures n = 0 → result.2 = 0.0
  ensures n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n)
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
  loom_solve_async
end Proof
