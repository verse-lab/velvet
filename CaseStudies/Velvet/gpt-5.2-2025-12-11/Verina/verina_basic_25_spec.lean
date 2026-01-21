import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
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
def gaussSumNat (n : Nat) : Nat :=
  n * (n + 1) / 2

-- Precondition: allow all n to match provided tests (including n = 0).
def precondition (n : Nat) : Prop :=
  True

-- Postcondition:
-- 1) result.1 is exactly the Gauss sum (as an Int).
-- 2) result.2 is the average:
--    - if n = 0, it is 0.0 (per tests)
--    - if n > 0, it is Float.ofInt result.1 / Float.ofNat n
-- This fully determines the output for every n.
def postcondition (n : Nat) (result : Int × Float) : Prop :=
  result.1 = Int.ofNat (gaussSumNat n) ∧
  (n = 0 → result.2 = 0.0) ∧
  (n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n))

end Specs

section Impl

method sumAndAverage (n: Nat) return (result: Int × Float)
  require precondition n
  ensures postcondition n result
  do
  pure (0, 0.0)  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt: n = 5
-- Sum 0..5 = 15, average = 15/5 = 3.0

def test1_n : Nat := 5

def test1_Expected : Int × Float := (15, 3.0)

-- Test case 2: n = 1
-- Sum 0..1 = 1, average = 1/1 = 1.0

def test2_n : Nat := 1

def test2_Expected : Int × Float := (1, 1.0)

-- Test case 3: n = 10
-- Sum 0..10 = 55, average = 55/10 = 5.5

def test3_n : Nat := 10

def test3_Expected : Int × Float := (55, 5.5)

-- Test case 4: edge case from prompt: n = 0
-- By the tests: sum = 0 and average = 0.0

def test4_n : Nat := 0

def test4_Expected : Int × Float := (0, 0.0)

-- Test case 5: n = 2
-- Sum 0..2 = 3, average = 3/2 = 1.5

def test5_n : Nat := 2

def test5_Expected : Int × Float := (3, 1.5)

-- Additional representative cases (not in the original provided list)

-- Test case 6: n = 3
-- Sum = 6, average = 2.0

def test6_n : Nat := 3

def test6_Expected : Int × Float := (6, 2.0)

-- Test case 7: n = 4
-- Sum = 10, average = 2.5

def test7_n : Nat := 4

def test7_Expected : Int × Float := (10, 2.5)

-- Test case 8: n = 6
-- Sum = 21, average = 3.5

def test8_n : Nat := 6

def test8_Expected : Int × Float := (21, 3.5)

-- Test case 9: n = 8
-- Sum = 36, average = 4.5

def test9_n : Nat := 8

def test9_Expected : Int × Float := (36, 4.5)

-- Recommend to validate: test1, test4, test5

end TestCases
