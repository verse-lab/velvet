import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumAndAverage: Calculate both the sum and the average of the first n natural numbers
    Natural language breakdown:
    1. Given a positive natural number n, compute the sum of numbers from 1 to n
    2. The sum of first n natural numbers equals n * (n + 1) / 2 (Gauss formula)
    3. The average is computed by dividing the sum by n
    4. The result is a pair: (sum as Int, average as Float)
    5. Preconditions:
       - n must be positive (n > 0)
       - n must be bounded (n < 2^53) to ensure floating-point precision
    6. Key properties:
       - The sum equals n * (n + 1) / 2
       - The average equals sum / n as a Float
    7. Edge cases:
       - n = 1: sum = 1, average = 1.0
       - n = 2: sum = 3, average = 1.5
       - Larger values: n = 10 gives sum = 55, average = 5.5
-/

section Specs

-- Helper function to compute the expected sum using Gauss formula
-- Renamed to avoid conflict with Mathlib's gaussSum
def sumFormula (n : Nat) : Nat :=
  n * (n + 1) / 2

-- Precondition: n must be positive and bounded for float precision
def precondition (n : Nat) : Prop :=
  n > 0 ∧ n < 9007199254740992  -- 2^53

-- Postcondition clauses
-- The sum component equals the Gauss formula result
def ensures1 (n : Nat) (result : Int × Float) : Prop :=
  result.fst = (sumFormula n : Int)

-- The average component equals sum divided by n
def ensures2 (n : Nat) (result : Int × Float) : Prop :=
  result.snd = (sumFormula n : Nat).toFloat / (n : Nat).toFloat

def postcondition (n : Nat) (result : Int × Float) : Prop :=
  ensures1 n result ∧ ensures2 n result

end Specs

section Impl

method sumAndAverage (n : Nat)
  return (result : Int × Float)
  require precondition n
  ensures postcondition n result
  do
  pure (0, 0.0)  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 5 (example from problem)
def test1_n : Nat := 5
def test1_Expected : Int × Float := (15, 3.0)

-- Test case 2: n = 1 (minimum valid input)
def test2_n : Nat := 1
def test2_Expected : Int × Float := (1, 1.0)

-- Test case 3: n = 10 (example from problem)
def test3_n : Nat := 10
def test3_Expected : Int × Float := (55, 5.5)

-- Test case 4: n = 2 (small case with non-integer average)
def test4_n : Nat := 2
def test4_Expected : Int × Float := (3, 1.5)

-- Test case 5: n = 100 (larger value)
def test5_n : Nat := 100
def test5_Expected : Int × Float := (5050, 50.5)

-- Test case 6: n = 3 (small odd number)
def test6_n : Nat := 3
def test6_Expected : Int × Float := (6, 2.0)

-- Test case 7: n = 7 (prime number)
def test7_n : Nat := 7
def test7_Expected : Int × Float := (28, 4.0)

-- Test case 8: n = 20 (medium value)
def test8_n : Nat := 20
def test8_Expected : Int × Float := (210, 10.5)

-- Test case 9: n = 50 (larger value)
def test9_n : Nat := 50
def test9_Expected : Int × Float := (1275, 25.5)

-- Test case 10: n = 1000 (stress test)
def test10_n : Nat := 1000
def test10_Expected : Int × Float := (500500, 500.5)

-- Recommend to validate: 1, 2, 4

end TestCases
