import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumOfSquaresOfFirstNOddNumbers: Compute the sum of squares of the first n odd natural numbers
    Natural language breakdown:
    1. The first n odd natural numbers are: 1, 3, 5, 7, ..., (2n-1)
    2. The k-th odd number (1-indexed) is (2k - 1) for k from 1 to n
    3. We need to compute: 1² + 3² + 5² + ... + (2n-1)²
    4. This sum equals the closed-form formula: (n * (2 * n - 1) * (2 * n + 1)) / 3
    5. For n = 0, the sum is 0 (empty sum)
    6. For n = 1, the sum is 1² = 1
    7. For n = 2, the sum is 1² + 3² = 1 + 9 = 10
    8. The formula always yields a natural number (divisibility by 3 is guaranteed)
-/

section Specs

-- The k-th odd number (0-indexed) is 2k + 1
-- For k from 0 to n-1, the odd numbers are: 1, 3, 5, ..., (2n-1)

-- Postcondition: The result equals the closed-form formula
-- The formula (n * (2 * n - 1) * (2 * n + 1)) / 3 computes the sum of squares
-- of the first n odd natural numbers

def precondition (n : Nat) :=
  True  -- n can be any natural number (including 0)

def postcondition (n : Nat) (result : Nat) :=
  result = (n * (2 * n - 1) * (2 * n + 1)) / 3

end Specs

section Impl

method sumOfSquaresOfFirstNOddNumbers (n: Nat)
  return (result: Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 0, empty sum
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1, sum = 1² = 1
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2, sum = 1² + 3² = 1 + 9 = 10
def test3_n : Nat := 2
def test3_Expected : Nat := 10

-- Test case 4: n = 3, sum = 1² + 3² + 5² = 1 + 9 + 25 = 35
def test4_n : Nat := 3
def test4_Expected : Nat := 35

-- Test case 5: n = 4, sum = 1² + 3² + 5² + 7² = 1 + 9 + 25 + 49 = 84
def test5_n : Nat := 4
def test5_Expected : Nat := 84

-- Test case 6: n = 5, sum = 1² + 3² + 5² + 7² + 9² = 1 + 9 + 25 + 49 + 81 = 165
def test6_n : Nat := 5
def test6_Expected : Nat := 165

-- Test case 7: n = 10, larger case to verify formula
def test7_n : Nat := 10
def test7_Expected : Nat := 1330

-- Recommend to validate: 1, 2, 3

end TestCases
