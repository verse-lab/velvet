import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumOfFourthPowerOfOddNumbers: Compute the sum of the fourth power of the first n odd natural numbers
    Natural language breakdown:
    1. Given a non-negative integer n, compute the sum 1⁴ + 3⁴ + 5⁴ + ... for the first n odd numbers
    2. The k-th odd number (0-indexed) is (2*k + 1)
    3. For n = 0, the sum is 0 (empty sum)
    4. For n = 1, the sum is 1⁴ = 1
    5. For n = 2, the sum is 1⁴ + 3⁴ = 1 + 81 = 82
    6. For n = 3, the sum is 1⁴ + 3⁴ + 5⁴ = 1 + 81 + 625 = 707
    7. The general formula: sum over k from 0 to n-1 of (2*k + 1)⁴
    8. Using Finset.sum from Mathlib: Finset.sum (Finset.range n) (fun k => (2*k + 1)^4)
-/

section Specs

-- The k-th odd number (0-indexed) is 2*k + 1
-- We use Finset.sum from Mathlib to express the sum

-- Postcondition: result equals the sum of fourth powers of first n odd numbers
def ensures1 (n : Nat) (result : Nat) :=
  result = Finset.sum (Finset.range n) (fun k => (2 * k + 1) ^ 4)

def precondition (n : Nat) :=
  True  -- n is any non-negative natural number

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result

end Specs

section Impl

method sumOfFourthPowerOfOddNumbers (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 0 (empty sum)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 (only 1⁴ = 1)
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2 (1⁴ + 3⁴ = 1 + 81 = 82)
def test3_n : Nat := 2
def test3_Expected : Nat := 82

-- Test case 4: n = 3 (1⁴ + 3⁴ + 5⁴ = 1 + 81 + 625 = 707)
def test4_n : Nat := 3
def test4_Expected : Nat := 707

-- Test case 5: n = 4 (1⁴ + 3⁴ + 5⁴ + 7⁴ = 1 + 81 + 625 + 2401 = 3108)
def test5_n : Nat := 4
def test5_Expected : Nat := 3108

-- Test case 6: n = 5 (1⁴ + 3⁴ + 5⁴ + 7⁴ + 9⁴ = 1 + 81 + 625 + 2401 + 6561 = 9669)
def test6_n : Nat := 5
def test6_Expected : Nat := 9669

-- Test case 7: n = 6 (adding 11⁴ = 14641, total = 9669 + 14641 = 24310)
def test7_n : Nat := 6
def test7_Expected : Nat := 24310

-- Recommend to validate: 1, 3, 5

end TestCases
