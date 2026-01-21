import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Abs: Calculate the absolute value of an integer
    Natural language breakdown:
    1. We have an input integer x
    2. The absolute value is the non-negative magnitude of the integer
    3. If x is non-negative (x ≥ 0), the result is x itself
    4. If x is negative (x < 0), the result is the negation of x (i.e., -x)
    5. The result is always non-negative (result ≥ 0)
    6. Zero has absolute value zero
    7. For any integer x, |x| = |-x| (symmetry property)
    8. The result satisfies: result * result = x * x

    Property-oriented specification:
    - The result is non-negative
    - The result equals x if x ≥ 0, otherwise equals -x
    - Equivalently: result = x.natAbs (using Mathlib's Int.natAbs converted to Int)
-/

section Specs

-- Helper Functions
-- Using Int.natAbs from Mathlib which computes absolute value

-- Precondition: no restrictions on input integer
def precondition (x : Int) :=
  True

-- Postcondition: result is the absolute value of x
-- Properties:
-- 1. result is non-negative
-- 2. result equals x if x ≥ 0, otherwise equals -x
-- 3. result squared equals x squared (another way to characterize abs)
def postcondition (x : Int) (result : Int) :=
  result ≥ 0 ∧
  (x ≥ 0 → result = x) ∧
  (x < 0 → result = -x)

end Specs

section Impl

method Abs (x: Int)
  return (result: Int)
  require precondition x
  ensures postcondition x result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Positive integer (from provided examples)
def test1_x : Int := 5
def test1_Expected : Int := 5

-- Test case 2: Zero (edge case)
def test2_x : Int := 0
def test2_Expected : Int := 0

-- Test case 3: Negative integer (from provided examples)
def test3_x : Int := -5
def test3_Expected : Int := 5

-- Test case 4: Larger positive integer
def test4_x : Int := 10
def test4_Expected : Int := 10

-- Test case 5: Larger negative integer
def test5_x : Int := -10
def test5_Expected : Int := 10

-- Test case 6: Small negative integer
def test6_x : Int := -1
def test6_Expected : Int := 1

-- Test case 7: Small positive integer
def test7_x : Int := 1
def test7_Expected : Int := 1

-- Test case 8: Large negative number
def test8_x : Int := -1000
def test8_Expected : Int := 1000

-- Test case 9: Large positive number
def test9_x : Int := 1000
def test9_Expected : Int := 1000

-- Test case 10: Negative two (another small case)
def test10_x : Int := -2
def test10_Expected : Int := 2

-- Recommend to validate: 1, 2, 3

end TestCases
