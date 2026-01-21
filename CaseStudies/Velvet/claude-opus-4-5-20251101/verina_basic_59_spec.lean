import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    DoubleQuadruple: Given an integer x, return a pair (a, b) where a = 2*x and b = 4*x
    Natural language breakdown:
    1. We are given an integer x (can be positive, negative, or zero)
    2. We need to compute a pair (a, b) of integers
    3. The first element a must equal 2 times x
    4. The second element b must equal 4 times x
    5. Note that b = 2 * a (relationship between components)
    6. No preconditions needed - method is defined for all integers
    7. Edge cases:
       - x = 0: result is (0, 0)
       - x positive: both components positive
       - x negative: both components negative
-/

section Specs

-- Precondition: no restrictions on input
def precondition (x : Int) :=
  True

-- Postcondition: first element is 2*x, second element is 4*x
def postcondition (x : Int) (result : Int × Int) :=
  result.1 = 2 * x ∧ result.2 = 4 * x

end Specs

section Impl

method DoubleQuadruple (x: Int)
  return (result: Int × Int)
  require precondition x
  ensures postcondition x result
  do
  pure (0, 0)  -- placeholder

end Impl

section TestCases

-- Test case 1: x = 0 (edge case - zero input)
def test1_x : Int := 0
def test1_Expected : Int × Int := (0, 0)

-- Test case 2: x = 1 (simple positive case)
def test2_x : Int := 1
def test2_Expected : Int × Int := (2, 4)

-- Test case 3: x = -1 (simple negative case)
def test3_x : Int := -1
def test3_Expected : Int × Int := (-2, -4)

-- Test case 4: x = 10 (larger positive value)
def test4_x : Int := 10
def test4_Expected : Int × Int := (20, 40)

-- Test case 5: x = -5 (negative value)
def test5_x : Int := -5
def test5_Expected : Int × Int := (-10, -20)

-- Test case 6: x = 100 (larger value to test scaling)
def test6_x : Int := 100
def test6_Expected : Int × Int := (200, 400)

-- Test case 7: x = -100 (larger negative value)
def test7_x : Int := -100
def test7_Expected : Int × Int := (-200, -400)

-- Recommend to validate: 1, 2, 3

end TestCases

