import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Triple: Compute three times the given integer
    Natural language breakdown:
    1. We are given an integer x as input
    2. The goal is to compute the product of x and 3
    3. The result should equal 3 * x
    4. The implementation may use different branches based on x < 18 or x >= 18,
       but both branches must produce the same result: 3 * x
    5. The postcondition simply states that result = 3 * x
    6. No preconditions are needed since multiplication is defined for all integers
-/

section Specs

-- No helper functions needed - we use standard integer multiplication from Mathlib

-- Precondition: no restrictions on input
def precondition (x : Int) :=
  True

-- Postcondition: result equals three times the input
def postcondition (x : Int) (result : Int) :=
  result = 3 * x

end Specs

section Impl

method Triple (x : Int)
  return (result : Int)
  require precondition x
  ensures postcondition x result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Positive integer less than 18
def test1_x : Int := 10
def test1_Expected : Int := 30

-- Test case 2: Exactly at boundary value 18
def test2_x : Int := 18
def test2_Expected : Int := 54

-- Test case 3: Zero case
def test3_x : Int := 0
def test3_Expected : Int := 0

-- Test case 4: Negative integer
def test4_x : Int := -5
def test4_Expected : Int := -15

-- Test case 5: Positive integer greater than 18
def test5_x : Int := 25
def test5_Expected : Int := 75

-- Test case 6: Small positive integer
def test6_x : Int := 1
def test6_Expected : Int := 3

-- Test case 7: Small negative integer
def test7_x : Int := -1
def test7_Expected : Int := -3

-- Test case 8: Value just below boundary
def test8_x : Int := 17
def test8_Expected : Int := 51

-- Test case 9: Large positive integer
def test9_x : Int := 100
def test9_Expected : Int := 300

-- Test case 10: Large negative integer
def test10_x : Int := -100
def test10_Expected : Int := -300

-- Recommend to validate: 1, 3, 4

end TestCases
