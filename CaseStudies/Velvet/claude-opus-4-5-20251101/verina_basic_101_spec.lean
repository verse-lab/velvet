import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Triple: Compute the triple of a given integer
    Natural language breakdown:
    1. We are given an integer x as input
    2. We need to compute the result that is exactly three times the input value
    3. The output should satisfy: result = 3 * x
    4. This is a simple arithmetic operation using integer multiplication
    5. The specification uses the standard integer multiplication from Mathlib
    6. Edge cases include: zero (3 * 0 = 0), positive numbers, negative numbers
-/

section Specs

-- Precondition: no restrictions on input integer
def precondition (x : Int) : Prop :=
  True

-- Postcondition: result must be exactly 3 times the input
def postcondition (x : Int) (result : Int) : Prop :=
  result = 3 * x

end Specs

section Impl

method Triple (x : Int)
  return (result : Int)
  require precondition x
  ensures postcondition x result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Zero input (edge case)
def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: Positive one
def test2_x : Int := 1
def test2_Expected : Int := 3

-- Test case 3: Negative one
def test3_x : Int := -1
def test3_Expected : Int := -3

-- Test case 4: Small positive number
def test4_x : Int := 5
def test4_Expected : Int := 15

-- Test case 5: Small negative number
def test5_x : Int := -10
def test5_Expected : Int := -30

-- Test case 6: Larger positive number
def test6_x : Int := 100
def test6_Expected : Int := 300

-- Test case 7: Larger negative number
def test7_x : Int := -50
def test7_Expected : Int := -150

-- Test case 8: Another positive value
def test8_x : Int := 7
def test8_Expected : Int := 21

-- Test case 9: Another negative value
def test9_x : Int := -3
def test9_Expected : Int := -9

-- Test case 10: Large value
def test10_x : Int := 1000
def test10_Expected : Int := 3000

-- Recommend to validate: 1, 2, 3

end TestCases
