import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Triple: Compute three times a given integer
    Natural language breakdown:
    1. We are given a single integer x as input
    2. We need to compute the product of x and 3
    3. The result should be exactly 3 * x
    4. This works for positive, negative, and zero values
    5. No preconditions are required (all integers are valid inputs)
-/

section Specs

-- No custom helper functions needed - we use standard integer multiplication

-- Precondition: no restrictions on input
def precondition (x : Int) : Prop :=
  True

-- Postcondition: result equals three times the input
def postcondition (x : Int) (result : Int) : Prop :=
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

-- Test case 1: Zero input (edge case)
def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: Small positive integer
def test2_x : Int := 2
def test2_Expected : Int := 6

-- Test case 3: Negative integer
def test3_x : Int := -4
def test3_Expected : Int := -12

-- Test case 4: Larger positive integer
def test4_x : Int := 10
def test4_Expected : Int := 30

-- Test case 5: Small negative integer
def test5_x : Int := -1
def test5_Expected : Int := -3

-- Test case 6: Positive one (identity-like case)
def test6_x : Int := 1
def test6_Expected : Int := 3

-- Test case 7: Large positive integer
def test7_x : Int := 100
def test7_Expected : Int := 300

-- Test case 8: Large negative integer
def test8_x : Int := -50
def test8_Expected : Int := -150

-- Recommend to validate: 1, 2, 3

end TestCases
