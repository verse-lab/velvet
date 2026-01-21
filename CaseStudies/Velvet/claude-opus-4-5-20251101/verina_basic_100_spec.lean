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
    1. We are given an integer x as input
    2. The output should be three times the input integer (3 * x)
    3. When x = 0, the output is 0
    4. The operation is equivalent to x + 2 * x = 3 * x
    5. Works for positive, negative, and zero integers
    6. No preconditions needed - any integer is valid input
-/

section Specs

-- Precondition: No restrictions on the input integer
def precondition (x : Int) :=
  True

-- Postcondition: The result must equal three times the input
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

-- Test case 1: Zero input (from problem description)
def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: Positive integer 1
def test2_x : Int := 1
def test2_Expected : Int := 3

-- Test case 3: Negative integer -2
def test3_x : Int := -2
def test3_Expected : Int := -6

-- Test case 4: Larger positive integer 10
def test4_x : Int := 10
def test4_Expected : Int := 30

-- Test case 5: Negative integer -5
def test5_x : Int := -5
def test5_Expected : Int := -15

-- Test case 6: Large positive integer
def test6_x : Int := 100
def test6_Expected : Int := 300

-- Test case 7: Large negative integer
def test7_x : Int := -100
def test7_Expected : Int := -300

-- Test case 8: Small positive integer 2
def test8_x : Int := 2
def test8_Expected : Int := 6

-- Test case 9: Negative one
def test9_x : Int := -1
def test9_Expected : Int := -3

-- Test case 10: Moderately large integer
def test10_x : Int := 33
def test10_Expected : Int := 99

-- Recommend to validate: 1, 2, 3

end TestCases
