import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MultipleReturns: Given two integers, compute their sum and difference as a tuple
    Natural language breakdown:
    1. We are given two integers x and y
    2. The first output is the sum x + y
    3. The second output is the difference x - y
    4. The result is a tuple (sum, difference)
    5. There are no constraints on the input integers
    6. The result is uniquely determined by the inputs
-/

section Specs

-- No helper functions needed - using built-in Int.add and Int.sub via + and - operators

def precondition (x : Int) (y : Int) :=
  True  -- no preconditions

def postcondition (x : Int) (y : Int) (result : Int × Int) :=
  result.1 = x + y ∧ result.2 = x - y

end Specs

section Impl

method MultipleReturns (x : Int) (y : Int)
  return (result : Int × Int)
  require precondition x y
  ensures postcondition x y result
  do
  pure (0, 0)  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic positive integers (example from problem)
def test1_x : Int := 3
def test1_y : Int := 2
def test1_Expected : Int × Int := (5, 1)

-- Test case 2: Mixed signs - negative x, positive y
def test2_x : Int := -2
def test2_y : Int := 3
def test2_Expected : Int × Int := (1, -5)

-- Test case 3: Both zeros
def test3_x : Int := 0
def test3_y : Int := 0
def test3_Expected : Int × Int := (0, 0)

-- Test case 4: Larger positive integers
def test4_x : Int := 10
def test4_y : Int := 5
def test4_Expected : Int × Int := (15, 5)

-- Test case 5: Both negative integers
def test5_x : Int := -5
def test5_y : Int := -10
def test5_Expected : Int × Int := (-15, 5)

-- Test case 6: Zero and positive
def test6_x : Int := 0
def test6_y : Int := 7
def test6_Expected : Int × Int := (7, -7)

-- Test case 7: Positive and zero
def test7_x : Int := 7
def test7_y : Int := 0
def test7_Expected : Int × Int := (7, 7)

-- Test case 8: Equal values
def test8_x : Int := 5
def test8_y : Int := 5
def test8_Expected : Int × Int := (10, 0)

-- Test case 9: Opposite values
def test9_x : Int := 8
def test9_y : Int := -8
def test9_Expected : Int × Int := (0, 16)

-- Test case 10: Large negative values
def test10_x : Int := -100
def test10_y : Int := -50
def test10_Expected : Int × Int := (-150, -50)

-- Recommend to validate: 1, 2, 5

end TestCases
