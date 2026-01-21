import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    SwapSimultaneous: Swap two integer values and return them as a tuple
    Natural language breakdown:
    1. Given two integers X and Y as input
    2. Return a tuple (Int × Int) where the values are swapped
    3. The first element of the output tuple equals the second input (Y)
    4. The second element of the output tuple equals the first input (X)
    5. No preconditions are required - any pair of integers is valid input
    6. The result is uniquely determined by: result.fst = Y ∧ result.snd = X
-/

section Specs

-- Precondition: No restrictions on input integers
def precondition (X : Int) (Y : Int) : Prop :=
  True

-- Postcondition: The result tuple has swapped values
-- result.fst = Y (second input becomes first output)
-- result.snd = X (first input becomes second output)
def postcondition (X : Int) (Y : Int) (result : Int × Int) : Prop :=
  result.fst = Y ∧ result.snd = X

end Specs

section Impl

method SwapSimultaneous (X : Int) (Y : Int)
  return (result : Int × Int)
  require precondition X Y
  ensures postcondition X Y result
  do
  pure (0, 0)  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic positive integers (from problem example)
def test1_X : Int := 3
def test1_Y : Int := 4
def test1_Expected : Int × Int := (4, 3)

-- Test case 2: Mixed positive and negative
def test2_X : Int := -10
def test2_Y : Int := 20
def test2_Expected : Int × Int := (20, -10)

-- Test case 3: Both zeros
def test3_X : Int := 0
def test3_Y : Int := 0
def test3_Expected : Int × Int := (0, 0)

-- Test case 4: Positive and negative with larger values
def test4_X : Int := 123
def test4_Y : Int := -456
def test4_Expected : Int × Int := (-456, 123)

-- Test case 5: Both negative
def test5_X : Int := -1
def test5_Y : Int := -2
def test5_Expected : Int × Int := (-2, -1)

-- Test case 6: Same values (non-zero)
def test6_X : Int := 7
def test6_Y : Int := 7
def test6_Expected : Int × Int := (7, 7)

-- Test case 7: Zero and positive
def test7_X : Int := 0
def test7_Y : Int := 100
def test7_Expected : Int × Int := (100, 0)

-- Test case 8: Zero and negative
def test8_X : Int := -50
def test8_Y : Int := 0
def test8_Expected : Int × Int := (0, -50)

-- Test case 9: Large values
def test9_X : Int := 999999
def test9_Y : Int := -888888
def test9_Expected : Int × Int := (-888888, 999999)

-- Test case 10: Opposite signs with same absolute value
def test10_X : Int := 42
def test10_Y : Int := -42
def test10_Expected : Int × Int := (-42, 42)

-- Recommend to validate: 1, 2, 5

end TestCases
