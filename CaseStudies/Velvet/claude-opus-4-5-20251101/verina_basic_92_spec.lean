import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    SwapArithmetic: Swap the values of two integers
    Natural language breakdown:
    1. We have two integer inputs X and Y
    2. The output is a tuple (pair) of two integers
    3. The first element of the output must equal Y (the second input)
    4. The second element of the output must equal X (the first input)
    5. There are no restrictions on input values - they can be positive, negative, or zero
    6. The function simply reverses the order of the two inputs
-/

-- No helper functions needed - this uses basic tuple construction from Lean

section Specs

-- Precondition: No restrictions on input values
def precondition (X : Int) (Y : Int) :=
  True

-- Postcondition: The result is the swapped pair (Y, X)
-- First element of result equals Y, second element equals X
def postcondition (X : Int) (Y : Int) (result : Int × Int) :=
  result.fst = Y ∧ result.snd = X

end Specs

section Impl

method SwapArithmetic (X : Int) (Y : Int)
  return (result : Int × Int)
  require precondition X Y
  ensures postcondition X Y result
  do
  pure (0, 0)  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic positive integers (example from problem)
def test1_X : Int := 3
def test1_Y : Int := 4
def test1_Expected : Int × Int := (4, 3)

-- Test case 2: Negative and positive integers
def test2_X : Int := -1
def test2_Y : Int := 10
def test2_Expected : Int × Int := (10, -1)

-- Test case 3: Both zeros
def test3_X : Int := 0
def test3_Y : Int := 0
def test3_Expected : Int × Int := (0, 0)

-- Test case 4: Larger positive integers
def test4_X : Int := 100
def test4_Y : Int := 50
def test4_Expected : Int × Int := (50, 100)

-- Test case 5: Both negative integers
def test5_X : Int := -5
def test5_Y : Int := -10
def test5_Expected : Int × Int := (-10, -5)

-- Test case 6: Same positive values
def test6_X : Int := 7
def test6_Y : Int := 7
def test6_Expected : Int × Int := (7, 7)

-- Test case 7: Zero and positive
def test7_X : Int := 0
def test7_Y : Int := 42
def test7_Expected : Int × Int := (42, 0)

-- Test case 8: Zero and negative
def test8_X : Int := -15
def test8_Y : Int := 0
def test8_Expected : Int × Int := (0, -15)

-- Test case 9: Large magnitude integers
def test9_X : Int := 1000000
def test9_Y : Int := -999999
def test9_Expected : Int × Int := (-999999, 1000000)

-- Recommend to validate: 1, 2, 5

end TestCases
