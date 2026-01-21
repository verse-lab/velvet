import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Swap: Swap two integer values and return them as a pair
    Natural language breakdown:
    1. We have two input integers X and Y
    2. The function returns a pair (Int × Int)
    3. The first element of the result pair must equal the second input (Y)
    4. The second element of the result pair must equal the first input (X)
    5. There are no preconditions - any two integers can be swapped
    6. The operation is symmetric: swapping (a, b) gives (b, a)
    7. Edge cases include: identical values, zero values, negative values
-/

section Specs

-- No helper functions needed - this uses basic product type operations

-- Precondition: no restrictions on input integers
def precondition (X : Int) (Y : Int) :=
  True

-- Postcondition: the result is a pair where first element is Y and second is X
def postcondition (X : Int) (Y : Int) (result : Int × Int) :=
  result.fst = Y ∧ result.snd = X

end Specs

section Impl

method Swap (X : Int) (Y : Int)
  return (result : Int × Int)
  require precondition X Y
  ensures postcondition X Y result
  do
  pure (0, 0)

end Impl

section TestCases

-- Test case 1: Basic swap of two different positive integers
def test1_X : Int := 1
def test1_Y : Int := 2
def test1_Expected : Int × Int := (2, 1)

-- Test case 2: Swap of two zeros
def test2_X : Int := 0
def test2_Y : Int := 0
def test2_Expected : Int × Int := (0, 0)

-- Test case 3: Swap with negative and positive integers
def test3_X : Int := -1
def test3_Y : Int := 5
def test3_Expected : Int × Int := (5, -1)

-- Test case 4: Swap with positive and negative (opposite signs, same magnitude)
def test4_X : Int := 100
def test4_Y : Int := -100
def test4_Expected : Int × Int := (-100, 100)

-- Test case 5: Swap of two identical values
def test5_X : Int := 42
def test5_Y : Int := 42
def test5_Expected : Int × Int := (42, 42)

-- Test case 6: Swap with zero and positive
def test6_X : Int := 0
def test6_Y : Int := 7
def test6_Expected : Int × Int := (7, 0)

-- Test case 7: Swap with zero and negative
def test7_X : Int := -5
def test7_Y : Int := 0
def test7_Expected : Int × Int := (0, -5)

-- Test case 8: Swap of two negative integers
def test8_X : Int := -10
def test8_Y : Int := -20
def test8_Expected : Int × Int := (-20, -10)

-- Test case 9: Swap with large positive integers
def test9_X : Int := 999999
def test9_Y : Int := 1000000
def test9_Expected : Int × Int := (1000000, 999999)

-- Test case 10: Swap with large negative integers
def test10_X : Int := -999999
def test10_Y : Int := -1000000
def test10_Expected : Int × Int := (-1000000, -999999)

-- Recommend to validate: 1, 3, 5

end TestCases
