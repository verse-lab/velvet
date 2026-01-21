import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    CountLessThan: Count how many elements in an array are less than a given threshold
    Natural language breakdown:
    1. We are given an array of integers (which may be empty or non-empty)
    2. We are given an integer threshold for comparison
    3. We need to count how many elements in the array are strictly less than the threshold
    4. The result is a natural number (Nat) representing this count
    5. Edge cases:
       - Empty array: count = 0
       - All elements less than threshold: count = array size
       - No elements less than threshold: count = 0
       - Mixed case: count equals number of elements below threshold
    6. The count can be computed using Array.countP with predicate (· < threshold)
-/

section Specs

-- Precondition: No restrictions on input
def precondition (numbers : Array Int) (threshold : Int) :=
  True

-- Postcondition: result equals the count of elements less than threshold
-- Using Array.countP which counts elements satisfying a predicate
def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) :=
  result = numbers.countP (· < threshold)

end Specs

section Impl

method CountLessThan (numbers : Array Int) (threshold : Int)
  return (result : Nat)
  require precondition numbers threshold
  ensures postcondition numbers threshold result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Basic case with elements both above and below threshold
def test1_numbers : Array Int := #[1, 2, 3, 4, 5]
def test1_threshold : Int := 3
def test1_Expected : Nat := 2

-- Test case 2: Empty array
def test2_numbers : Array Int := #[]
def test2_threshold : Int := 10
def test2_Expected : Nat := 0

-- Test case 3: Array with negative numbers and zero threshold
def test3_numbers : Array Int := #[-1, 0, 1]
def test3_threshold : Int := 0
def test3_Expected : Nat := 1

-- Test case 4: Unsorted array with mixed values
def test4_numbers : Array Int := #[5, 6, 7, 2, 1]
def test4_threshold : Int := 5
def test4_Expected : Nat := 2

-- Test case 5: All elements equal to threshold (none less than)
def test5_numbers : Array Int := #[3, 3, 3, 3]
def test5_threshold : Int := 3
def test5_Expected : Nat := 0

-- Test case 6: All elements less than threshold
def test6_numbers : Array Int := #[1, 2, 3, 4, 5]
def test6_threshold : Int := 10
def test6_Expected : Nat := 5

-- Test case 7: All elements greater than or equal to threshold
def test7_numbers : Array Int := #[10, 20, 30]
def test7_threshold : Int := 5
def test7_Expected : Nat := 0

-- Test case 8: Single element less than threshold
def test8_numbers : Array Int := #[5]
def test8_threshold : Int := 10
def test8_Expected : Nat := 1

-- Test case 9: Single element not less than threshold
def test9_numbers : Array Int := #[10]
def test9_threshold : Int := 5
def test9_Expected : Nat := 0

-- Test case 10: Array with negative threshold
def test10_numbers : Array Int := #[-5, -3, -1, 0, 2]
def test10_threshold : Int := -2
def test10_Expected : Nat := 2

-- Recommend to validate: 1, 2, 3

end TestCases
