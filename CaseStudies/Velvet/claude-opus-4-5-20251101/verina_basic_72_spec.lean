import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    append: Append an integer to the end of an array of integers
    Natural language breakdown:
    1. We have an input array `a` of integers and a single integer `b`
    2. We need to construct a new array that contains all elements of `a` followed by `b`
    3. The resulting array should have size equal to `a.size + 1`
    4. All original elements from `a` should be preserved in their original positions
    5. The element `b` should be placed at the last position (index `a.size`)
    6. The result's list representation equals `a.toList ++ [b]`
    7. Edge cases: empty input array should result in a single-element array containing `b`
-/

section Specs

-- Precondition: No special preconditions needed
def precondition (a : Array Int) (b : Int) :=
  True

-- Postcondition: The result array has the correct size and elements
-- - The size is one more than the original array
-- - All original elements are preserved at their positions
-- - The new element is at the last position
def postcondition (a : Array Int) (b : Int) (result : Array Int) :=
  result.size = a.size + 1 ∧
  (∀ i : Nat, i < a.size → result[i]! = a[i]!) ∧
  result[a.size]! = b

end Specs

section Impl

method append (a : Array Int) (b : Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic case with non-empty array (from problem description)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Int := 4
def test1_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 2: Empty array with element 0
def test2_a : Array Int := #[]
def test2_b : Int := 0
def test2_Expected : Array Int := #[0]

-- Test case 3: Array with negative element to append
def test3_a : Array Int := #[5, 6]
def test3_b : Int := -1
def test3_Expected : Array Int := #[5, 6, -1]

-- Test case 4: Array of zeros with positive element
def test4_a : Array Int := #[0, 0, 0]
def test4_b : Int := 1
def test4_Expected : Array Int := #[0, 0, 0, 1]

-- Test case 5: Array of negative numbers with negative element
def test5_a : Array Int := #[-2, -3]
def test5_b : Int := -4
def test5_Expected : Array Int := #[-2, -3, -4]

-- Test case 6: Single element array
def test6_a : Array Int := #[42]
def test6_b : Int := 99
def test6_Expected : Array Int := #[42, 99]

-- Test case 7: Empty array with negative element
def test7_a : Array Int := #[]
def test7_b : Int := -5
def test7_Expected : Array Int := #[-5]

-- Test case 8: Large positive numbers
def test8_a : Array Int := #[1000, 2000, 3000]
def test8_b : Int := 4000
def test8_Expected : Array Int := #[1000, 2000, 3000, 4000]

-- Test case 9: Mixed positive and negative numbers
def test9_a : Array Int := #[-1, 0, 1]
def test9_b : Int := 2
def test9_Expected : Array Int := #[-1, 0, 1, 2]

-- Test case 10: Duplicate elements
def test10_a : Array Int := #[7, 7, 7]
def test10_b : Int := 7
def test10_Expected : Array Int := #[7, 7, 7, 7]

-- Recommend to validate: 1, 2, 3

end TestCases
