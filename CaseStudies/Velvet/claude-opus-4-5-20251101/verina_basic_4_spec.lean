import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- kthElement: Find the kth element in an array using 1-based indexing
--
-- Natural language breakdown:
-- 1. We are given an array of integers and a position k (1-based index)
-- 2. The first element is at position 1, second at position 2, etc.
-- 3. We need to return the element at position k
-- 4. To convert 1-based to 0-based indexing: index = k - 1
-- 5. Preconditions:
--    a. The array must be non-empty (arr.size > 0)
--    b. k must be valid: 1 ≤ k ≤ arr.size
-- 6. The result is the element at index (k - 1) in 0-based indexing
-- 7. This is a direct array access operation after index conversion

section Specs

-- Precondition: array is non-empty and k is a valid 1-based index
def precondition (arr : Array Int) (k : Nat) : Prop :=
  arr.size > 0 ∧ k ≥ 1 ∧ k ≤ arr.size

-- Postcondition: result is the element at 0-based index (k - 1)
def postcondition (arr : Array Int) (k : Nat) (result : Int) : Prop :=
  result = arr[k - 1]!

end Specs

section Impl

method kthElement (arr : Array Int) (k : Nat)
  return (result : Int)
  require precondition arr k
  ensures postcondition arr k result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: First element of array [10, 20, 30, 40, 50]
def test1_arr : Array Int := #[10, 20, 30, 40, 50]
def test1_k : Nat := 1
def test1_Expected : Int := 10

-- Test case 2: Middle element (3rd) of array [10, 20, 30, 40, 50]
def test2_arr : Array Int := #[10, 20, 30, 40, 50]
def test2_k : Nat := 3
def test2_Expected : Int := 30

-- Test case 3: Last element (5th) of array [10, 20, 30, 40, 50]
def test3_arr : Array Int := #[10, 20, 30, 40, 50]
def test3_k : Nat := 5
def test3_Expected : Int := 50

-- Test case 4: Single element array
def test4_arr : Array Int := #[5]
def test4_k : Nat := 1
def test4_Expected : Int := 5

-- Test case 5: Last element of small array [1, 2, 3]
def test5_arr : Array Int := #[1, 2, 3]
def test5_k : Nat := 3
def test5_Expected : Int := 3

-- Test case 6: Middle element of small array [1, 2, 3]
def test6_arr : Array Int := #[1, 2, 3]
def test6_k : Nat := 2
def test6_Expected : Int := 2

-- Test case 7: Array with repeated elements
def test7_arr : Array Int := #[9, 9, 9]
def test7_k : Nat := 2
def test7_Expected : Int := 9

-- Test case 8: Array with negative numbers, first element
def test8_arr : Array Int := #[0, -1, -2]
def test8_k : Nat := 1
def test8_Expected : Int := 0

-- Test case 9: Array with negative numbers, second element
def test9_arr : Array Int := #[0, -1, -2]
def test9_k : Nat := 2
def test9_Expected : Int := -1

-- Test case 10: Array with negative numbers, last element
def test10_arr : Array Int := #[0, -1, -2]
def test10_k : Nat := 3
def test10_Expected : Int := -2

-- Recommend to validate: 1, 2, 4

end TestCases
