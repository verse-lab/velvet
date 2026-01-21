import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    BinarySearch: Find the correct insertion index for a given integer in a sorted array.
    Natural language breakdown:
    1. We have a sorted array of integers in non-decreasing order
    2. We want to find the index where a key could be inserted to maintain sorted order
    3. All elements before the returned index must be strictly less than the key
    4. All elements from the returned index onwards must be greater than or equal to the key
    5. The returned index is in the range [0, array.size]
    6. If all elements are less than the key, return the array size
    7. If all elements are greater than or equal to the key, return 0
    8. This is the "lower bound" binary search - finding first position where element >= key
-/

section Specs

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: array must be sorted in non-decreasing order
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNonDecreasing a

-- Postcondition clauses
-- 1. Result is a valid index (between 0 and size inclusive)
def ensures1 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  result ≤ a.size

-- 2. All elements before the result index are strictly less than the key
def ensures2 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ∀ i : Nat, i < result → a[i]! < key

-- 3. All elements from the result index onwards are greater than or equal to the key
def ensures3 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ∀ i : Nat, result ≤ i → i < a.size → a[i]! ≥ key

def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ensures1 a key result ∧
  ensures2 a key result ∧
  ensures3 a key result

end Specs

section Impl

method BinarySearch (a : Array Int) (key : Int)
  return (result : Nat)
  require precondition a key
  ensures postcondition a key result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Key exists in array (from problem example)
def test1_a : Array Int := #[1, 3, 5, 7, 9]
def test1_key : Int := 5
def test1_Expected : Nat := 2

-- Test case 2: Key not in array, between elements
def test2_a : Array Int := #[1, 3, 5, 7, 9]
def test2_key : Int := 6
def test2_Expected : Nat := 3

-- Test case 3: Key smaller than all elements
def test3_a : Array Int := #[2, 4, 6, 8]
def test3_key : Int := 1
def test3_Expected : Nat := 0

-- Test case 4: Key larger than all elements
def test4_a : Array Int := #[2, 4, 6, 8]
def test4_key : Int := 10
def test4_Expected : Nat := 4

-- Test case 5: Array with duplicate elements, key equals duplicates
def test5_a : Array Int := #[1, 1, 1, 1]
def test5_key : Int := 1
def test5_Expected : Nat := 0

-- Test case 6: Empty array
def test6_a : Array Int := #[]
def test6_key : Int := 5
def test6_Expected : Nat := 0

-- Test case 7: Single element array, key less than element
def test7_a : Array Int := #[5]
def test7_key : Int := 3
def test7_Expected : Nat := 0

-- Test case 8: Single element array, key greater than element
def test8_a : Array Int := #[5]
def test8_key : Int := 7
def test8_Expected : Nat := 1

-- Test case 9: Single element array, key equals element
def test9_a : Array Int := #[5]
def test9_key : Int := 5
def test9_Expected : Nat := 0

-- Test case 10: Array with negative numbers
def test10_a : Array Int := #[-5, -2, 0, 3, 7]
def test10_key : Int := -1
def test10_Expected : Nat := 2

-- Recommend to validate: 1, 3, 5

end TestCases
