import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    BubbleSort: Sort an array of integers in non-decreasing order
    Natural language breakdown:
    1. We have an input array of integers (can be empty or non-empty)
    2. The output must be sorted in non-decreasing order
    3. For any indices i < j, the element at index i must be less than or equal to element at index j
    4. The output must have the same size as the input
    5. The output must be a permutation of the input (same multiset of elements)
    6. Empty arrays should return empty arrays
    7. Single element arrays are already sorted
    8. Arrays with duplicate elements must preserve all duplicates
-/

section Specs

-- Helper function: check if array is sorted in non-decreasing order
def isSortedArray (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper function: check if two arrays are permutations of each other
-- Using List.Perm via toList
def isPermutationArray (arr1 arr2 : Array Int) : Prop :=
  arr1.toList.Perm arr2.toList

-- Precondition: no restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition clauses
-- 1. Result is sorted in non-decreasing order
def ensures1 (a : Array Int) (result : Array Int) : Prop :=
  isSortedArray result

-- 2. Result is a permutation of input (preserves multiset and implies same size)
def ensures2 (a : Array Int) (result : Array Int) : Prop :=
  isPermutationArray a result

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  ensures1 a result ∧
  ensures2 a result

end Specs

section Impl

method BubbleSort (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Reverse sorted array (from problem description)
def test1_a : Array Int := #[5, 4, 3, 2, 1]
def test1_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 2: Already sorted array
def test2_a : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 3: Array with duplicates
def test3_a : Array Int := #[3, 1, 2, 1, 5]
def test3_Expected : Array Int := #[1, 1, 2, 3, 5]

-- Test case 4: Single element array
def test4_a : Array Int := #[10]
def test4_Expected : Array Int := #[10]

-- Test case 5: Array with multiple duplicates
def test5_a : Array Int := #[4, 4, 4, 2, 2, 8]
def test5_Expected : Array Int := #[2, 2, 4, 4, 4, 8]

-- Test case 6: Empty array
def test6_a : Array Int := #[]
def test6_Expected : Array Int := #[]

-- Test case 7: Array with negative numbers
def test7_a : Array Int := #[-3, 1, -5, 2, 0]
def test7_Expected : Array Int := #[-5, -3, 0, 1, 2]

-- Test case 8: Array with all same elements
def test8_a : Array Int := #[7, 7, 7, 7]
def test8_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 9: Two element array in wrong order
def test9_a : Array Int := #[9, 1]
def test9_Expected : Array Int := #[1, 9]

-- Test case 10: Large range of values
def test10_a : Array Int := #[100, -100, 0, 50, -50]
def test10_Expected : Array Int := #[-100, -50, 0, 50, 100]

-- Recommend to validate: 1, 3, 5

end TestCases
