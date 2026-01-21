import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    SelectionSort: Sort an array of integers into non-decreasing order
    Natural language breakdown:
    1. We have an input array of integers
    2. The output must be sorted in non-decreasing order (each element ≤ next element)
    3. The output must be a permutation of the input (same elements with same multiplicities)
    4. Permutation can be expressed using List.Perm or count equality
    5. Sorted property: for all valid indices i and j where i < j, we have result[i] ≤ result[j]
    6. Edge cases:
       - Empty array: returns empty array (trivially sorted and a permutation)
       - Single element: returns same array (trivially sorted)
       - Already sorted array: returns same array
       - Reverse sorted array: returns reversed array
       - Array with duplicates: preserves all duplicates
       - Array with negative numbers: handles correctly
-/

section Specs

-- Helper: Check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: Check if two arrays are permutations of each other using count equality
def isPermutation (a b : Array Int) : Prop :=
  a.size = b.size ∧ ∀ x : Int, a.toList.count x = b.toList.count x

-- Precondition: no constraints needed, any array is valid input
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  isSortedNonDecreasing result ∧ isPermutation a result

end Specs

section Impl

method SelectionSort (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
    pure #[]

end Impl

section TestCases

-- Test case 1: Basic unsorted array (from problem description)
def test1_a : Array Int := #[3, 1, 2]
def test1_Expected : Array Int := #[1, 2, 3]

-- Test case 2: Single element array
def test2_a : Array Int := #[0]
def test2_Expected : Array Int := #[0]

-- Test case 3: Reverse sorted array
def test3_a : Array Int := #[5, 4, 3, 2, 1]
def test3_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 4: Array with duplicates
def test4_a : Array Int := #[2, 2, 1, 4]
def test4_Expected : Array Int := #[1, 2, 2, 4]

-- Test case 5: Array with negative numbers
def test5_a : Array Int := #[10, -5, 0, 3]
def test5_Expected : Array Int := #[-5, 0, 3, 10]

-- Test case 6: Empty array
def test6_a : Array Int := #[]
def test6_Expected : Array Int := #[]

-- Test case 7: Already sorted array
def test7_a : Array Int := #[1, 2, 3, 4, 5]
def test7_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 8: All same elements
def test8_a : Array Int := #[7, 7, 7, 7]
def test8_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 9: Two elements unsorted
def test9_a : Array Int := #[5, 3]
def test9_Expected : Array Int := #[3, 5]

-- Test case 10: Array with large negative and positive values
def test10_a : Array Int := #[-100, 50, -50, 100, 0]
def test10_Expected : Array Int := #[-100, -50, 0, 50, 100]

-- Recommend to validate: 1, 3, 5

end TestCases
