import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSorted: Check whether an array of integers is sorted in non-decreasing order
    Natural language breakdown:
    1. We have an input array of integers
    2. The array is sorted in non-decreasing order if for all valid indices i < j,
       the element at index i is less than or equal to the element at index j
    3. Equivalently, for all adjacent pairs of elements, the first is ≤ the second
    4. The function should return true if the array is sorted, false otherwise
    5. Edge case: An empty array is considered sorted (vacuously true)
    6. Edge case: A single-element array is considered sorted
    7. An array with all equal elements is considered sorted (non-decreasing allows equality)
    8. Using Array.Pairwise with (· ≤ ·) captures this property directly
-/

section Specs

-- Using Mathlib's Array.Pairwise to define sorted property
-- Array.Pairwise R as means all pairs (i, j) with i < j satisfy R as[i] as[j]

-- The sorted property: all pairs of elements with earlier index ≤ later index
def isSortedProp (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i < j → a[i]! ≤ a[j]!

-- Precondition: No restrictions on input
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is true iff array is sorted in non-decreasing order
def postcondition (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ isSortedProp a

end Specs

section Impl

method isSorted (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure true

end Impl

section TestCases

-- Test case 1: Strictly increasing array - sorted
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: Strictly decreasing array - not sorted
def test2_a : Array Int := #[5, 4, 3, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: Unsorted array with elements out of order in the middle
def test3_a : Array Int := #[1, 3, 2, 4, 5]
def test3_Expected : Bool := false

-- Test case 4: Empty array - sorted (vacuously true)
def test4_a : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Single element array - sorted
def test5_a : Array Int := #[10]
def test5_Expected : Bool := true

-- Test case 6: All equal elements - sorted (non-decreasing allows equality)
def test6_a : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: Non-decreasing with some equal adjacent elements
def test7_a : Array Int := #[1, 2, 2, 3]
def test7_Expected : Bool := true

-- Test case 8: Two elements sorted
def test8_a : Array Int := #[1, 5]
def test8_Expected : Bool := true

-- Test case 9: Two elements not sorted
def test9_a : Array Int := #[5, 1]
def test9_Expected : Bool := false

-- Test case 10: Negative numbers sorted
def test10_a : Array Int := #[-5, -3, 0, 2, 7]
def test10_Expected : Bool := true

-- Recommend to validate: 1, 4, 6

end TestCases
