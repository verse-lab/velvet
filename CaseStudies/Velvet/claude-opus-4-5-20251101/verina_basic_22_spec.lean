import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- dissimilarElements: Find elements that appear in one array but not the other
-- Natural language breakdown:
-- 1. Given two arrays of integers a and b
-- 2. Find all elements that are in a but not in b, and all elements that are in b but not in a
-- 3. This is the symmetric difference of the two sets represented by the arrays
-- 4. The result should contain no duplicate elements
-- 5. The result should be sorted in ascending order
-- 6. An element x is in the result if and only if:
--    (x is in a and x is not in b) OR (x is in b and x is not in a)
-- 7. The result array must be sorted (each element is less than or equal to the next)
-- 8. The result array must have no duplicates (all elements are distinct)

section Specs

-- Helper: check if array is sorted in ascending order
def isSortedAsc (arr : Array Int) : Prop :=
  ∀ i : Nat, i + 1 < arr.size → arr[i]! ≤ arr[i + 1]!

-- Helper: check if array has no duplicates
def hasNoDuplicates (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < arr.size → j < arr.size → i ≠ j → arr[i]! ≠ arr[j]!

-- Helper: check membership in array
def inArray (arr : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = x

-- Precondition: no special requirements on input arrays
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition clauses
-- 1. Result contains exactly the symmetric difference elements
def ensures1 (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, inArray result x ↔ ((inArray a x ∧ ¬inArray b x) ∨ (inArray b x ∧ ¬inArray a x))

-- 2. Result is sorted in ascending order
def ensures2 (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  isSortedAsc result

-- 3. Result has no duplicates
def ensures3 (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  hasNoDuplicates result

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  ensures1 a b result ∧ ensures2 a b result ∧ ensures3 a b result

end Specs

section Impl

method dissimilarElements (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic example from problem (elements in one array but not the other)
def test1_a : Array Int := #[1, 2, 3, 4]
def test1_b : Array Int := #[3, 4, 5, 6]
def test1_Expected : Array Int := #[1, 2, 5, 6]

-- Test case 2: Array with duplicates in input
def test2_a : Array Int := #[1, 1, 2]
def test2_b : Array Int := #[2, 3]
def test2_Expected : Array Int := #[1, 3]

-- Test case 3: First array is empty
def test3_a : Array Int := #[]
def test3_b : Array Int := #[4, 5]
def test3_Expected : Array Int := #[4, 5]

-- Test case 4: Second array is empty
def test4_a : Array Int := #[7, 8]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[7, 8]

-- Test case 5: Both arrays have same elements (no dissimilar elements)
def test5_a : Array Int := #[1, 2, 3]
def test5_b : Array Int := #[1, 2, 3]
def test5_Expected : Array Int := #[]

-- Test case 6: Completely disjoint arrays (all elements are dissimilar)
def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[4, 5, 6]
def test6_Expected : Array Int := #[1, 2, 3, 4, 5, 6]

-- Test case 7: Arrays with negative numbers and zero
def test7_a : Array Int := #[-1, 0, 1]
def test7_b : Array Int := #[0]
def test7_Expected : Array Int := #[-1, 1]

-- Test case 8: Both arrays empty
def test8_a : Array Int := #[]
def test8_b : Array Int := #[]
def test8_Expected : Array Int := #[]

-- Test case 9: Single element arrays with same element
def test9_a : Array Int := #[5]
def test9_b : Array Int := #[5]
def test9_Expected : Array Int := #[]

-- Test case 10: Single element arrays with different elements
def test10_a : Array Int := #[3]
def test10_b : Array Int := #[7]
def test10_Expected : Array Int := #[3, 7]

-- Recommend to validate: 1, 2, 5

end TestCases
