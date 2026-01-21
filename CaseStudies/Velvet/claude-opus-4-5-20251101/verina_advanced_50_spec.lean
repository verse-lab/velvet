import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- mergeSorted: Merge two sorted arrays of natural numbers into a single sorted array
--
-- Natural language breakdown:
-- 1. We have two input arrays a1 and a2, both containing natural numbers
-- 2. Both input arrays must be sorted in non-decreasing order (precondition)
-- 3. The output array must contain all elements from both input arrays
-- 4. Each element appears exactly as many times as it appears in a1 plus a2 combined
-- 5. The output array must also be sorted in non-decreasing order
-- 6. The size of the output equals the sum of sizes of the two input arrays
-- 7. This is a merge operation that preserves all elements (including duplicates)

section Specs

-- Helper: check if an array is sorted in non-decreasing order
def isSortedArray (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: count occurrences of a value in an array
def countInArray (arr : Array Nat) (v : Nat) : Nat :=
  arr.toList.count v

-- Precondition: both input arrays must be sorted
def precondition (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  isSortedArray a1 ∧ isSortedArray a2

-- Postcondition clauses
-- 1. The result size equals the sum of input sizes
def ensures1 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  result.size = a1.size + a2.size

-- 2. The result is sorted in non-decreasing order
def ensures2 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  isSortedArray result

-- 3. Every element's count in result equals its count in a1 plus its count in a2
def ensures3 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ∀ v : Nat, countInArray result v = countInArray a1 v + countInArray a2 v

def postcondition (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ensures1 a1 a2 result ∧
  ensures2 a1 a2 result ∧
  ensures3 a1 a2 result

end Specs

section Impl

method mergeSorted (a1 : Array Nat) (a2 : Array Nat)
  return (result : Array Nat)
  require precondition a1 a2
  ensures postcondition a1 a2 result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic merge of two interleaved arrays (from problem)
def test1_a1 : Array Nat := #[1, 3, 5]
def test1_a2 : Array Nat := #[2, 4, 6]
def test1_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

-- Test case 2: First array empty
def test2_a1 : Array Nat := #[]
def test2_a2 : Array Nat := #[1, 2, 3]
def test2_Expected : Array Nat := #[1, 2, 3]

-- Test case 3: Second array empty
def test3_a1 : Array Nat := #[1, 2, 3]
def test3_a2 : Array Nat := #[]
def test3_Expected : Array Nat := #[1, 2, 3]

-- Test case 4: Both arrays empty
def test4_a1 : Array Nat := #[]
def test4_a2 : Array Nat := #[]
def test4_Expected : Array Nat := #[]

-- Test case 5: Arrays with duplicate elements
def test5_a1 : Array Nat := #[1, 1, 2]
def test5_a2 : Array Nat := #[1, 2, 2]
def test5_Expected : Array Nat := #[1, 1, 1, 2, 2, 2]

-- Test case 6: Arrays with interleaved ranges
def test6_a1 : Array Nat := #[10, 20, 30]
def test6_a2 : Array Nat := #[5, 15, 25]
def test6_Expected : Array Nat := #[5, 10, 15, 20, 25, 30]

-- Test case 7: Longer arrays with alternating elements
def test7_a1 : Array Nat := #[1, 3, 5, 7, 9]
def test7_a2 : Array Nat := #[2, 4, 6, 8, 10]
def test7_Expected : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

-- Test case 8: Arrays with all same elements
def test8_a1 : Array Nat := #[5, 5, 5]
def test8_a2 : Array Nat := #[5, 5, 5]
def test8_Expected : Array Nat := #[5, 5, 5, 5, 5, 5]

-- Test case 9: Single element arrays
def test9_a1 : Array Nat := #[1]
def test9_a2 : Array Nat := #[2]
def test9_Expected : Array Nat := #[1, 2]

-- Test case 10: One array completely before the other
def test10_a1 : Array Nat := #[1, 2, 3]
def test10_a2 : Array Nat := #[4, 5, 6]
def test10_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

-- Recommend to validate: 1, 5, 6

end TestCases
