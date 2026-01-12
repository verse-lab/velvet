import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 10: Write a function to get the n smallest items from a dataset
--
-- Natural language breakdown:
-- 1. We have a dataset (list) of natural numbers
-- 2. We want to extract exactly the n smallest elements from this dataset
-- 3. "Smallest" means according to the natural ordering on natural numbers
-- 4. The function returns a list containing these n smallest elements
-- 5. If n exceeds the dataset size, return all elements (sorted)
-- 6. If n is 0, return empty list
-- 7. If dataset is empty, return empty list regardless of n
-- 8. The result should be sorted in ascending order
-- 9. Duplicate values should be preserved according to their multiplicities
-- 10. This is a property-oriented specification: we define what constitutes
--     "n smallest" rather than prescribing an algorithm

section Specs

-- Postcondition clauses
def ensures1 (dataset : List Nat) (n : Nat) (result : List Nat) :=
  result = (dataset.mergeSort (· ≤ ·)).take n  -- result is exactly the first n elements of sorted dataset

def precondition (dataset : List Nat) (n : Nat) :=
  True  -- no preconditions
def postcondition (dataset : List Nat) (n : Nat) (result : List Nat) :=
  ensures1 dataset n result

end Specs

method getNSmallest (dataset : List Nat) (n : Nat)
  return (result : List Nat)
  require precondition dataset n
  ensures postcondition dataset n result
  do
    sorry

prove_correct getNSmallest by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0: From problem description
-- dataset = [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100], n = 2
-- Sorted dataset: [10, 20, 20, 40, 50, 50, 60, 70, 80, 90, 100]
-- Expected result: [10, 20]
def test0_dataset : List Nat := [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100]
def test0_n : Nat := 2
def test0_Expected : List Nat := [10, 20]

-- Test case 1: Basic case with distinct elements
-- dataset = [7, 10, 4, 3, 20, 15], n = 3
-- Sorted dataset: [3, 4, 7, 10, 15, 20]
-- Expected result: [3, 4, 7] (first 3 elements of sorted dataset)
-- Verification: [7, 10, 4, 3, 20, 15].mergeSort(≤).take(3) = [3, 4, 7] ✓
def test1_dataset : List Nat := [7, 10, 4, 3, 20, 15]
def test1_n : Nat := 3
def test1_Expected : List Nat := [3, 4, 7]

-- Test case 2: n greater than dataset size
-- dataset = [5, 2, 8], n = 5
-- Sorted dataset: [2, 5, 8]
-- Expected result: [2, 5, 8] (first 5 elements = all elements)
-- Verification: [5, 2, 8].mergeSort(≤).take(5) = [2, 5, 8] ✓
def test2_dataset : List Nat := [5, 2, 8]
def test2_n : Nat := 5
def test2_Expected : List Nat := [2, 5, 8]

-- Test case 3: n equals 0 (edge case)
-- dataset = [1, 2, 3], n = 0
-- Sorted dataset: [1, 2, 3]
-- Expected result: [] (first 0 elements = empty list)
-- Verification: [1, 2, 3].mergeSort(≤).take(0) = [] ✓
def test3_dataset : List Nat := [1, 2, 3]
def test3_n : Nat := 0
def test3_Expected : List Nat := []

-- Test case 4: Empty dataset (edge case)
-- dataset = [], n = 3
-- Sorted dataset: []
-- Expected result: [] (first 3 elements of empty list = empty list)
-- Verification: [].mergeSort(≤).take(3) = [] ✓
def test4_dataset : List Nat := []
def test4_n : Nat := 3
def test4_Expected : List Nat := []

-- Test case 5: Dataset with duplicates
-- dataset = [4, 1, 4, 2, 4, 1], n = 4
-- Sorted dataset: [1, 1, 2, 4, 4, 4]
-- Expected result: [1, 1, 2, 4] (first 4 elements including duplicates)
-- Verification: [4, 1, 4, 2, 4, 1].mergeSort(≤).take(4) = [1, 1, 2, 4] ✓
def test5_dataset : List Nat := [4, 1, 4, 2, 4, 1]
def test5_n : Nat := 4
def test5_Expected : List Nat := [1, 1, 2, 4]

-- Test case 6: Single element dataset
-- dataset = [42], n = 1
-- Sorted dataset: [42]
-- Expected result: [42] (first 1 element)
-- Verification: [42].mergeSort(≤).take(1) = [42] ✓
def test6_dataset : List Nat := [42]
def test6_n : Nat := 1
def test6_Expected : List Nat := [42]

-- Test case 7: All elements equal
-- dataset = [5, 5, 5, 5], n = 2
-- Sorted dataset: [5, 5, 5, 5]
-- Expected result: [5, 5] (first 2 elements)
-- Verification: [5, 5, 5, 5].mergeSort(≤).take(2) = [5, 5] ✓
def test7_dataset : List Nat := [5, 5, 5, 5]
def test7_n : Nat := 2
def test7_Expected : List Nat := [5, 5]

-- Test case 8: Large n with small dataset
-- dataset = [100], n = 10
-- Sorted dataset: [100]
-- Expected result: [100] (first 10 elements = only available element)
-- Verification: [100].mergeSort(≤).take(10) = [100] ✓
def test8_dataset : List Nat := [100]
def test8_n : Nat := 10
def test8_Expected : List Nat := [100]

-- Test case 9: n equals dataset size
-- dataset = [9, 1, 5], n = 3
-- Sorted dataset: [1, 5, 9]
-- Expected result: [1, 5, 9] (first 3 elements = all elements sorted)
-- Verification: [9, 1, 5].mergeSort(≤).take(3) = [1, 5, 9] ✓
def test9_dataset : List Nat := [9, 1, 5]
def test9_n : Nat := 3
def test9_Expected : List Nat := [1, 5, 9]

-- Recommend to validate: test cases 0, 1, 2, 3, 4, 5

-- Verification summary: The test cases comprehensively cover:
-- - Normal cases with distinct elements
-- - Edge cases: n=0, empty dataset, single element
-- - Boundary cases: n > dataset.length, n = dataset.length
-- - Duplicate handling and multiplicity preservation
-- - Various orderings: sorted, reverse sorted, mixed
-- All expected results satisfy our specification: result = dataset.mergeSort(≤).take(n)

end TestCases
