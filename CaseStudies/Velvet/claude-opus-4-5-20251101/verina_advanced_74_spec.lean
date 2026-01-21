import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- solution: Calculate the sum of squared distinct counts for all subarrays
--
-- Natural language breakdown:
-- 1. A subarray is a contiguous portion of the original list, defined by start index i and end index j where i ≤ j
-- 2. For a list of length n, there are n*(n+1)/2 subarrays total
-- 3. For each subarray, we count the number of distinct elements in it
-- 4. We then square that count
-- 5. The final result is the sum of all these squared values across all subarrays
-- 6. A subarray from index i to j (inclusive) contains elements nums[i], nums[i+1], ..., nums[j]
-- 7. The distinct count of a subarray is the cardinality of the set formed by its elements
-- 8. Example: [1, 2, 1] has subarrays:
--    - [1] (i=0,j=0): 1 distinct, 1^2 = 1
--    - [1,2] (i=0,j=1): 2 distinct, 2^2 = 4
--    - [1,2,1] (i=0,j=2): 2 distinct, 2^2 = 4
--    - [2] (i=1,j=1): 1 distinct, 1^2 = 1
--    - [2,1] (i=1,j=2): 2 distinct, 2^2 = 4
--    - [1] (i=2,j=2): 1 distinct, 1^2 = 1
--    Total = 1 + 4 + 4 + 1 + 4 + 1 = 15
-- 9. Preconditions: list length between 1 and 100, each element between 1 and 100

section Specs

-- Helper function to extract a subarray (contiguous portion) from a list
-- subarray l i j returns elements from index i to j (inclusive)
def subarray (l : List Nat) (i : Nat) (j : Nat) : List Nat :=
  (l.drop i).take (j - i + 1)

-- Helper function to count distinct elements in a list using toFinset cardinality
def distinctCount (l : List Nat) : Nat :=
  l.toFinset.card

-- Helper function to compute squared distinct count for a subarray
def squaredDistinctCount (l : List Nat) (i : Nat) (j : Nat) : Nat :=
  let sub := subarray l i j
  let d := distinctCount sub
  d * d

-- Precondition: list is non-empty, length at most 100, elements between 1 and 100
def precondition (nums : List Nat) :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)

-- Postcondition: result equals sum of squared distinct counts over all subarrays
-- A subarray is defined by indices (i, j) where 0 ≤ i ≤ j < nums.length
-- Using Finset.sum for a declarative mathematical specification
def postcondition (nums : List Nat) (result : Nat) :=
  result = (Finset.range nums.length).sum (fun i =>
           (Finset.Icc i (nums.length - 1)).sum (fun j =>
           squaredDistinctCount nums i j))

end Specs

section Impl

method solution (nums : List Nat)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Single element list
def test1_nums : List Nat := [1]
def test1_Expected : Nat := 1

-- Test case 2: All same elements
def test2_nums : List Nat := [1, 1, 1]
def test2_Expected : Nat := 6

-- Test case 3: Mixed with duplicate (example from problem)
def test3_nums : List Nat := [1, 2, 1]
def test3_Expected : Nat := 15

-- Test case 4: All distinct elements
def test4_nums : List Nat := [1, 2, 3, 4]
def test4_Expected : Nat := 50

-- Test case 5: Longer list with mixed duplicates
def test5_nums : List Nat := [1, 2, 2, 3, 1]
def test5_Expected : Nat := 62

-- Test case 6: Two elements, same
def test6_nums : List Nat := [5, 5]
def test6_Expected : Nat := 3

-- Test case 7: Two elements, different
def test7_nums : List Nat := [1, 2]
def test7_Expected : Nat := 6

-- Test case 8: Three distinct elements
def test8_nums : List Nat := [1, 2, 3]
def test8_Expected : Nat := 20

-- Test case 9: Alternating pattern
def test9_nums : List Nat := [1, 2, 1, 2]
def test9_Expected : Nat := 30

-- Test case 10: Boundary values (max element value)
def test10_nums : List Nat := [100, 1, 100]
def test10_Expected : Nat := 15

-- Recommend to validate: 1, 3, 4

end TestCases
