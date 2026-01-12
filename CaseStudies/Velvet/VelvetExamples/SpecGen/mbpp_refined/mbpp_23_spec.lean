import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MaxArraySum: Find the maximum sum of elements of array in an array of arrays
    Natural language breakdown:
    1. We have an array of arrays (2D structure) where each inner array contains integers
    2. For each inner array, we can compute the sum of all its elements
    3. We want to find the maximum sum among all these inner array sums
    4. The function should return this maximum sum value
    5. Edge cases to consider:
       - Empty outer array: Since there are no inner arrays, there is no well-defined maximum.
         This case should be handled by a precondition requiring the outer array to be non-empty.
       - Outer array with at least one inner array: The result should be the maximum sum.
         Note: An empty inner array has sum 0, which is a valid sum to consider.
    6. Key properties:
       - The result must equal the sum of at least one inner array (achievability)
       - The result must be greater than or equal to the sum of every inner array (maximality)
    7. This is a property-oriented specification: we specify what the maximum sum must satisfy,
       not how to compute it
-/

-- Helper Functions

-- Helper function to compute the sum of integers in an array using foldl

section Specs

-- Helper Functions

def arraySum (arr: Array Int) : Int :=
  arr.foldl (· + ·) 0

def isAchievable (val: Int) (arrays: Array (Array Int)) : Prop :=
  ∃ i, i < arrays.size ∧ arraySum arrays[i]! = val

def isMaximal (val: Int) (arrays: Array (Array Int)) : Prop :=
  ∀ i, i < arrays.size → arraySum arrays[i]! ≤ val

def require1 (arrays : Array (Array Int)) :=
  arrays.size > 0  -- Need at least one inner array

-- Postcondition clauses
def ensures1 (arrays : Array (Array Int)) (maxSum : Int) :=
  isAchievable maxSum arrays
def ensures2 (arrays : Array (Array Int)) (maxSum : Int) :=
  isMaximal maxSum arrays

def precondition (arrays : Array (Array Int)) :=
  require1 arrays
def postcondition (arrays : Array (Array Int)) (maxSum : Int) :=
  ensures1 arrays maxSum ∧
  ensures2 arrays maxSum

end Specs

method MaxArraySum (arrays: Array (Array Int))
  return (maxSum: Int)
  require precondition arrays
  ensures postcondition arrays maxSum
  do
    sorry

prove_correct MaxArraySum by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_arrays : Array (Array Int) := #[#[1,2,3], #[4,5,6], #[10,11,12], #[7,8,9]]
def test1_Expected : Int := 33
-- Verification:
-- - array sums: [6, 15, 33, 24], max = 33 ✓

-- Test case 2: Simple case with positive numbers
def test2_arrays : Array (Array Int) := #[#[1, 2, 3], #[4, 5], #[6]]
def test2_Expected : Int := 9
-- Verification:
-- - array sums: [6, 9, 6], max = 9 ✓

-- Test case 3: Arrays with negative numbers
def test3_arrays : Array (Array Int) := #[#[1, 2, 3], #[-4, 5], #[6]]
def test3_Expected : Int := 6
-- Verification:
-- - array sums: [6, 1, 6], max = 6 (tie between first and third) ✓

-- Test case 4: Arrays with all negative numbers
def test4_arrays : Array (Array Int) := #[#[-1, -2], #[-3, -4, -5], #[-10]]
def test4_Expected : Int := -3
-- Verification:
-- - array sums: [-3, -12, -10], max = -3 ✓

-- Test case 5: Single inner array
def test5_arrays : Array (Array Int) := #[#[1, 2, 3, 4, 5]]
def test5_Expected : Int := 15
-- Verification:
-- - only one array, sum = 15 ✓

-- Test case 6: Arrays with empty inner arrays
def test6_arrays : Array (Array Int) := #[#[1, 2], #[], #[3, 4, 5]]
def test6_Expected : Int := 12
-- Verification:
-- - array sums: [3, 0, 12], max = 12 ✓

-- Test case 7: Large numbers
def test7_arrays : Array (Array Int) := #[#[100, 200, 300], #[1000], #[50, 50, 50, 50]]
def test7_Expected : Int := 1000
-- Verification:
-- - array sums: [600, 1000, 200], max = 1000 ✓

-- Test case 8: Mix of zeros and positives
def test8_arrays : Array (Array Int) := #[#[0, 0, 0], #[1, -1], #[2, 3]]
def test8_Expected : Int := 5
-- Verification:
-- - array sums: [0, 0, 5], max = 5 ✓

-- Test case 9: Two elements with same maximum sum
def test9_arrays : Array (Array Int) := #[#[10, 10], #[5, 5, 5, 5], #[1, 2, 3]]
def test9_Expected : Int := 20
-- Verification:
-- - array sums: [20, 20, 6], max = 20 (tie) ✓

-- Test case 10: Large array with many inner arrays
def test10_arrays : Array (Array Int) := #[#[1], #[2], #[3], #[4], #[5], #[100], #[6]]
def test10_Expected : Int := 100
-- Verification:
-- - array sums: [1, 2, 3, 4, 5, 100, 6], max = 100 ✓

-- Test case 11: Mix of positive and negative with zero sum
def test11_arrays : Array (Array Int) := #[#[5, -5], #[10, 20], #[-3, -7]]
def test11_Expected : Int := 30
-- Verification:
-- - array sums: [0, 30, -10], max = 30 ✓

-- Test case 12: Single element arrays
def test12_arrays : Array (Array Int) := #[#[42], #[-42], #[0], #[100]]
def test12_Expected : Int := 100
-- Verification:
-- - array sums: [42, -42, 0, 100], max = 100 ✓

-- Recommend to validate: test cases 1, 2, 4, 5, 6, 8
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Simple positive numbers
-- - Test 4: All negative numbers (important edge case)
-- - Test 5: Single inner array
-- - Test 6: Empty inner arrays (sum = 0)
-- - Test 8: Mix of zeros and positives

/- Rationale for Specification

   This specification captures the intended behavior through property-oriented postconditions:

   1. **Achievability** (`isAchievable maxSum arrays`):
      - States: ∃ i, i < arrays.size ∧ arraySum arrays[i]! = maxSum
      - Ensures the result is not arbitrary - it must actually be the sum of some inner array
      - This prevents returning values that are not achievable (e.g., returning 999 when no array sums to 999)

   2. **Maximality** (`isMaximal maxSum arrays`):
      - States: ∀ i, i < arrays.size → arraySum arrays[i]! ≤ maxSum
      - Ensures the result is at least as large as every inner array sum
      - This prevents returning a sum that is not maximal

   3. **Precondition** (`arrays.size > 0`):
      - Required because maximum is undefined for empty arrays
      - Ensures at least one inner array exists to compute a sum from

   4. **Why these postconditions are sufficient**:
      - Together, achievability and maximality uniquely determine the maximum sum
      - Achievability: maxSum ∈ {arraySum arrays[i]! | i < arrays.size}
      - Maximality: maxSum ≥ all elements in that set
      - Therefore: maxSum = max {arraySum arrays[i]! | i < arrays.size}

   5. **Array-specific considerations**:
      - Uses Array.foldl for computing sums (standard fold operation)
      - Uses Array.map for computing all sums (transforms each inner array to its sum)
      - Array indexing with [i]! requires bounds check (i < arrays.size)
      - Empty inner arrays (#[]) have sum 0, which is correct behavior

   6. **Why this is testable**:
      - For any concrete input, we can compute arraySum for each inner array
      - We can verify that maxSum equals one of these sums (achievability)
      - We can verify that maxSum ≥ all of these sums (maximality)
      - Test cases demonstrate this verification process

   7. **Comparison with List-based version**:
      - Semantically equivalent but uses Array operations instead of List operations
      - Array.foldl instead of List.foldl
      - Array.map instead of List.map
      - Array indexing arrays[i]! instead of list membership (∈)
      - Array.size instead of List.length
      - Potentially more efficient for large datasets due to O(1) indexing
-/

end TestCases
