import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxSubarraySumDivisibleByK: Find the maximum sum of a subarray whose length is divisible by k
    Natural language breakdown:
    1. We are given an array of integers arr and a positive integer k (larger than 1)
    2. A subarray is a contiguous sequence of elements defined by start and stop indices
    3. We need to find subarrays whose length (stop - start) is divisible by k
    4. Among all such valid subarrays, we want the one with the maximum sum
    5. If no valid subarray exists (empty array or no subarray with length divisible by k), return 0
    6. A subarray from index i to j (exclusive) has length j - i
    7. The sum of a subarray is the sum of all elements from index i to j-1
    8. Key properties:
       a. k must be positive (k ≥ 1 based on test cases)
       b. Subarray length must be divisible by k (length % k = 0)
       c. We want the maximum sum among all valid subarrays
       d. Default return is 0 when no valid subarray exists
    9. Edge cases:
       - Empty array: return 0
       - k larger than array size: only check if k divides any valid subarray length
       - All negative sums: return 0 (since empty subarray with length 0 is divisible by k)
       - k = 1: any subarray length is valid, find max contiguous subarray sum
-/

section Specs

-- Helper: compute sum of array elements from index start to stop (exclusive)
def subarraySum (arr : Array Int) (start : Nat) (stop : Nat) : Int :=
  if stop ≤ start then 0
  else if stop > arr.size then 0
  else (arr.toList.drop start).take (stop - start) |>.foldl (· + ·) 0

-- Helper: check if a subarray is valid (has length divisible by k)
def isValidSubarray (arr : Array Int) (k : Int) (start : Nat) (stop : Nat) : Bool :=
  start ≤ stop ∧ stop ≤ arr.size ∧ k > 0 ∧ (stop - start) % k.toNat = 0

-- Helper: predicate for a valid subarray with a specific sum
def validSubarrayWithSum (arr : Array Int) (k : Int) (s : Int) : Prop :=
  ∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ 
    (stop - start) % k.toNat = 0 ∧ subarraySum arr start stop = s

-- Precondition: k must be at least 1
def precondition (arr : Array Int) (k : Int) : Prop :=
  k ≥ 1

-- Postcondition: result is the maximum sum of a valid subarray, or 0 if none exists
def postcondition (arr : Array Int) (k : Int) (result : Int) : Prop :=
  -- Case 1: No valid subarray exists (with positive length) → result is 0
  ((¬∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0) → result = 0) ∧
  -- Case 2: Valid subarrays exist → result is the maximum sum, or 0 if all sums are negative
  ((∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0) →
    -- result is either 0 (if all valid subarray sums are ≤ 0) or the maximum valid subarray sum
    ((result = 0 ∧ ∀ start stop : Nat, start < stop → stop ≤ arr.size → 
      (stop - start) % k.toNat = 0 → subarraySum arr start stop ≤ 0) ∨
     (result > 0 ∧ validSubarrayWithSum arr k result ∧
      ∀ start stop : Nat, start < stop → stop ≤ arr.size → 
        (stop - start) % k.toNat = 0 → subarraySum arr start stop ≤ result)))

end Specs

section Impl

method maxSubarraySumDivisibleByK (arr : Array Int) (k : Int)
  return (result : Int)
  require precondition arr k
  ensures postcondition arr k result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Basic case with positive integers, k=2
def test1_arr : Array Int := #[1, 2, 3, 4, 5]
def test1_k : Int := 2
def test1_Expected : Int := 14

-- Test case 2: Mixed positive and negative integers, k=3
def test2_arr : Array Int := #[1, -2, 3, -4, 5]
def test2_k : Int := 3
def test2_Expected : Int := 4

-- Test case 3: Empty array
def test3_arr : Array Int := #[]
def test3_k : Int := 5
def test3_Expected : Int := 0

-- Test case 4: k=1 means any subarray length is valid
def test4_arr : Array Int := #[1, 2, 3, 4]
def test4_k : Int := 1
def test4_Expected : Int := 10

-- Test case 5: Mixed values with k=2
def test5_arr : Array Int := #[-2, 7, 1, 3]
def test5_k : Int := 2
def test5_Expected : Int := 9

-- Test case 6: k larger than array size, no valid subarray with positive length divisible by k
def test6_arr : Array Int := #[-100, 0, 1]
def test6_k : Int := 5
def test6_Expected : Int := 0

-- Test case 7: Larger numbers with k=2
def test7_arr : Array Int := #[1999, 1, -1023, 12351, -9999]
def test7_k : Int := 2
def test7_Expected : Int := 13328

-- Test case 8: All negative numbers
def test8_arr : Array Int := #[-5, -3, -8, -2]
def test8_k : Int := 2
def test8_Expected : Int := 0

-- Test case 9: Single element array with k=1
def test9_arr : Array Int := #[42]
def test9_k : Int := 1
def test9_Expected : Int := 42

-- Test case 10: Array where best sum uses non-obvious subarray
def test10_arr : Array Int := #[2, -1, 2, -1, 2, -1, 2]
def test10_k : Int := 3
def test10_Expected : Int := 5

-- Recommend to validate: 1, 2, 5

end TestCases
