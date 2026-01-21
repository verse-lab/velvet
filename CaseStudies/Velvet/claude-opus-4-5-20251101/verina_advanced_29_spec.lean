import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    longestGoodSubarray: Find the length of the longest good subarray where each element's frequency is at most k
    Natural language breakdown:
    1. Given an array of natural numbers nums and a positive natural number k
    2. The frequency of an element x in an array is the number of times x appears in that array
    3. An array is "good" if every element's frequency is less than or equal to k
    4. A subarray is a contiguous non-empty sequence of elements within the array
    5. We need to find the maximum length among all good subarrays
    6. Since k > 0, any single element forms a good subarray (frequency = 1 ≤ k)
    7. Example: [1,2,3,1,2,3,1,2] with k=2: longest good subarray has length 6
       - The subarray [1,2,3,1,2,3] has each element appearing at most 2 times
    8. Example: [1,2,1,2,1,2,1,2] with k=1: longest good subarray has length 2
       - Any subarray of length > 2 would have some element appearing more than once
    9. Example: [5,5,5,5,5,5,5] with k=4: longest good subarray has length 4
       - Taking 4 consecutive 5's gives frequency exactly 4
    10. The result is always at least 1 (for non-empty arrays) since k ≥ 1
    11. The result is at most nums.length (the entire array might be good)
-/

section Specs

-- Helper: check if a list is "good" (all elements have frequency ≤ k)
def isGoodList (l : List Nat) (k : Nat) : Bool :=
  l.all (fun x => l.count x ≤ k)

-- Helper: extract subarray as a list from index start to index stop (exclusive)
def sublist (l : List Nat) (start : Nat) (stop : Nat) : List Nat :=
  (l.drop start).take (stop - start)

-- Helper: check if there exists a good subarray of a given length
def existsGoodSubarrayOfLength (nums : List Nat) (k : Nat) (len : Nat) : Prop :=
  ∃ start : Nat, start + len ≤ nums.length ∧ isGoodList (sublist nums start (start + len)) k = true

-- Precondition: k must be positive (k > 0) and nums must be non-empty
def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0 ∧ nums.length > 0

-- Postcondition: result is the length of the longest good subarray
def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=
  -- result is a valid length (at least 1, at most nums.length)
  result ≥ 1 ∧
  result ≤ nums.length ∧
  -- there exists a good subarray of length result
  existsGoodSubarrayOfLength nums k result ∧
  -- no good subarray of length greater than result exists
  (∀ len : Nat, len > result → len ≤ nums.length → ¬existsGoodSubarrayOfLength nums k len)

end Specs

section Impl

method longestGoodSubarray (nums : List Nat) (k : Nat)
  return (result : Nat)
  require precondition nums k
  ensures postcondition nums k result
  do
  pure 1  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - mixed elements with k=2
def test1_nums : List Nat := [1, 2, 3, 1, 2, 3, 1, 2]
def test1_k : Nat := 2
def test1_Expected : Nat := 6

-- Test case 2: Alternating elements with k=1
def test2_nums : List Nat := [1, 2, 1, 2, 1, 2, 1, 2]
def test2_k : Nat := 1
def test2_Expected : Nat := 2

-- Test case 3: All same elements with k=4
def test3_nums : List Nat := [5, 5, 5, 5, 5, 5, 5]
def test3_k : Nat := 4
def test3_Expected : Nat := 4

-- Test case 4: Single element array with k=1
def test4_nums : List Nat := [1]
def test4_k : Nat := 1
def test4_Expected : Nat := 1

-- Test case 5: All elements fit within k (entire array is good)
def test5_nums : List Nat := [2, 2, 1, 1, 3]
def test5_k : Nat := 2
def test5_Expected : Nat := 5

-- Test case 6: All distinct elements (entire array is good)
def test6_nums : List Nat := [1, 2, 3, 4, 5]
def test6_k : Nat := 1
def test6_Expected : Nat := 5

-- Test case 7: Large k value (entire array is good)
def test7_nums : List Nat := [1, 1, 1, 2, 2, 2]
def test7_k : Nat := 10
def test7_Expected : Nat := 6

-- Test case 8: Edge case with two same elements and k=1
def test8_nums : List Nat := [3, 3]
def test8_k : Nat := 1
def test8_Expected : Nat := 1

-- Test case 9: Multiple groups with varying frequencies
def test9_nums : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 3]
def test9_k : Nat := 2
def test9_Expected : Nat := 4

-- Test case 10: Single repeated element with k=2
def test10_nums : List Nat := [7, 7, 7, 7, 7]
def test10_k : Nat := 2
def test10_Expected : Nat := 2

-- Recommend to validate: 1, 2, 3

end TestCases
