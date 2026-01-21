import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    topKFrequent: Return the k most frequent elements from a list of integers
    Natural language breakdown:
    1. Given a list of integers nums (possibly with duplicates) and a natural number k
    2. Count the frequency of each distinct element in the list
    3. Return exactly k integers that appear most frequently
    4. The result should be ordered from higher frequency to lower frequency
    5. If two numbers have the same frequency, any consistent ordering is acceptable
    6. Precondition: k must be at most the number of distinct elements in nums
    7. The result list should have exactly k elements
    8. Every element in the result must be from the original list
    9. The result should contain distinct elements (no duplicates)
    10. For any element not in the result, its frequency should be at most the frequency of any element in the result
-/

section Specs

-- Helper Functions

-- Count occurrences of an element in a list (using List.count from Mathlib)
def countFreq (x : Int) (nums : List Int) : Nat :=
  nums.count x

-- Get the list of distinct elements
def distinctElements (nums : List Int) : List Int :=
  nums.eraseDups

-- Check if result is sorted by frequency in descending order
def isSortedByFreqDesc (result : List Int) (nums : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < result.length →
    countFreq result[i]! nums ≥ countFreq result[j]! nums

-- Precondition: k is at most the number of distinct elements
def precondition (nums : List Int) (k : Nat) : Prop :=
  k ≤ (distinctElements nums).length

-- Postcondition clauses
-- 1. Result has exactly k elements
def ensures1 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  result.length = k

-- 2. All elements in result are from the original list
def ensures2 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∀ x ∈ result, x ∈ nums

-- 3. Result contains no duplicates
def ensures3 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  result.Nodup

-- 4. Result is sorted by frequency (descending)
def ensures4 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  isSortedByFreqDesc result nums

-- 5. Any element not in result has frequency at most the minimum frequency in result
def ensures5 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∀ x ∈ nums, x ∉ result →
    ∀ y ∈ result, countFreq x nums ≤ countFreq y nums

def postcondition (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ensures1 nums k result ∧
  ensures2 nums k result ∧
  ensures3 nums k result ∧
  ensures4 nums k result ∧
  ensures5 nums k result

end Specs

section Impl

method topKFrequent (nums : List Int) (k : Nat)
  return (result : List Int)
  require precondition nums k
  ensures postcondition nums k result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem - [1, 1, 1, 2, 2, 3], k=2 -> [1, 2]
def test1_nums : List Int := [1, 1, 1, 2, 2, 3]
def test1_k : Nat := 2
def test1_Expected : List Int := [1, 2]

-- Test case 2: Negative numbers - [4, 1, -1, 2, -1, 2, 3], k=2 -> [-1, 2]
def test2_nums : List Int := [4, 1, -1, 2, -1, 2, 3]
def test2_k : Nat := 2
def test2_Expected : List Int := [-1, 2]

-- Test case 3: Single element list - [5], k=1 -> [5]
def test3_nums : List Int := [5]
def test3_k : Nat := 1
def test3_Expected : List Int := [5]

-- Test case 4: Clear winner - [7, 7, 7, 8, 8, 9], k=1 -> [7]
def test4_nums : List Int := [7, 7, 7, 8, 8, 9]
def test4_k : Nat := 1
def test4_Expected : List Int := [7]

-- Test case 5: Empty list with k=0 - [], k=0 -> []
def test5_nums : List Int := []
def test5_k : Nat := 0
def test5_Expected : List Int := []

-- Test case 6: All same frequency, return all - [1, 2, 3], k=3
def test6_nums : List Int := [1, 2, 3]
def test6_k : Nat := 3
def test6_Expected : List Int := [1, 2, 3]

-- Test case 7: All same element - [4, 4, 4, 4], k=1 -> [4]
def test7_nums : List Int := [4, 4, 4, 4]
def test7_k : Nat := 1
def test7_Expected : List Int := [4]

-- Test case 8: Multiple elements with varying frequencies - [1, 2, 2, 3, 3, 3], k=2 -> [3, 2]
def test8_nums : List Int := [1, 2, 2, 3, 3, 3]
def test8_k : Nat := 2
def test8_Expected : List Int := [3, 2]

-- Test case 9: Large negative numbers - [-100, -100, -200, -100], k=1 -> [-100]
def test9_nums : List Int := [-100, -100, -200, -100]
def test9_k : Nat := 1
def test9_Expected : List Int := [-100]

-- Test case 10: Mixed positive and negative with ties - [0, 0, 1, 1, -1, -1], k=2
def test10_nums : List Int := [0, 0, 1, 1, -1, -1]
def test10_k : Nat := 2
def test10_Expected : List Int := [0, 1]

-- Recommend to validate: 1, 2, 3

end TestCases
