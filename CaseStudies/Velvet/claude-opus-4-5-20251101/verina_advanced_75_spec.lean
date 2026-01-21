import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MaxSubarraySum: Find the largest sum obtainable by choosing a contiguous subarray
    Natural language breakdown:
    1. Given a non-empty sequence of n integers, find the maximum sum of any contiguous subarray
    2. A contiguous subarray is defined by a start index i and end index j where 0 ≤ i ≤ j < n
    3. The sum of a contiguous subarray from index i to j (inclusive) is the sum of all elements in that range
    4. At least one element must be selected (subarray cannot be empty)
    5. The result must be the maximum among all possible contiguous subarray sums
    6. Key properties:
       - The result must equal the sum of at least one contiguous subarray (achievability)
       - The result must be greater than or equal to the sum of every contiguous subarray (maximality)
    7. Edge cases:
       - Single element: the result is that element
       - All negative: the result is the largest (least negative) single element
       - All positive: the result is the sum of the entire array
       - Mixed: depends on the optimal contiguous selection
-/

section Specs

-- Helper function to compute the sum of a contiguous subarray from index start to index stop (exclusive)
def subarraySum (seq : List Int) (start : Nat) (stop : Nat) : Int :=
  (seq.drop start).take (stop - start) |>.foldl (· + ·) 0

-- Predicate: checks if (start, stop) defines a valid non-empty contiguous subarray
def isValidSubarray (seq : List Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ seq.length

-- Predicate: the result is achievable by some contiguous non-empty subarray
def isAchievable (seq : List Int) (result : Int) : Prop :=
  ∃ start stop, isValidSubarray seq start stop ∧ subarraySum seq start stop = result

-- Predicate: the result is maximal among all contiguous non-empty subarrays
def isMaximal (seq : List Int) (result : Int) : Prop :=
  ∀ start stop, isValidSubarray seq start stop → subarraySum seq start stop ≤ result

-- Precondition: the sequence must be non-empty
def precondition (sequence : List Int) : Prop :=
  sequence.length > 0

-- Postcondition: the result is achievable and maximal
def postcondition (sequence : List Int) (result : Int) : Prop :=
  isAchievable sequence result ∧ isMaximal sequence result

end Specs

section Impl

method task_code (sequence : List Int)
  return (result : Int)
  require precondition sequence
  ensures postcondition sequence result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - mixed positive and negative values
def test1_sequence : List Int := [10, -4, 3, 1, 5, 6, -35, 12, 21, -1]
def test1_Expected : Int := 33

-- Test case 2: Another mixed case
def test2_sequence : List Int := [2, 1, -4, 3, 4, -4, 6, 5, -5, 1]
def test2_Expected : Int := 14

-- Test case 3: All negative numbers - should return the largest (least negative)
def test3_sequence : List Int := [-1, -2, -3, -4, -5]
def test3_Expected : Int := -1

-- Test case 4: Single element
def test4_sequence : List Int := [7]
def test4_Expected : Int := 7

-- Test case 5: All positive numbers - sum of entire array
def test5_sequence : List Int := [1, 2, 3, 4, 5]
def test5_Expected : Int := 15

-- Test case 6: Single negative element
def test6_sequence : List Int := [-5]
def test6_Expected : Int := -5

-- Test case 7: Alternating positive and negative with clear optimal subarray
def test7_sequence : List Int := [-2, 1, -3, 4, -1, 2, 1, -5, 4]
def test7_Expected : Int := 6

-- Test case 8: Two separate positive regions
def test8_sequence : List Int := [5, -10, 8]
def test8_Expected : Int := 8

-- Test case 9: All zeros
def test9_sequence : List Int := [0, 0, 0]
def test9_Expected : Int := 0

-- Test case 10: Large negative followed by large positive
def test10_sequence : List Int := [-100, 50, 60]
def test10_Expected : Int := 110

-- Recommend to validate: 1, 3, 4

end TestCases
