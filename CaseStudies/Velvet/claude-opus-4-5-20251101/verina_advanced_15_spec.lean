import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    increasingTriplet: Determine if there exists a strictly increasing triplet in an array
    Natural language breakdown:
    1. We have an input list of integers (nums)
    2. We need to find if there exist three indices i, j, k such that i < j < k
    3. At these indices, the values must be strictly increasing: nums[i] < nums[j] < nums[k]
    4. The function returns true if such a triplet exists, false otherwise
    5. Edge cases:
       - Empty list: no triplet possible, return false
       - List with fewer than 3 elements: no triplet possible, return false
       - Strictly decreasing list: no triplet exists, return false
       - Any list with an increasing subsequence of length 3: return true
    6. Property-oriented specification:
       - result = true ↔ there exist indices i < j < k with nums[i] < nums[j] < nums[k]
       - The indices must be valid (all less than list length)
-/

section Specs

-- Helper predicate: there exists a strictly increasing triplet
def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!

-- Postcondition: result is true iff such a triplet exists
def ensures1 (nums : List Int) (result : Bool) :=
  result = true ↔ hasIncreasingTriplet nums

def precondition (nums : List Int) :=
  True  -- no preconditions

def postcondition (nums : List Int) (result : Bool) :=
  ensures1 nums result

end Specs

section Impl

method increasingTriplet (nums : List Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: Simple increasing sequence [1, 2, 3] - example from problem
def test1_nums : List Int := [1, 2, 3]
def test1_Expected : Bool := true

-- Test case 2: Strictly decreasing sequence [5, 4, 3, 2, 1]
def test2_nums : List Int := [5, 4, 3, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: Mixed sequence with triplet [2, 1, 5, 0, 4, 6]
def test3_nums : List Int := [2, 1, 5, 0, 4, 6]
def test3_Expected : Bool := true

-- Test case 4: Another mixed sequence with triplet [1, 5, 0, 4, 1, 3]
def test4_nums : List Int := [1, 5, 0, 4, 1, 3]
def test4_Expected : Bool := true

-- Test case 5: Small decreasing sequence [5, 4, 3]
def test5_nums : List Int := [5, 4, 3]
def test5_Expected : Bool := false

-- Test case 6: Empty list
def test6_nums : List Int := []
def test6_Expected : Bool := false

-- Test case 7: List with two elements (cannot have triplet)
def test7_nums : List Int := [1, 2]
def test7_Expected : Bool := false

-- Test case 8: List with exactly three equal elements
def test8_nums : List Int := [3, 3, 3]
def test8_Expected : Bool := false

-- Test case 9: Triplet not adjacent [1, 10, 2, 9, 3, 8]
def test9_nums : List Int := [1, 10, 2, 9, 3, 8]
def test9_Expected : Bool := true

-- Test case 10: Single element
def test10_nums : List Int := [5]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 3

end TestCases
