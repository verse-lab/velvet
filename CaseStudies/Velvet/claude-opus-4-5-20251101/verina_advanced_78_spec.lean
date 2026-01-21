import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    TwoSum: Given a list of integers and a target, find two indices whose elements sum to target
    Natural language breakdown:
    1. We are given a list of integers (nums) and a target integer
    2. We need to find two indices i and j such that nums[i] + nums[j] = target
    3. The two indices must be different (i ≠ j)
    4. The result should be ordered with the first index smaller than the second (i < j)
    5. Each input is guaranteed to have exactly one solution
    6. The same element cannot be used twice (enforced by i < j)
    7. Both indices must be valid (within bounds of the list)
    8. The result is a pair (Prod) of natural numbers representing the indices
-/

section Specs

-- Precondition: There exists exactly one solution (a valid pair of indices)
-- We require that at least one valid pair exists
def hasSolution (nums : List Int) (target : Int) : Prop :=
  ∃ i j : Nat, i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

def precondition (nums : List Int) (target : Int) : Prop :=
  hasSolution nums target

-- Postcondition clauses
-- The first index is strictly less than the second
def ensures1 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  result.1 < result.2

-- Both indices are within bounds
def ensures2 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  result.2 < nums.length

-- The elements at the two indices sum to the target
def ensures3 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  nums[result.1]! + nums[result.2]! = target

def postcondition (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  ensures1 nums target result ∧
  ensures2 nums target result ∧
  ensures3 nums target result

end Specs

section Impl

method twoSum (nums : List Int) (target : Int)
  return (result : Prod Nat Nat)
  require precondition nums target
  ensures postcondition nums target result
  do
  pure (0, 1)  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic example from problem description
def test1_nums : List Int := [2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Prod Nat Nat := (0, 1)

-- Test case 2: Elements not at the beginning
def test2_nums : List Int := [3, 2, 4]
def test2_target : Int := 6
def test2_Expected : Prod Nat Nat := (1, 2)

-- Test case 3: Duplicate values in list
def test3_nums : List Int := [3, 3]
def test3_target : Int := 6
def test3_Expected : Prod Nat Nat := (0, 1)

-- Test case 4: Last two elements
def test4_nums : List Int := [1, 2, 3, 4]
def test4_target : Int := 7
def test4_Expected : Prod Nat Nat := (2, 3)

-- Test case 5: Zero values in list
def test5_nums : List Int := [0, 4, 3, 0]
def test5_target : Int := 0
def test5_Expected : Prod Nat Nat := (0, 3)

-- Test case 6: Negative numbers
def test6_nums : List Int := [-1, -2, -3, -4, -5]
def test6_target : Int := -8
def test6_Expected : Prod Nat Nat := (2, 4)

-- Test case 7: Mixed positive and negative
def test7_nums : List Int := [-3, 4, 3, 90]
def test7_target : Int := 0
def test7_Expected : Prod Nat Nat := (0, 2)

-- Test case 8: Larger list
def test8_nums : List Int := [1, 5, 3, 7, 2, 8, 4, 6]
def test8_target : Int := 15
def test8_Expected : Prod Nat Nat := (3, 5)

-- Test case 9: First and last elements
def test9_nums : List Int := [5, 1, 2, 3, 4]
def test9_target : Int := 9
def test9_Expected : Prod Nat Nat := (0, 4)

-- Test case 10: Two element list
def test10_nums : List Int := [10, 20]
def test10_target : Int := 30
def test10_Expected : Prod Nat Nat := (0, 1)

-- Recommend to validate: 1, 3, 5

end TestCases
