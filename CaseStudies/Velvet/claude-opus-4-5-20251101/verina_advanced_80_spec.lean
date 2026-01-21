import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    twoSum: Find indices of two numbers that add up to a target value
    Natural language breakdown:
    1. We are given an array of integers (nums) and a target integer
    2. We need to find two distinct indices i and j such that nums[i] + nums[j] = target
    3. The same element cannot be used twice (i ≠ j)
    4. Each input has exactly one solution (precondition)
    5. The result should be an array of two indices, sorted in ascending order (i < j)
    6. The indices must be valid (within bounds of the array)
    7. Example: nums = [2, 7, 11, 15], target = 9 → result = [0, 1] because nums[0] + nums[1] = 2 + 7 = 9
-/

section Specs

-- Helper: Check if a pair of indices (i, j) forms a valid solution
def isValidPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- Helper: Check if there exists exactly one valid pair (for precondition)
def hasUniqueSolution (nums : Array Int) (target : Int) : Prop :=
  ∃ i j, isValidPair nums target i j ∧
    (∀ i' j', isValidPair nums target i' j' → i' = i ∧ j' = j)

-- Precondition: array has at least 2 elements and exactly one solution exists
def precondition (nums : Array Int) (target : Int) :=
  nums.size ≥ 2 ∧ hasUniqueSolution nums target

-- Postcondition: result contains the two valid indices in sorted order
def postcondition (nums : Array Int) (target : Int) (result : Array Nat) :=
  result.size = 2 ∧
  result[0]! < result[1]! ∧
  result[1]! < nums.size ∧
  nums[result[0]!]! + nums[result[1]!]! = target

end Specs

section Impl

method twoSum (nums : Array Int) (target : Int)
  return (result : Array Nat)
  require precondition nums target
  ensures postcondition nums target result
  do
  pure #[0, 1]  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic example from problem (2 + 7 = 9)
def test1_nums : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Array Nat := #[0, 1]

-- Test case 2: Solution not at beginning (2 + 4 = 6)
def test2_nums : Array Int := #[3, 2, 4]
def test2_target : Int := 6
def test2_Expected : Array Nat := #[1, 2]

-- Test case 3: Duplicate values (3 + 3 = 6)
def test3_nums : Array Int := #[3, 3]
def test3_target : Int := 6
def test3_Expected : Array Nat := #[0, 1]

-- Test case 4: Solution at end of array (4 + 5 = 9)
def test4_nums : Array Int := #[1, 2, 3, 4, 5]
def test4_target : Int := 9
def test4_Expected : Array Nat := #[3, 4]

-- Test case 5: Zero values (0 + 0 = 0)
def test5_nums : Array Int := #[0, 4, 3, 0]
def test5_target : Int := 0
def test5_Expected : Array Nat := #[0, 3]

-- Test case 6: Negative numbers (-3 + 8 = 5)
def test6_nums : Array Int := #[-3, 4, 8, 2]
def test6_target : Int := 5
def test6_Expected : Array Nat := #[0, 2]

-- Test case 7: Mixed positive and negative (-1 + 1 = 0)
def test7_nums : Array Int := #[-1, -2, 1, 3]
def test7_target : Int := 0
def test7_Expected : Array Nat := #[0, 2]

-- Test case 8: Larger array with solution in middle
def test8_nums : Array Int := #[1, 5, 3, 7, 2, 8]
def test8_target : Int := 10
def test8_Expected : Array Nat := #[1, 3]

-- Test case 9: Two element array
def test9_nums : Array Int := #[5, 10]
def test9_target : Int := 15
def test9_Expected : Array Nat := #[0, 1]

-- Recommend to validate: 1, 2, 3

end TestCases

