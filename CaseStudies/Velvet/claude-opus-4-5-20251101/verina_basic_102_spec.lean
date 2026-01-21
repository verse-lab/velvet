import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    twoSum: Find the lexicographically smallest pair of indices whose elements sum to target
    Natural language breakdown:
    1. We are given an array of integers and a target sum value
    2. We need to find a pair of indices (i, j) where i < j
    3. The elements at these indices must sum to the target: nums[i] + nums[j] = target
    4. Among all valid pairs, we want the lexicographically smallest one
    5. Lexicographically smallest means: minimize i first, then minimize j for that i
    6. Preconditions:
       - The array must have at least 2 elements
       - There must exist at least one valid pair
    7. Postconditions:
       - 0 ≤ i < j < nums.size
       - nums[i] + nums[j] = target
       - (i, j) is lexicographically smallest among all valid pairs
    8. Edge cases:
       - First two elements sum to target
       - Valid pair at the end of array
       - Multiple valid pairs with same first index
       - Negative numbers in array
       - Zero target with zeros in array
-/

section Specs

-- Helper: Check if a pair (i, j) is a valid pair summing to target
def isValidPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- Helper: Check if pair (i1, j1) is lexicographically smaller than or equal to (i2, j2)
def lexLE (i1 : Nat) (j1 : Nat) (i2 : Nat) (j2 : Nat) : Prop :=
  i1 < i2 ∨ (i1 = i2 ∧ j1 ≤ j2)

-- Helper: There exists at least one valid pair
def existsValidPair (nums : Array Int) (target : Int) : Prop :=
  ∃ i j, isValidPair nums target i j

-- Precondition: array has at least 2 elements and a valid pair exists
def precondition (nums : Array Int) (target : Int) :=
  nums.size ≥ 2 ∧ existsValidPair nums target

-- Postcondition: result is a valid pair and is lexicographically smallest
def postcondition (nums : Array Int) (target : Int) (result : Nat × Nat) :=
  let (i, j) := result
  -- The result is a valid pair
  isValidPair nums target i j ∧
  -- The result is lexicographically smallest among all valid pairs
  (∀ i' j', isValidPair nums target i' j' → lexLE i j i' j')

end Specs

section Impl

method twoSum (nums : Array Int) (target : Int)
  return (result : Nat × Nat)
  require precondition nums target
  ensures postcondition nums target result
  do
  pure (0, 1)  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic case from problem description
def test1_nums : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Nat × Nat := (0, 1)

-- Test case 2: Valid pair not at the beginning
def test2_nums : Array Int := #[3, 2, 4]
def test2_target : Int := 6
def test2_Expected : Nat × Nat := (1, 2)

-- Test case 3: Negative numbers in array
def test3_nums : Array Int := #[-1, 0, 1, 2]
def test3_target : Int := 1
def test3_Expected : Nat × Nat := (0, 3)

-- Test case 4: Large numbers
def test4_nums : Array Int := #[5, 75, 25]
def test4_target : Int := 100
def test4_Expected : Nat × Nat := (1, 2)

-- Test case 5: Valid pair at the end
def test5_nums : Array Int := #[1, 2, 3, 4, 5]
def test5_target : Int := 9
def test5_Expected : Nat × Nat := (3, 4)

-- Test case 6: Multiple valid pairs, choose lexicographically smallest
def test6_nums : Array Int := #[1, 5, 3, 5]
def test6_target : Int := 8
def test6_Expected : Nat × Nat := (1, 2)

-- Test case 7: All zeros, target zero
def test7_nums : Array Int := #[0, 0, 0]
def test7_target : Int := 0
def test7_Expected : Nat × Nat := (0, 1)

-- Test case 8: Two elements only
def test8_nums : Array Int := #[10, 20]
def test8_target : Int := 30
def test8_Expected : Nat × Nat := (0, 1)

-- Test case 9: Negative target
def test9_nums : Array Int := #[-5, -3, 2, 8]
def test9_target : Int := -8
def test9_Expected : Nat × Nat := (0, 1)

-- Recommend to validate: 1, 2, 7

end TestCases
