import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    twoSum: Find two indices whose elements sum to a target value
    
    Natural language breakdown:
    1. We are given a list of integers and a target integer
    2. We need to find two distinct indices i and j such that nums[i] + nums[j] = target
    3. The indices must satisfy i < j (ordered pair)
    4. Both indices must be valid (within bounds of the list)
    5. If such a pair exists, return some (i, j)
    6. If no such pair exists, return none
    7. If multiple valid pairs exist, return the lexicographically first pair
    8. Lexicographically first means: smallest i first, then smallest j among those with same i
    9. Edge cases:
       - Empty list: return none
       - Single element list: return none (need two distinct indices)
       - No pair sums to target: return none
       - Multiple pairs sum to target: return lexicographically smallest
-/

section Specs

-- A valid pair is one where i < j, both in bounds, and elements sum to target
def isValidPair (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

-- Lexicographic ordering on pairs: (i1, j1) < (i2, j2) iff i1 < i2, or i1 = i2 and j1 < j2
def lexLt (p1 : Nat × Nat) (p2 : Nat × Nat) : Prop :=
  p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)

-- Postcondition for when result is some (i, j)
def ensuresSome (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  isValidPair nums target i j ∧
  (∀ i' j', isValidPair nums target i' j' → ¬lexLt (i', j') (i, j))

-- Postcondition for when result is none
def ensuresNone (nums : List Int) (target : Int) : Prop :=
  ∀ i j, ¬isValidPair nums target i j

def precondition (nums : List Int) (target : Int) :=
  True  -- no preconditions

def postcondition (nums : List Int) (target : Int) (result : Option (Nat × Nat)) :=
  match result with
  | none => ensuresNone nums target
  | some (i, j) => ensuresSome nums target i j

end Specs

section Impl

method twoSum (nums : List Int) (target : Int)
  return (result : Option (Nat × Nat))
  require precondition nums target
  ensures postcondition nums target result
  do
  pure none  -- placeholder

end Impl

section TestCases

-- Test case 1: [2, 7, 11, 15] with target 9 → (0, 1) (example from problem)
def test1_nums : List Int := [2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Option (Nat × Nat) := some (0, 1)

-- Test case 2: [3, 2, 4] with target 6 → (1, 2)
def test2_nums : List Int := [3, 2, 4]
def test2_target : Int := 6
def test2_Expected : Option (Nat × Nat) := some (1, 2)

-- Test case 3: [3, 3] with target 6 → (0, 1)
def test3_nums : List Int := [3, 3]
def test3_target : Int := 6
def test3_Expected : Option (Nat × Nat) := some (0, 1)

-- Test case 4: [1, 2, 3] with target 7 → none (no valid pair)
def test4_nums : List Int := [1, 2, 3]
def test4_target : Int := 7
def test4_Expected : Option (Nat × Nat) := none

-- Test case 5: [0, 4, 3, 0] with target 0 → (0, 3)
def test5_nums : List Int := [0, 4, 3, 0]
def test5_target : Int := 0
def test5_Expected : Option (Nat × Nat) := some (0, 3)

-- Test case 6: Empty list with any target → none
def test6_nums : List Int := []
def test6_target : Int := 5
def test6_Expected : Option (Nat × Nat) := none

-- Test case 7: Single element list → none
def test7_nums : List Int := [5]
def test7_target : Int := 10
def test7_Expected : Option (Nat × Nat) := none

-- Test case 8: Multiple valid pairs, lexicographically first should be returned
def test8_nums : List Int := [1, 2, 3, 4, 5]
def test8_target : Int := 5
def test8_Expected : Option (Nat × Nat) := some (0, 3)

-- Test case 9: Negative numbers
def test9_nums : List Int := [-1, -2, 3, 5]
def test9_target : Int := 2
def test9_Expected : Option (Nat × Nat) := some (0, 2)

-- Test case 10: Zero target with negatives
def test10_nums : List Int := [-3, 1, 3, 2]
def test10_target : Int := 0
def test10_Expected : Option (Nat × Nat) := some (0, 2)

-- Recommend to validate: 1, 3, 5

end TestCases
