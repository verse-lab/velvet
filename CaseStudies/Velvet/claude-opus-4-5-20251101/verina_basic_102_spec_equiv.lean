import Lean
import Mathlib.Tactic

namespace VerinaSpec

def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList
  -- !benchmark @end precond

def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  -- !benchmark @start postcond
  let (i, j) := result
  -- Basic validity: i < j, in bounds, and sum equals target
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  -- Lexicographically first: no valid pair (i', j') with i' < i exists
  (nums.toList.take i).zipIdx.all (fun ⟨a, i'⟩ =>
    (nums.toList.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
  -- For our i, j is the smallest valid partner
  ((nums.toList.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

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

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : Array Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target := by
  sorry

theorem postcondition_equiv (nums : Array Int) (target : Int) (result : (Nat × Nat)) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result := by
  sorry
