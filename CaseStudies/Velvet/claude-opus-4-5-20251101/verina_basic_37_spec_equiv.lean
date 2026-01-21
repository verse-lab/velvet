import Lean
import Mathlib.Tactic

namespace VerinaSpec

def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond

def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper definition: check if target exists in the array
def targetExists (arr : Array Int) (target : Int) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = target

-- Precondition: array must be sorted in non-decreasing order
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedNonDecreasing arr

-- Postcondition: result is -1 if target not found, otherwise it's the first index
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  -- Case 1: target not found, result is -1
  (¬targetExists arr target → result = -1) ∧
  -- Case 2: target found, result is a valid index with the target
  (targetExists arr target →
    result ≥ 0 ∧
    result < arr.size ∧
    arr[result.toNat]! = target ∧
    -- No earlier index contains the target (first occurrence)
    ∀ j : Nat, j < result.toNat → arr[j]! ≠ target)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (target : Int):
  VerinaSpec.findFirstOccurrence_precond arr target ↔ LeetProofSpec.precondition arr target := by
  sorry

theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) (h_precond : VerinaSpec.findFirstOccurrence_precond arr target):
  VerinaSpec.findFirstOccurrence_postcond arr target result h_precond ↔ LeetProofSpec.postcondition arr target result := by
  sorry
