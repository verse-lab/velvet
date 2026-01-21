import Lean
import Mathlib.Tactic

namespace VerinaSpec

def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond

def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: array must be sorted in non-decreasing order
def precondition (arr : Array Int) (elem : Int) :=
  isSortedNonDecreasing arr

-- Postcondition clauses
-- Case 1: Element found - result is the last index where elem appears
def ensures_found (arr : Array Int) (elem : Int) (result : Int) :=
  result ≥ 0 →
    (result.toNat < arr.size ∧
     arr[result.toNat]! = elem ∧
     (∀ k : Nat, k < arr.size → k > result.toNat → arr[k]! ≠ elem))

-- Case 2: Element not found - result is -1 and elem does not appear in array
def ensures_not_found (arr : Array Int) (elem : Int) (result : Int) :=
  result = -1 →
    (∀ k : Nat, k < arr.size → arr[k]! ≠ elem)

-- Case 3: Result is either -1 or a valid non-negative index
def ensures_valid_result (arr : Array Int) (elem : Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result.toNat < arr.size)

-- Case 4: If elem exists in the array, result must be non-negative
def ensures_completeness (arr : Array Int) (elem : Int) (result : Int) :=
  (∃ k : Nat, k < arr.size ∧ arr[k]! = elem) → result ≥ 0

def postcondition (arr : Array Int) (elem : Int) (result : Int) :=
  ensures_found arr elem result ∧
  ensures_not_found arr elem result ∧
  ensures_valid_result arr elem result ∧
  ensures_completeness arr elem result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (elem : Int):
  VerinaSpec.lastPosition_precond arr elem ↔ LeetProofSpec.precondition arr elem := by
  sorry

theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) (h_precond : VerinaSpec.lastPosition_precond arr elem):
  VerinaSpec.lastPosition_postcond arr elem result h_precond ↔ LeetProofSpec.postcondition arr elem result := by
  sorry
