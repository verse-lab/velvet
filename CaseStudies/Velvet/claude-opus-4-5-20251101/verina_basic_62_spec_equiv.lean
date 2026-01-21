import Lean
import Mathlib.Tactic

namespace VerinaSpec

def Find_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  -- !benchmark @start postcond
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input
def precondition (a : Array Int) (key : Int) : Prop :=
  True

-- Postcondition: Result is either -1 (not found) or the index of first occurrence
def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  -- Case 1: key not found - result is -1 and key does not appear in array
  (result = -1 ∧ ∀ i : Nat, i < a.size → a[i]! ≠ key) ∨
  -- Case 2: key found - result is valid index, element at result equals key,
  -- and all elements before result are not equal to key
  (result ≥ 0 ∧
   result < a.size ∧
   a[result.toNat]! = key ∧
   ∀ i : Nat, i < result.toNat → a[i]! ≠ key)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.Find_precond a key ↔ LeetProofSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Int) (h_precond : VerinaSpec.Find_precond a key):
  VerinaSpec.Find_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  sorry
