import Lean
import Mathlib.Tactic

namespace VerinaSpec

def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ a[i]! = e
  -- !benchmark @end precond

def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: The element e must exist in the array a
def precondition (a : Array Int) (e : Int) :=
  ∃ i : Nat, i < a.size ∧ a[i]! = e

-- Postcondition: The result is the index of the first occurrence of e
-- 1. The index is valid (within bounds)
-- 2. The element at that index equals e
-- 3. All elements before that index are different from e
def postcondition (a : Array Int) (e : Int) (result : Nat) :=
  result < a.size ∧
  a[result]! = e ∧
  (∀ i : Nat, i < result → a[i]! ≠ e)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (e : Int):
  VerinaSpec.LinearSearch_precond a e ↔ LeetProofSpec.precondition a e := by
  sorry

theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) (h_precond : VerinaSpec.LinearSearch_precond a e):
  VerinaSpec.LinearSearch_postcond a e result h_precond ↔ LeetProofSpec.postcondition a e result := by
  sorry
