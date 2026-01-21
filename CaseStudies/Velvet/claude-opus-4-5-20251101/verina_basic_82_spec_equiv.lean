import Lean
import Mathlib.Tactic

namespace VerinaSpec

def remove_front_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond

def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc

def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  -- !benchmark @start postcond
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: Array must be non-empty
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: Result is the array without the first element
-- 1. Length is one less than original
-- 2. Each element at index i in result equals element at index i+1 in original
def postcondition (a : Array Int) (result : Array Int) :=
  result.size = a.size - 1 ∧
  ∀ i : Nat, i < result.size → result[i]! = a[i + 1]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.remove_front_precond a ↔ LeetProofSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.remove_front_precond a):
  VerinaSpec.remove_front_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  sorry
