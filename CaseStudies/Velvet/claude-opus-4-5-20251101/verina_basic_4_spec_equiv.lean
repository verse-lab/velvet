/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 31d86d87-c230-414e-934e-93ca84132fc6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (k : Nat):
  VerinaSpec.kthElement_precond arr k ↔ LeetProofSpec.precondition arr k

- theorem postcondition_equiv (arr : Array Int) (k : Nat) (result : Int) (h_precond : VerinaSpec.kthElement_precond arr k):
  VerinaSpec.kthElement_postcond arr k result h_precond ↔ LeetProofSpec.postcondition arr k result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≥ 1 ∧ k ≤ arr.size

-- !benchmark @end precond

def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  -- !benchmark @start postcond
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: array is non-empty and k is a valid 1-based index
def precondition (arr : Array Int) (k : Nat) : Prop :=
  arr.size > 0 ∧ k ≥ 1 ∧ k ≤ arr.size

-- Postcondition: result is the element at 0-based index (k - 1)
def postcondition (arr : Array Int) (k : Nat) (result : Int) : Prop :=
  result = arr[k - 1]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (k : Nat):
  VerinaSpec.kthElement_precond arr k ↔ LeetProofSpec.precondition arr k := by
  -- The preconditions are equivalent because they both require the array to be non-empty and k to be a valid 1-based index.
  simp [VerinaSpec.kthElement_precond, LeetProofSpec.precondition];
  grind

theorem postcondition_equiv (arr : Array Int) (k : Nat) (result : Int) (h_precond : VerinaSpec.kthElement_precond arr k):
  VerinaSpec.kthElement_postcond arr k result h_precond ↔ LeetProofSpec.postcondition arr k result := by
  -- The two conditions are equivalent because if the element is equal to itself, then it must be true.
  simp [VerinaSpec.kthElement_postcond, LeetProofSpec.postcondition];
  obtain ⟨ hk₁, hk₂ ⟩ := h_precond;
  grind