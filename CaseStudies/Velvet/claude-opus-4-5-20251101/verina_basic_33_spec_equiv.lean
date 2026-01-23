/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2efd1cfb-0a52-49b1-a1ce-a380b4f78bef

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : List Nat):
  VerinaSpec.smallestMissingNumber_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : List Nat) (result : Nat) (h_precond : VerinaSpec.smallestMissingNumber_precond s):
  VerinaSpec.smallestMissingNumber_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def smallestMissingNumber_precond (s : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) s

-- !benchmark @end precond

def smallestMissingNumber_postcond (s : List Nat) (result: Nat) (h_precond : smallestMissingNumber_precond (s)) :=
  -- !benchmark @start postcond
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: The input list is sorted in non-decreasing order
def precondition (s : List Nat) : Prop :=
  List.Sorted (· ≤ ·) s

-- Postcondition: The result is the smallest natural number not in the list
-- Property 1: The result is not in the list
-- Property 2: All natural numbers smaller than result are in the list
def postcondition (s : List Nat) (result : Nat) : Prop :=
  result ∉ s ∧
  (∀ k : Nat, k < result → k ∈ s)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : List Nat):
  VerinaSpec.smallestMissingNumber_precond s ↔ LeetProofSpec.precondition s := by
  exact?

theorem postcondition_equiv (s : List Nat) (result : Nat) (h_precond : VerinaSpec.smallestMissingNumber_precond s):
  VerinaSpec.smallestMissingNumber_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- The two postconditions are equivalent because they both require that the result is not in the list and that all smaller numbers are in the list.
  simp [VerinaSpec.smallestMissingNumber_postcond, LeetProofSpec.postcondition]