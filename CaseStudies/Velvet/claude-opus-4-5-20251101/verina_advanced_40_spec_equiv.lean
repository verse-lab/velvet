/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b177b4d4-61e5-4d02-88e8-ecb0de98de5d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Nat):
  VerinaSpec.maxOfList_precond lst ↔ LeetProofSpec.precondition lst

- theorem postcondition_equiv (lst : List Nat) (result : Nat) (h_precond : VerinaSpec.maxOfList_precond lst):
  VerinaSpec.maxOfList_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def maxOfList_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  lst ≠ []

-- Ensure the list is non-empty
  -- !benchmark @end precond

@[reducible]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: list must be non-empty
def precondition (lst : List Nat) :=
  lst.length > 0

-- Postcondition: result is the maximum element
-- Property 1: result is a member of the list
-- Property 2: result is greater than or equal to all elements in the list
def postcondition (lst : List Nat) (result : Nat) :=
  result ∈ lst ∧
  ∀ x, x ∈ lst → x ≤ result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Nat):
  VerinaSpec.maxOfList_precond lst ↔ LeetProofSpec.precondition lst := by
  -- Both preconditions are equivalent because a list's length being greater than 0 is the same as it not being empty.
  simp [VerinaSpec.maxOfList_precond, LeetProofSpec.precondition];
  cases lst <;> aesop

theorem postcondition_equiv (lst : List Nat) (result : Nat) (h_precond : VerinaSpec.maxOfList_precond lst):
  VerinaSpec.maxOfList_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  -- By definition of postcondition, we need to show that the result is in the list and that it is greater than or equal to all elements in the list.
  simp [VerinaSpec.maxOfList_postcond, LeetProofSpec.postcondition]