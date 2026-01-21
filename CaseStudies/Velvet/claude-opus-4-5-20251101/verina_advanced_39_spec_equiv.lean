/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0f160940-2f8f-4664-b2ae-af40dde7a0f6

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

def maxOfList_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  lst.length > 0

-- !benchmark @end precond

def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: list must be non-empty
def precondition (lst : List Nat) :=
  lst ≠ []

-- Postcondition clauses:
-- 1. The result is a member of the list
-- 2. The result is greater than or equal to all elements in the list
def postcondition (lst : List Nat) (result : Nat) :=
  result ∈ lst ∧
  ∀ x, x ∈ lst → x ≤ result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Nat):
  VerinaSpec.maxOfList_precond lst ↔ LeetProofSpec.precondition lst := by
  -- The length of a list is greater than zero if and only if the list is non-empty.
  simp [VerinaSpec.maxOfList_precond, LeetProofSpec.precondition];
  cases lst <;> aesop

theorem postcondition_equiv (lst : List Nat) (result : Nat) (h_precond : VerinaSpec.maxOfList_precond lst):
  VerinaSpec.maxOfList_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  -- By definition of `maxOfList_postcond` and `postcondition`, they are equivalent because they both require the result to be in the list and greater than or equal to all elements.
  simp [VerinaSpec.maxOfList_postcond, LeetProofSpec.postcondition]