/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bd3ce333-5394-4b70-9fe6-50128c4443f9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (X : Int) (Y : Int):
  VerinaSpec.Swap_precond X Y ↔ LeetProofSpec.precondition X Y

- theorem postcondition_equiv (X : Int) (Y : Int) (result : Int × Int) (h_precond : VerinaSpec.Swap_precond X Y):
  VerinaSpec.Swap_postcond X Y result h_precond ↔ LeetProofSpec.postcondition X Y result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def Swap_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def Swap_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : Swap_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- No helper functions needed - this uses basic product type operations

-- Precondition: no restrictions on input integers
def precondition (X : Int) (Y : Int) :=
  True

-- Postcondition: the result is a pair where first element is Y and second is X
def postcondition (X : Int) (Y : Int) (result : Int × Int) :=
  result.fst = Y ∧ result.snd = X

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (X : Int) (Y : Int):
  VerinaSpec.Swap_precond X Y ↔ LeetProofSpec.precondition X Y := by
  -- Since both preconditions are true for any X and Y, they are equivalent.
  simp [VerinaSpec.Swap_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (X : Int) (Y : Int) (result : Int × Int) (h_precond : VerinaSpec.Swap_precond X Y):
  VerinaSpec.Swap_postcond X Y result h_precond ↔ LeetProofSpec.postcondition X Y result := by
  unfold VerinaSpec.Swap_postcond LeetProofSpec.postcondition; aesop;