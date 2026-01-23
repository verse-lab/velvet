/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3f6ce3bd-719d-42b2-9e6d-06c7968ed5af

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (X : Int) (Y : Int):
  VerinaSpec.SwapArithmetic_precond X Y ↔ LeetProofSpec.precondition X Y

- theorem postcondition_equiv (X : Int) (Y : Int) (result : (Int × Int)) (h_precond : VerinaSpec.SwapArithmetic_precond X Y):
  VerinaSpec.SwapArithmetic_postcond X Y result h_precond ↔ LeetProofSpec.postcondition X Y result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input values
def precondition (X : Int) (Y : Int) :=
  True

-- Postcondition: The result is the swapped pair (Y, X)
-- First element of result equals Y, second element equals X
def postcondition (X : Int) (Y : Int) (result : Int × Int) :=
  result.fst = Y ∧ result.snd = X

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (X : Int) (Y : Int):
  VerinaSpec.SwapArithmetic_precond X Y ↔ LeetProofSpec.precondition X Y := by
  aesop

theorem postcondition_equiv (X : Int) (Y : Int) (result : (Int × Int)) (h_precond : VerinaSpec.SwapArithmetic_precond X Y):
  VerinaSpec.SwapArithmetic_postcond X Y result h_precond ↔ LeetProofSpec.postcondition X Y result := by
  unfold VerinaSpec.SwapArithmetic_postcond; unfold LeetProofSpec.postcondition; aesop;