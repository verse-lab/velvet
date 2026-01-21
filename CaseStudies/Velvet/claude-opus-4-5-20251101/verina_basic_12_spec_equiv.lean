/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 05ac3927-8892-4525-83c4-50a636383b0d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (size : Nat):
  VerinaSpec.cubeSurfaceArea_precond size ↔ LeetProofSpec.precondition size

- theorem postcondition_equiv (size : Nat) (result : Nat) (h_precond : VerinaSpec.cubeSurfaceArea_precond size):
  VerinaSpec.cubeSurfaceArea_postcond size result h_precond ↔ LeetProofSpec.postcondition size result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def cubeSurfaceArea_precond (size : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def cubeSurfaceArea_postcond (size : Nat) (result: Nat) (h_precond : cubeSurfaceArea_precond (size)) :=
  -- !benchmark @start postcond
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- No custom helpers needed - using standard Nat multiplication

-- Precondition: No special requirements, any natural number is valid
def precondition (size : Nat) :=
  True

-- Postcondition: The result equals 6 times the square of the edge length
-- A cube has 6 faces, each with area size^2
def postcondition (size : Nat) (result : Nat) :=
  result = 6 * size * size

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (size : Nat):
  VerinaSpec.cubeSurfaceArea_precond size ↔ LeetProofSpec.precondition size := by
  bound

theorem postcondition_equiv (size : Nat) (result : Nat) (h_precond : VerinaSpec.cubeSurfaceArea_precond size):
  VerinaSpec.cubeSurfaceArea_postcond size result h_precond ↔ LeetProofSpec.postcondition size result := by
  -- By definition of `cubeSurfaceArea_postcond`, we have `result = 6 * size * size`.
  simp [VerinaSpec.cubeSurfaceArea_postcond, LeetProofSpec.postcondition];
  grind