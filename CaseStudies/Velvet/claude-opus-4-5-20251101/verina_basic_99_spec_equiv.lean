/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cb37f71a-2495-4dc2-9558-f223d374b765

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int):
  VerinaSpec.Triple_precond x ↔ LeetProofSpec.precondition x

- theorem postcondition_equiv (x : Int) (result : Int) (h_precond : VerinaSpec.Triple_precond x):
  VerinaSpec.Triple_postcond x result h_precond ↔ LeetProofSpec.postcondition x result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result / 3 = x ∧ result / 3 * 3 = result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- No helper functions needed - we use standard integer multiplication from Mathlib

-- Precondition: no restrictions on input
def precondition (x : Int) :=
  True

-- Postcondition: result equals three times the input
def postcondition (x : Int) (result : Int) :=
  result = 3 * x

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int):
  VerinaSpec.Triple_precond x ↔ LeetProofSpec.precondition x := by
  -- By definition of `VerinaSpec.Triple_precond` and `LeetProofSpec.precondition`, both are equivalent to `True`.
  simp [VerinaSpec.Triple_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : Int) (result : Int) (h_precond : VerinaSpec.Triple_precond x):
  VerinaSpec.Triple_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  -- By definition of postcondition, we need to show that `result = 3 * x` if and only if `result / 3 = x` and `result / 3 * 3 = result`.
  simp [VerinaSpec.Triple_postcond, LeetProofSpec.postcondition];
  grind