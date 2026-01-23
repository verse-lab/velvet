/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 438d3da5-344c-471a-920b-ffbc9bfa6384

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

-- Precondition: no restrictions on input integer
def precondition (x : Int) : Prop :=
  True

-- Postcondition: result must be exactly 3 times the input
def postcondition (x : Int) (result : Int) : Prop :=
  result = 3 * x

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int):
  VerinaSpec.Triple_precond x ↔ LeetProofSpec.precondition x := by
  -- Both preconditions are defined as True, so they are trivially equivalent.
  simp [VerinaSpec.Triple_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : Int) (result : Int) (h_precond : VerinaSpec.Triple_precond x):
  VerinaSpec.Triple_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  -- Let's simplify the goal using the definitions of `VerinaSpec.Triple_postcond` and `LeetProofSpec.postcondition`.
  simp [VerinaSpec.Triple_postcond, LeetProofSpec.postcondition];
  grind