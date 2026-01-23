/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bcf77dd2-9141-42e8-95e9-44e34e425acc

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

-- Precondition: No restrictions on the input integer
def precondition (x : Int) :=
  True

-- Postcondition: The result must equal three times the input
def postcondition (x : Int) (result : Int) :=
  result = 3 * x

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int):
  VerinaSpec.Triple_precond x ↔ LeetProofSpec.precondition x := by
  -- Let's simplify the goal using the definitions of `Triple_precond` and `precondition`.
  simp [VerinaSpec.Triple_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : Int) (result : Int) (h_precond : VerinaSpec.Triple_precond x):
  VerinaSpec.Triple_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  -- By definition of postconditions, we need to show that if `result / 3 = x` and `result / 3 * 3 = result`, then `result = 3 * x`.
  simp [VerinaSpec.Triple_postcond, LeetProofSpec.postcondition];
  grind