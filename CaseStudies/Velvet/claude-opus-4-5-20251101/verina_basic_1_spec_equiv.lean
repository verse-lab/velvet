/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ad2c2fe7-8746-43df-8798-1937193e4d5b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int):
  VerinaSpec.hasOppositeSign_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Int) (b : Int) (result : Bool) (h_precond : VerinaSpec.hasOppositeSign_precond a b):
  VerinaSpec.hasOppositeSign_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  -- !benchmark @start postcond
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no restrictions on input integers
def precondition (a : Int) (b : Int) :=
  True

-- Postcondition: result is true iff a and b have opposite signs
-- Using Int.sign: opposite signs means sign(a) * sign(b) = -1
def postcondition (a : Int) (b : Int) (result : Bool) :=
  result = true ↔ (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Int) (b : Int):
  VerinaSpec.hasOppositeSign_precond a b ↔ LeetProofSpec.precondition a b := by
  -- Since both preconditions are always true, they are equivalent.
  simp [VerinaSpec.hasOppositeSign_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (result : Bool) (h_precond : VerinaSpec.hasOppositeSign_precond a b):
  VerinaSpec.hasOppositeSign_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- By definition of postconditions, we can see that they are equivalent.
  simp [VerinaSpec.hasOppositeSign_postcond, LeetProofSpec.postcondition];
  by_cases h1 : a < 0 <;> by_cases h2 : 0 < b <;> simp +decide [ h1, h2 ];
  · grind;
  · grind;
  · grind