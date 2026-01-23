/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c7f09059-d9af-434f-81cc-2c8cab637adc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int):
  VerinaSpec.Abs_precond x ↔ LeetProofSpec.precondition x

- theorem postcondition_equiv (x : Int) (result : Int) (h_precond : VerinaSpec.Abs_precond x):
  VerinaSpec.Abs_postcond x result h_precond ↔ LeetProofSpec.postcondition x result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def Abs_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  -- !benchmark @start postcond
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions
-- Using Int.natAbs from Mathlib which computes absolute value

-- Precondition: no restrictions on input integer
def precondition (x : Int) :=
  True

-- Postcondition: result is the absolute value of x
-- Properties:
-- 1. result is non-negative
-- 2. result equals x if x ≥ 0, otherwise equals -x
-- 3. result squared equals x squared (another way to characterize abs)
def postcondition (x : Int) (result : Int) :=
  result ≥ 0 ∧
  (x ≥ 0 → result = x) ∧
  (x < 0 → result = -x)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int):
  VerinaSpec.Abs_precond x ↔ LeetProofSpec.precondition x := by
  -- Since both preconditions are just True, the equivalence is trivial.
  simp [VerinaSpec.Abs_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : Int) (result : Int) (h_precond : VerinaSpec.Abs_precond x):
  VerinaSpec.Abs_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  -- By definition of VerinaSpec.Abs_postcond and LeetProofSpec.postcondition, we can split the proof into two implications.
  apply Iff.intro;
  · -- If $x$ is non-negative, then $result = x$, so $result$ is non-negative.
    intro h_postcond
    cases' lt_or_ge x 0 with hx_neg hx_nonneg;
    · exact ⟨ by linarith [ h_postcond.2 hx_neg ], fun _ => by linarith [ h_postcond.2 hx_neg ], fun _ => by linarith [ h_postcond.2 hx_neg ] ⟩;
    · -- Since x is non-negative, we have result = x by the postcondition.
      have h_result_eq_x : result = x := by
        exact h_postcond.1 hx_nonneg ▸ rfl;
      -- Since x is non-negative, we have result = x. Now, we need to show that result is non-negative and satisfies the other postcondition parts.
      simp [h_result_eq_x, hx_nonneg];
      exact ⟨ hx_nonneg, fun _ => rfl, fun _ => by linarith ⟩;
  · -- By definition of postcondition, we know that result is non-negative and that if x is non-negative, then result equals x, and if x is negative, then result equals -x.
    intro h_postcond
    obtain ⟨h_nonneg, h_cases⟩ := h_postcond;
    unfold VerinaSpec.Abs_postcond; aesop