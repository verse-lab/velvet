/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bb056821-9304-4cd4-aa5f-87586b2009b0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (N : Nat):
  VerinaSpec.CalSum_precond N ↔ LeetProofSpec.precondition N

- theorem postcondition_equiv (N : Nat) (result : Nat) (h_precond : VerinaSpec.CalSum_precond N):
  VerinaSpec.CalSum_postcond N result h_precond ↔ LeetProofSpec.postcondition N result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def CalSum_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  -- !benchmark @start postcond
  2 * result = N * (N + 1)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on N (any natural number is valid)
def precondition (N : Nat) :=
  True

-- Postcondition: The result equals the closed-form formula N * (N + 1) / 2
-- This is the triangular number formula for the sum of first N natural numbers
def postcondition (N : Nat) (result : Nat) :=
  result = N * (N + 1) / 2

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (N : Nat):
  VerinaSpec.CalSum_precond N ↔ LeetProofSpec.precondition N := by
  -- Since both preconditions are defined as True, they are equivalent.
  simp [VerinaSpec.CalSum_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (N : Nat) (result : Nat) (h_precond : VerinaSpec.CalSum_precond N):
  VerinaSpec.CalSum_postcond N result h_precond ↔ LeetProofSpec.postcondition N result := by
  -- To prove the equivalence, we can use the fact that multiplying both sides of an equation by 2 preserves the equality.
  apply Iff.intro;
  · intro h;
    exact Eq.symm ( Nat.div_eq_of_eq_mul_left two_pos ( by linarith [ h.symm ] ) );
  · -- To prove the reverse direction, we can multiply both sides of the equation by 2 and simplify.
    intro h_postcond
    have h_eq : 2 * result = N * (N + 1) := by
      -- By definition of postcondition, we have result = N * (N + 1) / 2.
      rw [h_postcond];
      exact Nat.mul_div_cancel' ( even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) )
    exact h_eq