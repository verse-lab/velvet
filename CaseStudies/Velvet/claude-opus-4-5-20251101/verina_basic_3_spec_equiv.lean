/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dcc4b252-5212-4c47-88a8-47bdf2dd9b8d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int):
  VerinaSpec.isDivisibleBy11_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isDivisibleBy11_precond n):
  VerinaSpec.isDivisibleBy11_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def isDivisibleBy11_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  -- !benchmark @start postcond
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no restrictions on input
def precondition (n : Int) :=
  True

-- Postcondition: result is true iff n is divisible by 11
def postcondition (n : Int) (result : Bool) :=
  result = true ↔ n % 11 = 0

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Int):
  VerinaSpec.isDivisibleBy11_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are true, the equivalence holds trivially.
  simp [VerinaSpec.isDivisibleBy11_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isDivisibleBy11_precond n):
  VerinaSpec.isDivisibleBy11_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of modulo, we know that n % 11 = 0 if and only if n is divisible by 11.
  have h_mod : n % 11 = 0 ↔ (∃ k : ℤ, n = 11 * k) := by
    -- By definition of modulo, we know that $n \mod 11 = 0$ if and only if there exists an integer $k$ such that $n = 11k$.
    apply Int.modEq_zero_iff_dvd;
  unfold VerinaSpec.isDivisibleBy11_postcond LeetProofSpec.postcondition; aesop;