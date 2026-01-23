/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 484a991a-ef3b-4f61-880d-149b36bc66b6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int):
  VerinaSpec.ComputeIsEven_precond x ↔ LeetProofSpec.precondition x

- theorem postcondition_equiv (x : Int) (result : Bool) (h_precond : VerinaSpec.ComputeIsEven_precond x):
  VerinaSpec.ComputeIsEven_postcond x result h_precond ↔ LeetProofSpec.postcondition x result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def ComputeIsEven_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k : Int, x = 2 * k

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- No helper functions needed - using Int's built-in modulo operation

-- Postcondition: result is true iff x is divisible by 2
def ensures1 (x : Int) (result : Bool) :=
  result = true ↔ x % 2 = 0

def precondition (x : Int) :=
  True

-- no preconditions needed

def postcondition (x : Int) (result : Bool) :=
  ensures1 x result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int):
  VerinaSpec.ComputeIsEven_precond x ↔ LeetProofSpec.precondition x := by
  -- Since both preconditions are true for any integer x, the equivalence is trivial.
  simp [VerinaSpec.ComputeIsEven_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : Int) (result : Bool) (h_precond : VerinaSpec.ComputeIsEven_precond x):
  VerinaSpec.ComputeIsEven_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  -- By definition of $ComputeIsEven_postcond$, we need to show that $result = true ↔ ∃ k : Int, x = 2 * k$.
  simp [VerinaSpec.ComputeIsEven_postcond, LeetProofSpec.postcondition];
  -- By definition of modulo, we know that $x \mod 2 = 0$ if and only if there exists some integer $k$ such that $x = 2k$.
  have h_mod : x % 2 = 0 ↔ ∃ k : ℤ, x = 2 * k := by
    -- By definition of divisibility, $x \mod 2 = 0$ if and only if there exists some integer $k$ such that $x = 2k$.
    apply Int.dvd_iff_emod_eq_zero.symm;
  -- By definition of $ensures1$, we know that $result = true ↔ x % 2 = 0$.
  simp [LeetProofSpec.ensures1, h_mod]