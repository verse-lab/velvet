/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3c0a6b7a-1d61-44e1-9fa8-00069076ba33

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.lastDigit_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.lastDigit_precond n):
  VerinaSpec.lastDigit_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def lastDigit_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  -- !benchmark @start postcond
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: n is a natural number (always satisfied for Nat type)
def precondition (n : Nat) :=
  True

-- Postcondition clauses
-- The result equals n modulo 10
def ensures1 (n : Nat) (result : Nat) :=
  result = n % 10

-- The result is a valid single digit (0 to 9)
def ensures2 (n : Nat) (result : Nat) :=
  result < 10

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result ∧
  ensures2 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.lastDigit_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.lastDigit_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.lastDigit_precond n):
  VerinaSpec.lastDigit_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of `lastDigit_postcond` and `postcondition`, we can rewrite them in terms of `n % 10`.
  simp [VerinaSpec.lastDigit_postcond, LeetProofSpec.postcondition];
  -- By definition of `ensures1` and `ensures2`, we can rewrite the postconditions in terms of `n % 10`.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2];
  grind