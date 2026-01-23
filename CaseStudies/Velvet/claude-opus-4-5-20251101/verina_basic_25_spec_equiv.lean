/-
Verina's specification is better.

It is better to use `==` instead of `=` for Float
-/


/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 96cd6c89-0e36-4019-be34-3d4cf8df96bf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.sumAndAverage_precond n ↔ LeetProofSpec.precondition n
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def sumAndAverage_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0 ∧ n < 9007199254740992

-- n must be positive and bounded for Float precision
  -- !benchmark @end precond

def sumAndAverage_postcond (n : Nat) (result: Int × Float) (h_precond : sumAndAverage_precond (n)) :=
  -- !benchmark @start postcond
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to compute the expected sum using Gauss formula
-- Renamed to avoid conflict with Mathlib's gaussSum
def sumFormula (n : Nat) : Nat :=
  n * (n + 1) / 2

-- Precondition: n must be positive and bounded for float precision
def precondition (n : Nat) : Prop :=
  n > 0 ∧ n < 9007199254740992

-- 2^53

-- Postcondition clauses
-- The sum component equals the Gauss formula result
def ensures1 (n : Nat) (result : Int × Float) : Prop :=
  result.fst = (sumFormula n : Int)

-- The average component equals sum divided by n
def ensures2 (n : Nat) (result : Int × Float) : Prop :=
  result.snd = (sumFormula n : Nat).toFloat / (n : Nat).toFloat

def postcondition (n : Nat) (result : Int × Float) : Prop :=
  ensures1 n result ∧ ensures2 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.sumAndAverage_precond n ↔ LeetProofSpec.precondition n := by
  exact Iff.rfl

/- Aristotle failed to find a proof. -/
theorem postcondition_equiv (n : Nat) (result : Int × Float) (h_precond : VerinaSpec.sumAndAverage_precond n):
  VerinaSpec.sumAndAverage_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  sorry
