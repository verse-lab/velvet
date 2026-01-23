/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b860a6a6-553f-49be-8347-b7e564ee1a44

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (X : UInt8) (Y : UInt8):
  VerinaSpec.SwapBitvectors_precond X Y ↔ LeetProofSpec.precondition X Y

- theorem postcondition_equiv (X : UInt8) (Y : UInt8) (result : UInt8 × UInt8) (h_precond : VerinaSpec.SwapBitvectors_precond X Y):
  VerinaSpec.SwapBitvectors_postcond X Y result h_precond ↔ LeetProofSpec.postcondition X Y result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def SwapBitvectors_precond (X : UInt8) (Y : UInt8) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def SwapBitvectors_postcond (X : UInt8) (Y : UInt8) (result: UInt8 × UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Postcondition clauses
-- The first element of the result pair equals the original second input
def ensures1 (X : UInt8) (Y : UInt8) (result : UInt8 × UInt8) :=
  result.fst = Y

-- The second element of the result pair equals the original first input
def ensures2 (X : UInt8) (Y : UInt8) (result : UInt8 × UInt8) :=
  result.snd = X

def precondition (X : UInt8) (Y : UInt8) :=
  True

-- no preconditions, works for any UInt8 values

def postcondition (X : UInt8) (Y : UInt8) (result : UInt8 × UInt8) :=
  ensures1 X Y result ∧ ensures2 X Y result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (X : UInt8) (Y : UInt8):
  VerinaSpec.SwapBitvectors_precond X Y ↔ LeetProofSpec.precondition X Y := by
  -- Since both preconditions are always true, the equivalence is trivial.
  simp [VerinaSpec.SwapBitvectors_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (X : UInt8) (Y : UInt8) (result : UInt8 × UInt8) (h_precond : VerinaSpec.SwapBitvectors_precond X Y):
  VerinaSpec.SwapBitvectors_postcond X Y result h_precond ↔ LeetProofSpec.postcondition X Y result := by
  -- By definition of SwapBitvectors_postcond and LeetProofSpec.postcondition, we can show that they are equivalent.
  simp [VerinaSpec.SwapBitvectors_postcond, LeetProofSpec.postcondition];
  -- Since the ensures1 and ensures2 conditions are just restating the first two parts of the condition, the equivalence follows directly from the definition of ensures1 and ensures2.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2];
  -- If result.1 = Y and result.2 = X, and X ≠ Y, then obviously result.1 ≠ X and result.2 ≠ Y.
  intros h1 h2 hxy
  simp [h1, h2, hxy];
  -- Since equality is symmetric, if $X \neq Y$, then $Y \neq X$.
  apply Ne.symm; exact hxy