/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5e706992-45f0-4f34-8fd7-69e9a5b16aee

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int):
  VerinaSpec.ComputeAvg_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Int) (b : Int) (result : Int) (h_precond : VerinaSpec.ComputeAvg_precond a b):
  VerinaSpec.ComputeAvg_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  -- !benchmark @start postcond
  2 * result = a + b - ((a + b) % 2)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no constraints needed, any two integers are valid inputs
def precondition (a : Int) (b : Int) : Prop :=
  True

-- Postcondition: the computed average is the floor of (a + b) / 2
-- This is uniquely determined by: 2 * result ≤ a + b < 2 * result + 2
def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  2 * result ≤ a + b ∧ a + b < 2 * result + 2

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Int) (b : Int):
  VerinaSpec.ComputeAvg_precond a b ↔ LeetProofSpec.precondition a b := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.ComputeAvg_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (result : Int) (h_precond : VerinaSpec.ComputeAvg_precond a b):
  VerinaSpec.ComputeAvg_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- By definition of VerinaSpec.ComputeAvg_postcond, we have that 2 * result = a + b - ((a + b) % 2).
  simp [VerinaSpec.ComputeAvg_postcond, LeetProofSpec.postcondition];
  grind