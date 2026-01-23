/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4fd0787d-0e8d-4403-84fe-1dbb2fc5a820

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.arraySum_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.arraySum_precond a b):
  VerinaSpec.arraySum_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size

-- !benchmark @end precond

def arraySum_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arraySum_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: both arrays must have the same size
def precondition (a : Array Int) (b : Array Int) :=
  a.size = b.size

-- Postcondition: result has same size and element-wise sum property
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.size = a.size ∧
  ∀ i : Nat, i < a.size → result[i]! = a[i]! + b[i]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.arraySum_precond a b ↔ LeetProofSpec.precondition a b := by
  rfl

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.arraySum_precond a b):
  VerinaSpec.arraySum_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- Unfold the definitions of VerinaSpec.arraySum_postcond and LeetProofSpec.postcondition.
  unfold VerinaSpec.arraySum_postcond LeetProofSpec.postcondition at *; simp_all +decide [ eq_comm ] ;