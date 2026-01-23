/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e756fa91-6c90-4d59-865e-546fad55209b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int):
  VerinaSpec.DoubleQuadruple_precond x ↔ LeetProofSpec.precondition x

- theorem postcondition_equiv (x : Int) (result : (Int × Int)) (h_precond : VerinaSpec.DoubleQuadruple_precond x):
  VerinaSpec.DoubleQuadruple_postcond x result h_precond ↔ LeetProofSpec.postcondition x result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  -- !benchmark @start postcond
  result.fst = 2 * x ∧ result.snd = 2 * result.fst

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no restrictions on input
def precondition (x : Int) :=
  True

-- Postcondition: first element is 2*x, second element is 4*x
def postcondition (x : Int) (result : Int × Int) :=
  result.1 = 2 * x ∧ result.2 = 4 * x

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int):
  VerinaSpec.DoubleQuadruple_precond x ↔ LeetProofSpec.precondition x := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.DoubleQuadruple_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : Int) (result : (Int × Int)) (h_precond : VerinaSpec.DoubleQuadruple_precond x):
  VerinaSpec.DoubleQuadruple_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  -- By definition of `VerinaSpec.DoubleQuadruple_postcond` and `LeetProofSpec.postcondition`, we can see that they are equivalent.
  simp [VerinaSpec.DoubleQuadruple_postcond, LeetProofSpec.postcondition];
  grind