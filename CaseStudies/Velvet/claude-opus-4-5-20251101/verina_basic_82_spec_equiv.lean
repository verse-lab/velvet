/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 702421ac-31a3-4b46-91cf-50938cd23c78

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.remove_front_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.remove_front_precond a):
  VerinaSpec.remove_front_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def remove_front_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc

def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  -- !benchmark @start postcond
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: Array must be non-empty
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: Result is the array without the first element
-- 1. Length is one less than original
-- 2. Each element at index i in result equals element at index i+1 in original
def postcondition (a : Array Int) (result : Array Int) :=
  result.size = a.size - 1 ∧
  ∀ i : Nat, i < result.size → result[i]! = a[i + 1]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.remove_front_precond a ↔ LeetProofSpec.precondition a := by
  rfl

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.remove_front_precond a):
  VerinaSpec.remove_front_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of `VerinaSpec.remove_front_postcond` and `LeetProofSpec.postcondition`, we can see that they are equivalent.
  simp [VerinaSpec.remove_front_postcond, LeetProofSpec.postcondition];
  -- By definition of `VerinaSpec.remove_front_precond`, we know that `a.size > 0`.
  apply fun h1 h2 => h_precond