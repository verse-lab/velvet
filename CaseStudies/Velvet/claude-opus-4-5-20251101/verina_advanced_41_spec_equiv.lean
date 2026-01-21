/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9311f6bf-611d-455f-a2b3-a097ab03dc55

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int) (c : Int):
  VerinaSpec.maxOfThree_precond a b c ↔ LeetProofSpec.precondition a b c

- theorem postcondition_equiv (a : Int) (b : Int) (c : Int) (result : Int) (h_precond : VerinaSpec.maxOfThree_precond a b c):
  VerinaSpec.maxOfThree_postcond a b c result h_precond ↔ LeetProofSpec.postcondition a b c result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  -- !benchmark @start postcond
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Postcondition clause 1: result is greater than or equal to all inputs
def ensures1 (a : Int) (b : Int) (c : Int) (result : Int) :=
  result ≥ a ∧ result ≥ b ∧ result ≥ c

-- Postcondition clause 2: result is one of the input values
def ensures2 (a : Int) (b : Int) (c : Int) (result : Int) :=
  result = a ∨ result = b ∨ result = c

def precondition (a : Int) (b : Int) (c : Int) :=
  True

-- no preconditions needed for any three integers

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) :=
  ensures1 a b c result ∧
  ensures2 a b c result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Int) (b : Int) (c : Int):
  VerinaSpec.maxOfThree_precond a b c ↔ LeetProofSpec.precondition a b c := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.maxOfThree_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (c : Int) (result : Int) (h_precond : VerinaSpec.maxOfThree_precond a b c):
  VerinaSpec.maxOfThree_postcond a b c result h_precond ↔ LeetProofSpec.postcondition a b c result := by
  -- By definition of `maxOfThree_postcond` and `postcondition`, we can rewrite the goal using the equivalence of `ensures1` and `ensures2`.
  simp [VerinaSpec.maxOfThree_postcond, LeetProofSpec.postcondition, LeetProofSpec.ensures1, LeetProofSpec.ensures2]