/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8056b4fc-4c87-4399-bde9-976d731a0665

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int) (c : Int):
  VerinaSpec.minOfThree_precond a b c ↔ LeetProofSpec.precondition a b c

- theorem postcondition_equiv (a : Int) (b : Int) (c : Int) (result : Int) (h_precond : VerinaSpec.minOfThree_precond a b c):
  VerinaSpec.minOfThree_postcond a b c result h_precond ↔ LeetProofSpec.postcondition a b c result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No constraints needed for three integers
def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

-- Postcondition clauses:
-- 1. Result is less than or equal to each input
def ensures1 (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ result ≤ c

-- 2. Result is one of the three input values
def ensures2 (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result = a ∨ result = b ∨ result = c

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  ensures1 a b c result ∧ ensures2 a b c result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Int) (b : Int) (c : Int):
  VerinaSpec.minOfThree_precond a b c ↔ LeetProofSpec.precondition a b c := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.minOfThree_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (c : Int) (result : Int) (h_precond : VerinaSpec.minOfThree_precond a b c):
  VerinaSpec.minOfThree_postcond a b c result h_precond ↔ LeetProofSpec.postcondition a b c result := by
  -- By definition of postcondition, we need to show that the result is less than or equal to each input and equal to one of them.
  simp [LeetProofSpec.postcondition];
  -- By definition of postcondition, we can split the equivalence into two implications.
  simp [VerinaSpec.minOfThree_postcond, LeetProofSpec.ensures1, LeetProofSpec.ensures2]