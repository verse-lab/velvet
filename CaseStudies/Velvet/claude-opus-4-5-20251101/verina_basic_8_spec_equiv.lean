/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 183c9988-e5b1-4a71-9520-e3435a3298b8

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int):
  VerinaSpec.myMin_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Int) (b : Int) (result : Int) (h_precond : VerinaSpec.myMin_precond a b):
  VerinaSpec.myMin_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def myMin_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def myMin_postcond (a : Int) (b : Int) (result: Int) (h_precond : myMin_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on the inputs
def precondition (a : Int) (b : Int) :=
  True

-- Postcondition clauses:
-- 1. The result is less than or equal to a
def ensures1 (a : Int) (b : Int) (result : Int) :=
  result ≤ a

-- 2. The result is less than or equal to b
def ensures2 (a : Int) (b : Int) (result : Int) :=
  result ≤ b

-- 3. The result is one of the two inputs
def ensures3 (a : Int) (b : Int) (result : Int) :=
  result = a ∨ result = b

def postcondition (a : Int) (b : Int) (result : Int) :=
  ensures1 a b result ∧ ensures2 a b result ∧ ensures3 a b result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Int) (b : Int):
  VerinaSpec.myMin_precond a b ↔ LeetProofSpec.precondition a b := by
  -- Since both preconditions are just True, they are trivially equivalent.
  simp [VerinaSpec.myMin_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (result : Int) (h_precond : VerinaSpec.myMin_precond a b):
  VerinaSpec.myMin_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- By definition of conjunction, we can split the equivalence into two implications.
  simp [VerinaSpec.myMin_postcond, LeetProofSpec.postcondition];
  -- Apply the equivalence of conjunctions to split the goal into two implications.
  apply Iff.intro (fun h => by tauto) (fun h => by tauto)