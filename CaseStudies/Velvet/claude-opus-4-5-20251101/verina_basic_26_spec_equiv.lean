/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 49e78383-da4e-40c2-ba72-48336297ed86

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int):
  VerinaSpec.isEven_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isEven_precond n):
  VerinaSpec.isEven_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  -- !benchmark @start postcond
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- No custom helpers needed - we use Mathlib's Even predicate

-- Postcondition: result is true iff n is even
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ Even n

def precondition (n : Int) :=
  True

-- no preconditions; method works for any integer

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Int):
  VerinaSpec.isEven_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are trivially true, the equivalence holds by definition.
  simp [VerinaSpec.isEven_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isEven_precond n):
  VerinaSpec.isEven_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of `VerinaSpec.isEven_postcond` and `LeetProofSpec.postcondition`, we can show that they are equivalent.
  simp [VerinaSpec.isEven_postcond, LeetProofSpec.postcondition];
  -- By definition of `LeetProofSpec.ensures1`, we can rewrite the right-hand side of the equivalence.
  simp [LeetProofSpec.ensures1];
  cases result <;> simp +decide [ Int.even_iff ]