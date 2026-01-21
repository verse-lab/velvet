/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a7233e2d-e736-41e2-a76d-59cea24734dc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int):
  VerinaSpec.isItEight_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isItEight_precond n):
  VerinaSpec.isItEight_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def isItEight_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def isItEight_postcond (n : Int) (result: Bool) (h_precond : isItEight_precond (n)) : Prop :=
  -- !benchmark @start postcond
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Mathematical definition: a natural number has digit 8 if there exists some
-- position k such that the k-th digit (from the right, 0-indexed) equals 8
def hasDigit8 (n : Nat) : Prop :=
  ∃ k : Nat, (n / (10^k)) % 10 = 8

-- Postcondition: result is true iff n is divisible by 8 or contains digit 8
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ (n % 8 = 0 ∨ hasDigit8 (Int.natAbs n))

def precondition (n : Int) :=
  True

-- no preconditions

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Int):
  VerinaSpec.isItEight_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.isItEight_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isItEight_precond n):
  VerinaSpec.isItEight_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  unfold VerinaSpec.isItEight_postcond LeetProofSpec.postcondition;
  unfold LeetProofSpec.ensures1;
  unfold LeetProofSpec.hasDigit8; aesop;