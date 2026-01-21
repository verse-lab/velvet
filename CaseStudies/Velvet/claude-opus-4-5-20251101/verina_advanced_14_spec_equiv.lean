/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 954674dc-243f-4b38-86a8-a134e2e3349f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.ifPowerOfFour_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) (h_precond : VerinaSpec.ifPowerOfFour_precond n):
  VerinaSpec.ifPowerOfFour_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  -- !benchmark @start postcond
  result ↔ (∃ m:Nat, n=4^m)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Predicate: n is a power of four if there exists some natural x where 4^x = n
def isPowerOfFour (n : Nat) : Prop :=
  ∃ x : Nat, 4 ^ x = n

-- Postcondition: result is true iff n is a power of four
def ensures1 (n : Nat) (result : Bool) :=
  result = true ↔ isPowerOfFour n

def precondition (n : Nat) :=
  True

-- no preconditions

def postcondition (n : Nat) (result : Bool) :=
  ensures1 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.ifPowerOfFour_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.ifPowerOfFour_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Bool) (h_precond : VerinaSpec.ifPowerOfFour_precond n):
  VerinaSpec.ifPowerOfFour_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of `ifPowerOfFour_postcond` and `postcondition`, we can rewrite the goal in terms of the existence of `m` and `x`.
  simp [VerinaSpec.ifPowerOfFour_postcond, LeetProofSpec.postcondition, LeetProofSpec.precondition, LeetProofSpec.ensures1];
  -- By definition of `isPowerOfFour`, we have that `n = 4^m` if and only if `4^m = n`.
  simp [LeetProofSpec.isPowerOfFour];
  -- Since equality is symmetric, the existence of m such that n = 4^m is equivalent to the existence of x such that 4^x = n.
  simp [eq_comm]