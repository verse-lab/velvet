/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 374caa6b-901d-43a1-bb6c-cae8c0f8120c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int):
  VerinaSpec.isPowerOfTwo_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isPowerOfTwo_precond n):
  VerinaSpec.isPowerOfTwo_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def isPowerOfTwo_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n+1 => base * pow base n

@[reducible]
def isPowerOfTwo_postcond (n : Int) (result: Bool) (h_precond : isPowerOfTwo_precond (n)) : Prop :=
  -- !benchmark @start postcond
  if result then ∃ (x : Nat), (pow 2 x = n) ∧ (n > 0)
  else ¬ (∃ (x : Nat), (pow 2 x = n) ∧ (n > 0))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Predicate: check if an integer is a power of two
-- n is a power of two if n > 0 and there exists a natural number x such that n = 2^x
def isPowerOfTwoProp (n : Int) : Prop :=
  n > 0 ∧ ∃ x : Nat, n = (2 : Int) ^ x

-- Postcondition clauses
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ isPowerOfTwoProp n

def precondition (n : Int) :=
  True

-- no preconditions

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Int):
  VerinaSpec.isPowerOfTwo_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.isPowerOfTwo_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) (h_precond : VerinaSpec.isPowerOfTwo_precond n):
  VerinaSpec.isPowerOfTwo_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  unfold VerinaSpec.isPowerOfTwo_postcond LeetProofSpec.postcondition;
  unfold LeetProofSpec.ensures1;
  -- By definition of `isPowerOfTwoProp`, we know that `isPowerOfTwoProp n` is equivalent to `n > 0 ∧ ∃ x : ℕ, n = 2^x`.
  simp [LeetProofSpec.isPowerOfTwoProp];
  -- By definition of `VerinaSpec.pow`, we know that `VerinaSpec.pow 2 x = 2^x`.
  have h_pow : ∀ x : ℕ, VerinaSpec.pow 2 x = 2 ^ x := by
    intro x; induction x <;> simp +decide [ *, pow_succ' ] ;
    exact?;
  grind