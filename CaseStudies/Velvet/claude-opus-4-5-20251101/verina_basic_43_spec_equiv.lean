/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 19198a07-9491-4355-81e9-ff458e02653b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n):
  VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- The k-th odd number (0-indexed) is 2*k + 1
-- We use Finset.sum from Mathlib to express the sum

-- Postcondition: result equals the sum of fourth powers of first n odd numbers
def ensures1 (n : Nat) (result : Nat) :=
  result = Finset.sum (Finset.range n) (fun k => (2 * k + 1) ^ 4)

def precondition (n : Nat) :=
  True

-- n is any non-negative natural number

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n ↔ LeetProofSpec.precondition n := by
  exact Iff.rfl

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n):
  VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  unfold VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond LeetProofSpec.postcondition;
  cases n <;> simp_all +decide [ Nat.sub_sub ] ; ring_nf at * ; aesop;
  -- By simplifying both sides of the equation, we can see that they are indeed equal.
  have h_eq : (Nat.succ ‹_›) * (2 * Nat.succ ‹_› + 1) * (7 + 24 * (Nat.succ ‹_›) ^ 3 - (12 * (Nat.succ ‹_›) ^ 2 + 14 * (Nat.succ ‹_›))) = 15 * Finset.sum (Finset.range (Nat.succ ‹_›)) (fun k => (2 * k + 1) ^ 4) := by
    rw [ Nat.mul_sub_left_distrib ] ; ring;
    exact Nat.sub_eq_of_eq_add <| by induction' Nat.succ ‹_› with n ih <;> norm_num [ Finset.sum_range_succ ] at * ; linarith;
  unfold LeetProofSpec.ensures1; aesop;