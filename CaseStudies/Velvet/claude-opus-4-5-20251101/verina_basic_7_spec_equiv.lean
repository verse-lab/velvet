/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 47e6beb9-32dd-4f2b-b5a4-fddf087f594a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond n):
  VerinaSpec.sumOfSquaresOfFirstNOddNumbers_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- The k-th odd number (0-indexed) is 2k + 1
-- For k from 0 to n-1, the odd numbers are: 1, 3, 5, ..., (2n-1)

-- Postcondition: The result equals the closed-form formula
-- The formula (n * (2 * n - 1) * (2 * n + 1)) / 3 computes the sum of squares
-- of the first n odd natural numbers

def precondition (n : Nat) :=
  True

-- n can be any natural number (including 0)

def postcondition (n : Nat) (result : Nat) :=
  result = (n * (2 * n - 1) * (2 * n + 1)) / 3

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond n ↔ LeetProofSpec.precondition n := by
  exact?

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond n):
  VerinaSpec.sumOfSquaresOfFirstNOddNumbers_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of postcondition, we know that result = (n * (2 * n - 1) * (2 * n + 1)) / 3.
  simp [VerinaSpec.sumOfSquaresOfFirstNOddNumbers_postcond, LeetProofSpec.postcondition];
  grind