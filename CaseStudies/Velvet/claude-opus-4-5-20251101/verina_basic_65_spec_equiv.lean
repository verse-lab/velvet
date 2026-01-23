/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c12b76c5-0020-4931-9e88-c633246cc8e0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (N : Nat):
  VerinaSpec.SquareRoot_precond N ↔ LeetProofSpec.precondition N

- theorem postcondition_equiv (N : Nat) (result : Nat) (h_precond : VerinaSpec.SquareRoot_precond N):
  VerinaSpec.SquareRoot_postcond N result h_precond ↔ LeetProofSpec.postcondition N result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def SquareRoot_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  -- !benchmark @start postcond
  result * result ≤ N ∧ N < (result + 1) * (result + 1)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input N (all natural numbers are valid)
def precondition (N : Nat) :=
  True

-- Postcondition: result r satisfies r * r ≤ N < (r + 1) * (r + 1)
-- This uniquely characterizes the integer square root
def postcondition (N : Nat) (result : Nat) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (N : Nat):
  VerinaSpec.SquareRoot_precond N ↔ LeetProofSpec.precondition N := by
  -- Since both preconditions are True, their equivalence is trivially true.
  simp [VerinaSpec.SquareRoot_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (N : Nat) (result : Nat) (h_precond : VerinaSpec.SquareRoot_precond N):
  VerinaSpec.SquareRoot_postcond N result h_precond ↔ LeetProofSpec.postcondition N result := by
  -- Since the postconditions are identical, the equivalence holds trivially.
  simp [VerinaSpec.SquareRoot_postcond, LeetProofSpec.postcondition]