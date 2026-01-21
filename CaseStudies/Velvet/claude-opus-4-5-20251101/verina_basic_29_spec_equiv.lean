/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e8434b7e-ec7f-41d7-bbca-e192e69659f7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int) (k : Nat):
  VerinaSpec.removeElement_precond s k ↔ LeetProofSpec.precondition s k

- theorem postcondition_equiv (s : Array Int) (k : Nat) (result : Array Int) (h_precond : VerinaSpec.removeElement_precond s k):
  VerinaSpec.removeElement_postcond s k result h_precond ↔ LeetProofSpec.postcondition s k result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k < s.size

-- !benchmark @end precond

def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  -- !benchmark @start postcond
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: k must be a valid index within the array bounds
def precondition (s : Array Int) (k : Nat) :=
  k < s.size

-- Postcondition clauses:
-- 1. Result has length one less than original
def ensures1 (s : Array Int) (k : Nat) (result : Array Int) :=
  result.size = s.size - 1

-- 2. Elements before index k are unchanged
def ensures2 (s : Array Int) (k : Nat) (result : Array Int) :=
  ∀ i : Nat, i < k → result[i]! = s[i]!

-- 3. Elements after index k are shifted left by one position
def ensures3 (s : Array Int) (k : Nat) (result : Array Int) :=
  ∀ i : Nat, k ≤ i → i < result.size → result[i]! = s[i + 1]!

def postcondition (s : Array Int) (k : Nat) (result : Array Int) :=
  ensures1 s k result ∧
  ensures2 s k result ∧
  ensures3 s k result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : Array Int) (k : Nat):
  VerinaSpec.removeElement_precond s k ↔ LeetProofSpec.precondition s k := by
  rfl

theorem postcondition_equiv (s : Array Int) (k : Nat) (result : Array Int) (h_precond : VerinaSpec.removeElement_precond s k):
  VerinaSpec.removeElement_postcond s k result h_precond ↔ LeetProofSpec.postcondition s k result := by
  -- The result part of the postconditions is the same in both specifications.
  simp [VerinaSpec.removeElement_postcond, LeetProofSpec.postcondition];
  unfold LeetProofSpec.ensures1 LeetProofSpec.ensures2 LeetProofSpec.ensures3; aesop;