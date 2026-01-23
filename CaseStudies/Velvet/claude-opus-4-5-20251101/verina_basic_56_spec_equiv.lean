/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 68c25b99-7ab4-4f51-9369-e4623223f60d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat):
  VerinaSpec.copy_precond src sStart dest dStart len ↔ LeetProofSpec.precondition src sStart dest dStart len

- theorem postcondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result : Array Int) (h_precond : VerinaSpec.copy_precond src sStart dest dStart len):
  VerinaSpec.copy_postcond src sStart dest dStart len result h_precond ↔ LeetProofSpec.postcondition src sStart dest dStart len result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  -- !benchmark @start precond
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len

-- !benchmark @end precond

def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n

def copy_postcond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result: Array Int) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :=
  -- !benchmark @start postcond
  result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: source and destination arrays have sufficient elements
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) :=
  src.size ≥ sStart + len ∧ dest.size ≥ dStart + len

-- Postcondition: result is dest with segment replaced
def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result : Array Int) :=
  -- Result has same size as dest
  result.size = dest.size ∧
  -- Elements before the copied segment are unchanged
  (∀ i : Nat, i < dStart → i < result.size → result[i]! = dest[i]!) ∧
  -- Elements in the copied segment come from src
  (∀ i : Nat, i < len → result[dStart + i]! = src[sStart + i]!) ∧
  -- Elements after the copied segment are unchanged
  (∀ i : Nat, i ≥ dStart + len → i < result.size → result[i]! = dest[i]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat):
  VerinaSpec.copy_precond src sStart dest dStart len ↔ LeetProofSpec.precondition src sStart dest dStart len := by
  exact Iff.rfl

theorem postcondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result : Array Int) (h_precond : VerinaSpec.copy_precond src sStart dest dStart len):
  VerinaSpec.copy_postcond src sStart dest dStart len result h_precond ↔ LeetProofSpec.postcondition src sStart dest dStart len result := by
  unfold VerinaSpec.copy_postcond LeetProofSpec.postcondition;
  grind