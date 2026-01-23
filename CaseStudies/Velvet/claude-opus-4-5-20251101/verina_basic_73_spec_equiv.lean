/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 148120ad-8eb8-4e11-8075-72f29d41cd62

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) (p : String):
  VerinaSpec.Match_precond s p ↔ LeetProofSpec.precondition s p

- theorem postcondition_equiv (s : String) (p : String) (result : Bool) (h_precond : VerinaSpec.Match_precond s p):
  VerinaSpec.Match_postcond s p result h_precond ↔ LeetProofSpec.postcondition s p result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def Match_precond (s : String) (p : String) : Prop :=
  -- !benchmark @start precond
  s.toList.length = p.toList.length

-- !benchmark @end precond

def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  -- !benchmark @start postcond
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: both strings must have equal length
def precondition (s : String) (p : String) : Prop :=
  s.length = p.length

-- Postcondition: result is true iff for every position, either characters match or pattern has '?'
def postcondition (s : String) (p : String) (result : Bool) : Prop :=
  result = true ↔ (∀ i : Nat, i < s.length → (s.toList[i]! = p.toList[i]! ∨ p.toList[i]! = '?'))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String) (p : String):
  VerinaSpec.Match_precond s p ↔ LeetProofSpec.precondition s p := by
  exact Iff.rfl

theorem postcondition_equiv (s : String) (p : String) (result : Bool) (h_precond : VerinaSpec.Match_precond s p):
  VerinaSpec.Match_postcond s p result h_precond ↔ LeetProofSpec.postcondition s p result := by
  congr!