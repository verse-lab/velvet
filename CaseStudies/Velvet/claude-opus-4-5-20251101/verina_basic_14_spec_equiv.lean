/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d72ba8a0-e8de-49e2-b51b-eb69c8b2a773

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.containsZ_precond s ↔ LeetProofSpec.precondition s
-/

import Lean
import Mathlib.Tactic
import Batteries.Data.String.Lemmas

namespace VerinaSpec

def containsZ_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions
-- Using String.contains from Mathlib/Lean stdlib

-- Postcondition clauses
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ (s.contains 'z' ∨ s.contains 'Z')

def ensures2 (s : String) (result : Bool) :=
  result = false ↔ (¬s.contains 'z' ∧ ¬s.contains 'Z')

def precondition (s : String) :=
  True

-- no preconditions as stated in the problem

def postcondition (s : String) (result : Bool) :=
  ensures1 s result ∧ ensures2 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.containsZ_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.containsZ_precond, LeetProofSpec.precondition]

/- Aristotle failed to find a proof. -/
theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.containsZ_precond s):
  VerinaSpec.containsZ_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  simp [VerinaSpec.containsZ_postcond, LeetProofSpec.postcondition, LeetProofSpec.ensures1, LeetProofSpec.ensures2]
  constructor
  · intros hresult
    have ht : (result = true ↔ s.contains 'z' = true ∨ s.contains 'Z' = true) := by
      simp [← hresult, String.contains_iff]
      grind
    grind
  · intros hresult
    rcases hresult with ⟨hresult, _⟩
    simp [String.contains_iff] at hresult
    simp [hresult]
    grind
