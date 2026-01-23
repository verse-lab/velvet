/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 91596777-8367-40b0-b365-e5716c91d538

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.allCharactersSame_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allCharactersSame_precond s):
  VerinaSpec.allCharactersSame_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def allCharactersSame_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def allCharactersSame_postcond (s : String) (result: Bool) (h_precond : allCharactersSame_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (result → List.Pairwise (· = ·) cs) ∧
  (¬ result → (cs ≠ [] ∧ cs.any (fun x => x ≠ cs[0]!)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if all characters in a list are the same as the first character
def allSameAsFirst (chars : List Char) : Prop :=
  match chars with
  | [] => True
  | c :: _ => ∀ i : Nat, i < chars.length → chars[i]! = c

-- Postcondition clauses
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ allSameAsFirst s.toList

def precondition (s : String) :=
  True

-- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.allCharactersSame_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.allCharactersSame_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allCharactersSame_precond s):
  VerinaSpec.allCharactersSame_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- By definition of allCharactersSame_postcond and ensures1, we can split into cases based on the result.
  by_cases h_result : result = true;
  · simp [h_result, LeetProofSpec.postcondition, VerinaSpec.allCharactersSame_postcond, LeetProofSpec.ensures1];
    unfold LeetProofSpec.allSameAsFirst;
    -- If the list is pairwise equal, then every element must be equal to the first element.
    apply Iff.intro;
    · intro h_pairwise
      rcases s with ⟨_ | ⟨c, cs⟩⟩ <;> simp_all +decide [ List.pairwise_cons ];
      rintro ( _ | i ) hi <;> simp_all +decide [ List.get ];
      exact Eq.symm ( h_pairwise.1 _ ( by simp ) );
    · rcases s with ( _ | ⟨ c, _ | ⟨ d, s ⟩ ⟩ ) <;> simp_all +decide [ List.pairwise_iff_get ];
  · -- By definition of allCharactersSame_postcond and ensures1, we can split into cases based on the result and the equivalence of the conditions.
    simp [h_result, VerinaSpec.allCharactersSame_postcond, LeetProofSpec.postcondition];
    -- By definition of ensures1, we can rewrite the right-hand side of the equivalence.
    simp [LeetProofSpec.ensures1];
    -- By definition of `allSameAsFirst`, if the list is not all the same as the first element, then there must be some element `x` in the list such that `x` is not equal to the first element.
    simp [LeetProofSpec.allSameAsFirst];
    rcases s with ⟨ _ | ⟨ c, s ⟩ ⟩ <;> simp_all +decide;
    constructor <;> intro h;
    · obtain ⟨ x, hx₁, hx₂ ⟩ := h;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx₁; use i + 1; aesop;
    · rcases h with ⟨ x, hx₁, hx₂ ⟩ ; rcases x with ( _ | x ) <;> simp_all +decide;
      exact ⟨ _, List.getElem_mem _, hx₂ ⟩