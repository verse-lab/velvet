/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aa00c98f-93dd-4058-8b24-6ce58c59b0f4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.reverseString_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.reverseString_precond s):
  VerinaSpec.reverseString_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def reverseString_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def reverseString_postcond (s : String) (result: String) (h_precond : reverseString_precond (s)) : Prop :=
  -- !benchmark @start postcond
  result.length = s.length ∧ result.toList = s.toList.reverse

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no constraints on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: the result is the reversal of the input string
-- Specified via index-wise correspondence and length preservation
def postcondition (s : String) (result : String) : Prop :=
  let inputChars := s.toList
  let resultChars := result.toList
  -- Length is preserved
  resultChars.length = inputChars.length ∧
  -- Each character at position i in result equals character at position (length - 1 - i) in input
  (∀ i : Nat, i < inputChars.length →
    resultChars[i]! = inputChars[inputChars.length - 1 - i]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.reverseString_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.reverseString_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.reverseString_precond s):
  VerinaSpec.reverseString_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- By definition of `postcondition`, we know that if `postcondition s result` holds, then `result.toList = s.toList.reverse`.
  apply Iff.intro;
  · -- By definition of `LeetProofSpec.postcondition`, we need to show that the result's length is equal to the input's length and that each character at position i in the result is equal to the character at position (length - 1 - i) in the input.
    intro h_eq
    constructor
    · exact h_eq.left
    · intro i hi
      have h_char : result.data[i]! = s.data.reverse[i]! := by
        exact congr_arg ( ·[i]! ) h_eq.2
      grind;
  · unfold LeetProofSpec.postcondition;
    -- By definition of list equality, if two lists have the same length and corresponding elements are equal, then the lists are equal.
    intro h
    have h_eq : result.toList = s.toList.reverse := by
      -- By definition of list equality, if two lists have the same length and their elements are equal at every index, then the lists are equal. Therefore, we can conclude that result.toList = s.toList.reverse.
      apply List.ext_get;
      · -- Since the length of a list and its reverse are equal, we can conclude that the lengths of `result.toList` and `s.toList.reverse` are equal.
        simp [h.left];
        exact h.1;
      · grind;
    exact ⟨ by simpa using congr_arg List.length h_eq, h_eq ⟩