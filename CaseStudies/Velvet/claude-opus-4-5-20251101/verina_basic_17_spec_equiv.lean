/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: af3f345d-1847-4184-9c0c-240553081b59

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.toLowercase_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.toLowercase_precond s):
  VerinaSpec.toLowercase_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)

def toLowercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no constraints on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: result has same length and each character is the lowercase version
def postcondition (s : String) (result : String) : Prop :=
  -- Length is preserved
  result.length = s.length ∧
  -- Each character is converted using Char.toLower
  (∀ i : Nat, i < s.length → result.data[i]! = s.data[i]!.toLower)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.toLowercase_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are always true, the equivalence is trivial.
  simp [VerinaSpec.toLowercase_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.toLowercase_precond s):
  VerinaSpec.toLowercase_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  unfold VerinaSpec.toLowercase_postcond LeetProofSpec.postcondition;
  -- By definition of `Char.toLower`, we know that it is equivalent to the condition in the VerinaSpec.toLowercase_postcond.
  have h_char_toLower_eq : ∀ c : Char, Char.toLower c = if VerinaSpec.isUpperCase c then VerinaSpec.shift32 c else c := by
    unfold Char.toLower VerinaSpec.isUpperCase VerinaSpec.shift32; aesop;
  aesop