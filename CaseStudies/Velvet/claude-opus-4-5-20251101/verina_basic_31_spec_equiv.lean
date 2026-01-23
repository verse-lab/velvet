/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4ce6f7f9-0888-4338-b239-d67b0b0aa533

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.toUppercase_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.toUppercase_precond s):
  VerinaSpec.toUppercase_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)

def toUppercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Postcondition clauses

-- The result has the same length as the input
def ensures1 (s : String) (result : String) :=
  result.length = s.length

-- Each character in the result is the uppercase version of the corresponding input character
def ensures2 (s : String) (result : String) :=
  ∀ i : Nat, i < s.length → result.toList[i]! = (s.toList[i]!).toUpper

def precondition (s : String) :=
  True

-- no preconditions, any string is valid

def postcondition (s : String) (result : String) :=
  ensures1 s result ∧ ensures2 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.toUppercase_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are defined as `True`, they are trivially equivalent.
  simp [VerinaSpec.toUppercase_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.toUppercase_precond s):
  VerinaSpec.toUppercase_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  unfold VerinaSpec.toUppercase_postcond LeetProofSpec.postcondition;
  -- By definition of `Char.toUpper`, we know that `Char.toUpper c = if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat (c.toNat - 32) else c`.
  have h_toUpper : ∀ c : Char, c.toUpper = if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat (c.toNat - 32) else c := by
    aesop;
  -- By definition of `Char.toUpper`, we know that `Char.ofNat ((c.toNat - 32) % 128) = Char.ofNat (c.toNat - 32)` when `c` is a lowercase letter.
  have h_mod : ∀ c : Char, 'a' ≤ c ∧ c ≤ 'z' → Char.ofNat ((c.toNat - 32) % 128) = Char.ofNat (c.toNat - 32) := by
    simp +zetaDelta at *;
    intro c hc₁ hc₂; have : c.toNat ≤ 122 := by
      exact Nat.le_trans ( Nat.cast_le.mpr hc₂ ) ( by decide ); ; have : c.toNat ≥ 97 := by
      exact?; ; interval_cases c.toNat <;> trivial;
  unfold VerinaSpec.isLowerCase VerinaSpec.shiftMinus32 LeetProofSpec.ensures1 LeetProofSpec.ensures2; aesop;