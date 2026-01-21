/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4de97130-3c29-4be5-9295-d1f1c7c290a7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.allVowels_precond s ↔ LeetProofSpec.precondition s
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower

@[reducible]
def allVowels_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Define the set of vowels as lowercase characters
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']

-- Precondition: no restrictions on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff all 5 vowels appear in the string (case-insensitive)
-- Using property-based specification with List.all and membership
def postcondition (s : String) (result : Bool) : Prop :=
  result = (vowels.all (fun v => v ∈ s.toLower.toList))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.allVowels_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are true, the equivalence holds trivially.
  simp [VerinaSpec.allVowels_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allVowels_precond s):
  VerinaSpec.allVowels_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  have hfeq :
    ∀ str : String,
    ∀ v : Char,
      let chars := VerinaSpec.normalize_str str
      (chars.contains v = true) ↔ (v ∈ s.toLower.toList) := by
    intro str v
    simp [VerinaSpec.normalize_str]
    sorry
  simp [VerinaSpec.allVowels_postcond, LeetProofSpec.postcondition]
  apply Iff.intro
  · intro hresult
    simp [LeetProofSpec.vowels]
    grind
  · intro hresult
    simp [LeetProofSpec.vowels] at hresult
    grind
