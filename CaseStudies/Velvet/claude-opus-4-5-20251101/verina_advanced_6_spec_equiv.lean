import Lean
import Mathlib.Tactic
import Batteries.Data.String.Lemmas

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
  have hToLowerEq : ∀ c : Char, Char.toLower c = VerinaSpec.toLower c := by
    intros c; simp [Char.toLower, VerinaSpec.toLower]; rfl
  have toLowerSwap : ∀ str : String,
    str.toLower.data = str.data.map Char.toLower := by
    unfold String.toLower
    simp [String.map_eq]
  have hfeq :
    ∀ str : String, ∀ v : Char,
      let chars := VerinaSpec.normalize_str str
      (chars.contains v = true) ↔ (v ∈ str.toLower.toList) := by
    intro str v
    simp [VerinaSpec.normalize_str]
    rw [toLowerSwap]
    constructor
    · intros ha; rcases ha with ⟨a, hin, hToLower⟩
      rw [← hToLowerEq] at hToLower
      simp [← hToLower]
      use a
    · intros hv
      generalize str.data = s at *
      induction s with
      | nil => simp at hv
      | cons head tail hind =>
          simp at hv
          cases hv with
          | inl hv =>
              use head
              simp [← hToLowerEq, hv]
          | inr hv =>
              simp at *; right
              simp [← hToLowerEq, hv]
  simp [VerinaSpec.allVowels_postcond, LeetProofSpec.postcondition]
  apply Iff.intro
  · intro hresult
    simp [LeetProofSpec.vowels]
    grind
  · intro hresult
    simp [LeetProofSpec.vowels] at hresult
    grind
