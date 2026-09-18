module

public import Velvet
public meta import Velvet
public import Mathlib.Tactic

/-!
## Program description

Given two strings `s` and `t`, return `true` if `s` is a subsequence of `t`, or
`false` otherwise.

A subsequence of a string is a new string that is formed from the original
string by deleting some (can be none) of the characters without disturbing the
relative positions of the remaining characters. (i.e., `"ace"` is a subsequence
of `"abcde"` while `"aec"` is not).

1. Inputs are two sequences of characters `s` and `t`.
2. `s` is a subsequence of `t` if we can delete zero or more characters from `t`
   and obtain exactly `s`.
3. Deletions may be none; the relative order of the remaining characters must be
   preserved.
4. The output is true exactly when `s` is a subsequence of `t`, and false
   otherwise.
5. The empty sequence is a subsequence of any sequence.
6. If `s` is longer than `t`, then `s` cannot be a subsequence of `t`.

The inputs are arrays, so the standard two-pointer scan uses constant-time
indexed access. The program runs in O(|s| + |t|) time and O(1) extra space.
-/

namespace IsSubsequence

section Specs

public def subseqByIndex (s : Array Char) (t : Array Char) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i : Nat, i < s.size → f i < t.size) ∧
    StrictMonoOn f (Set.Iio s.size) ∧
    (∀ i : Nat, i < s.size → s[i]! = t[f i]!)

public def precondition (_s : Array Char) (_t : Array Char) : Prop :=
  True

public def postcondition (s : Array Char) (t : Array Char) (result : Bool) : Prop :=
  (result = true ↔ subseqByIndex s t)

end Specs

section Implementation

public def isSubseqRec (s : Array Char) (t : Array Char) (i : Nat) (j : Nat) : Bool :=
  if _hi : i < s.size then
    if _hj : j < t.size then
      if s[i]! == t[j]! then
        isSubseqRec s t (i + 1) (j + 1)
      else
        isSubseqRec s t i (j + 1)
    else
      false
  else
    true
termination_by (s.size - i) + (t.size - j)

method isSubsequence (s : Array Char) (t : Array Char)
  returns (result : Bool)
  requires valid: precondition s t
  ensures subseq: postcondition s t result
do
  let mut i : Nat := 0
  let mut j : Nat := 0
  while' scanning: i < s.size ∧ j < t.size
    invariant bounds: i ≤ s.size ∧ j ≤ t.size
    invariant continuation: isSubseqRec s t i j = isSubseqRec s t 0 0
    decreasing remaining: (s.size - i) + (t.size - j)
    done_with done: ¬(i < s.size ∧ j < t.size)
  do
    if match_char: s[i]! == t[j]! then
      i := i + 1
      j := j + 1
    else
      j := j + 1
  return i == s.size

end Implementation

section Proof

public def HasSubseqEmbeddingFrom (s t : Array Char) (i j : Nat) : Prop :=
  ∃ f : Nat → Nat,
    (∀ k, i ≤ k → k < s.size → j ≤ f k ∧ f k < t.size) ∧
    (∀ a b, i ≤ a → a < b → b < s.size → f a < f b) ∧
    (∀ k, i ≤ k → k < s.size → s[k]! = t[f k]!)

theorem embedding_to_subseqByIndex (s t : Array Char) (h : HasSubseqEmbeddingFrom s t 0 0) :
    subseqByIndex s t := by
  rcases h with ⟨f, hbound, hmono, hmatch⟩
  unfold subseqByIndex
  refine ⟨f, ?_, ?_, ?_⟩
  · intro k hk
    exact (hbound k (Nat.zero_le k) hk).2
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    exact hmono a b (Nat.zero_le a) hab hb
  · intro k hk
    exact hmatch k (Nat.zero_le k) hk

theorem subseqByIndex_to_embedding (s t : Array Char) (h : subseqByIndex s t) :
    HasSubseqEmbeddingFrom s t 0 0 := by
  rcases h with ⟨f, hbound, hmono, hmatch⟩
  unfold HasSubseqEmbeddingFrom
  refine ⟨f, ?_, ?_, ?_⟩
  · intro k _ hk
    exact ⟨Nat.zero_le (f k), hbound k hk⟩
  · intro a b _ hab hb
    have ha : a < s.size := lt_trans hab hb
    have ha_mem : a ∈ Set.Iio s.size := by simp only [Set.mem_Iio, ha]
    have hb_mem : b ∈ Set.Iio s.size := by simp only [Set.mem_Iio, hb]
    exact hmono ha_mem hb_mem hab
  · intro k _ hk
    exact hmatch k hk

theorem isSubseqRec_sound (s t : Array Char) (i j : Nat) (hi : i ≤ s.size) (hj : j ≤ t.size) :
    isSubseqRec s t i j = true → HasSubseqEmbeddingFrom s t i j := by
  induction' hmeas : (s.size - i) + (t.size - j) using Nat.strong_induction_on with m ih generalizing i j
  intro hrec
  rw [isSubseqRec.eq_def] at hrec
  by_cases hi_lt : i < s.size
  · simp only [hi_lt, ↓reduceDIte] at hrec
    by_cases hj_lt : j < t.size
    · simp only [hj_lt, ↓reduceDIte] at hrec
      by_cases hmatch_c : (s[i]! == t[j]!) = true
      · simp only [hmatch_c, ↓reduceIte] at hrec
        have h_eq : s[i]! = t[j]! := by simpa using hmatch_c
        have hm : (s.size - (i + 1)) + (t.size - (j + 1)) < m := by omega
        have hih := ih ((s.size - (i + 1)) + (t.size - (j + 1))) hm (i + 1) (j + 1)
          (by omega) (by omega) rfl hrec
        rcases hih with ⟨f', hf'_bound, hf'_mono, hf'_match⟩
        refine ⟨fun k => if k = i then j else f' k, ?_, ?_, ?_⟩
        · intro k hle hk
          dsimp only
          by_cases hki : k = i
          · subst hki
            simp only [ite_true]
            exact ⟨le_refl j, hj_lt⟩
          · have hsucc : i + 1 ≤ k := by omega
            simp only [hki, ite_false]
            have hres := hf'_bound k hsucc hk
            exact ⟨by omega, hres.2⟩
        · intro a b ha hab hb
          dsimp only
          by_cases hai : a = i
          · subst a
            have hbi : i + 1 ≤ b := by omega
            have hneq_b : b ≠ i := by omega
            simp [hneq_b]
            have hres := hf'_bound b hbi hb
            exact hres.1
          · have hsucc_a : i + 1 ≤ a := by omega
            have hneq_b : b ≠ i := by omega
            simp only [hai, hneq_b, ite_false]
            exact hf'_mono a b hsucc_a hab hb
        · intro k hle hk
          dsimp only
          by_cases hki : k = i
          · subst hki
            simp only [ite_true]
            exact h_eq
          · have hsucc : i + 1 ≤ k := by omega
            simp only [hki, ite_false]
            exact hf'_match k hsucc hk
      · have hnot_match : (s[i]! == t[j]!) = false := by
          cases h : (s[i]! == t[j]!)
          · rfl
          · contradiction
        simp only [hnot_match, ↓reduceIte, Bool.false_eq_true] at hrec
        have hm : (s.size - i) + (t.size - (j + 1)) < m := by omega
        have hih := ih ((s.size - i) + (t.size - (j + 1))) hm i (j + 1)
          (by omega) (by omega) rfl hrec
        rcases hih with ⟨f', hf'_bound, hf'_mono, hf'_match⟩
        refine ⟨f', ?_, hf'_mono, hf'_match⟩
        intro k hle hk
        have hres := hf'_bound k hle hk
        exact ⟨by omega, hres.2⟩
    · simp only [hj_lt, ↓reduceDIte, Bool.false_eq_true] at hrec
  · simp only [hi_lt, ↓reduceDIte] at hrec
    refine ⟨fun _ => j, ?_, ?_, ?_⟩
    · intro k hle hk; omega
    · intro a b ha hab hb; omega
    · intro k hle hk; omega

theorem isSubseqRec_complete (s t : Array Char) (i j : Nat) (hi : i ≤ s.size) (hj : j ≤ t.size) :
    HasSubseqEmbeddingFrom s t i j → isSubseqRec s t i j = true := by
  induction' hmeas : (s.size - i) + (t.size - j) using Nat.strong_induction_on with m ih generalizing i j
  intro hemb
  rw [isSubseqRec.eq_def]
  by_cases hi_lt : i < s.size
  · simp only [hi_lt, ↓reduceDIte]
    by_cases hj_lt : j < t.size
    · simp only [hj_lt, ↓reduceDIte]
      by_cases hmatch_c : (s[i]! == t[j]!) = true
      · simp only [hmatch_c, ↓reduceIte]
        have hm : (s.size - (i + 1)) + (t.size - (j + 1)) < m := by omega
        apply ih ((s.size - (i + 1)) + (t.size - (j + 1))) hm (i + 1) (j + 1) (by omega) (by omega) rfl
        rcases hemb with ⟨f, hbound, hmono, hmatch⟩
        refine ⟨f, ?_, ?_, ?_⟩
        · intro k hk_le hk_lt
          have hki : i < k := by omega
          have hmono_ik := hmono i k (le_refl i) hki hk_lt
          have hbi := hbound i (le_refl i) hi_lt
          exact ⟨by omega, (hbound k (by omega) hk_lt).2⟩
        · intro a b ha hab hb
          exact hmono a b (by omega) hab hb
        · intro k hk_le hk_lt
          exact hmatch k (by omega) hk_lt
      · have hnot_match : (s[i]! == t[j]!) = false := by
          cases h : (s[i]! == t[j]!)
          · rfl
          · contradiction
        simp only [hnot_match, ↓reduceIte, Bool.false_eq_true]
        have hm : (s.size - i) + (t.size - (j + 1)) < m := by omega
        apply ih ((s.size - i) + (t.size - (j + 1))) hm i (j + 1) (by omega) (by omega) rfl
        rcases hemb with ⟨f, hbound, hmono, hmatch⟩
        refine ⟨f, ?_, ?_, ?_⟩
        · intro k hk_le hk_lt
          have hbi := hbound i (le_refl i) hi_lt
          have hneq_ij : f i ≠ j := by
            intro hf_eq
            have hsi : s[i]! = t[f i]! := hmatch i (le_refl i) hi_lt
            rw [hf_eq] at hsi
            have : (s[i]! == t[j]!) = true := by simp [hsi]
            contradiction
          have hfi_gt : j + 1 ≤ f i := by
            have : j ≤ f i := hbi.1
            omega
          by_cases hki : k = i
          · subst hki
            exact ⟨hfi_gt, hbi.2⟩
          · have hmono_ik := hmono i k (le_refl i) (by omega) hk_lt
            exact ⟨by omega, (hbound k hk_le hk_lt).2⟩
        · intro a b ha hab hb
          exact hmono a b ha hab hb
        · intro k hk_le hk_lt
          exact hmatch k hk_le hk_lt
    · rcases hemb with ⟨f, hbound, _, _⟩
      have hbi := hbound i (le_refl i) hi_lt
      omega
  · simp only [hi_lt, ↓reduceDIte]

theorem isSubseqRec_iff_subseqByIndex (s t : Array Char) :
    (isSubseqRec s t 0 0 = true) ↔ subseqByIndex s t := by
  constructor
  · intro h
    exact embedding_to_subseqByIndex s t (isSubseqRec_sound s t 0 0 (Nat.zero_le _) (Nat.zero_le _) h)
  · intro h
    exact isSubseqRec_complete s t 0 0 (Nat.zero_le _) (Nat.zero_le _) (subseqByIndex_to_embedding s t h)

theorem exit_postcondition (s t : Array Char) (i j : Nat)
    (hbounds : i ≤ s.size ∧ j ≤ t.size)
    (hdone : ¬(i < s.size ∧ j < t.size))
    (hcont : isSubseqRec s t i j = isSubseqRec s t 0 0) :
    postcondition s t (i == s.size) := by
  unfold postcondition
  rw [← isSubseqRec_iff_subseqByIndex, ← hcont]
  rw [isSubseqRec.eq_def]
  by_cases hi : i < s.size
  · simp only [hi, ↓reduceDIte]
    have hj : ¬(j < t.size) := by
      intro hj
      exact hdone ⟨hi, hj⟩
    simp only [hj, ↓reduceDIte, Bool.false_eq_true]
    have hneq : ¬(i = s.size) := by omega
    simp [beq_iff_eq, hneq]
  · simp only [hi, ↓reduceDIte]
    have heq : i = s.size := by omega
    simp [heq]

theorem isSubseqRec_step_match (s t : Array Char) (i j : Nat)
    (hi : i < s.size) (hj : j < t.size) (hm : (s[i]! == t[j]!) = true) :
    isSubseqRec s t (i + 1) (j + 1) = isSubseqRec s t i j := by
  rw [isSubseqRec.eq_def (i := i) (j := j)]
  simp only [hi, hj, hm, ↓reduceDIte, ↓reduceIte]

theorem isSubseqRec_step_mismatch (s t : Array Char) (i j : Nat)
    (hi : i < s.size) (hj : j < t.size) (hm : (s[i]! == t[j]!) = false) :
    isSubseqRec s t i (j + 1) = isSubseqRec s t i j := by
  rw [isSubseqRec.eq_def (i := i) (j := j)]
  simp only [hi, hj, hm, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true]

prove_correct isSubsequence by
  velvet_vcgen [isSubsequence, postcondition] with try finish
  case subseq =>
    rename_i s t
    exact exit_postcondition s t i j bounds done continuation
  case continuation =>
    rename_i s t
    have hi : i < s.size := scanning.1
    have hj : j < t.size := scanning.2
    have hm : (s[i]! == t[j]!) = true := match_char
    rw [isSubseqRec_step_match s t i j hi hj hm, continuation]
  case continuation =>
    rename_i s t
    have hi : i < s.size := scanning.1
    have hj : j < t.size := scanning.2
    have hm : (s[i]! == t[j]!) = false := by
      have harray : (s[i]! == t[j]!) = false := by
        cases h : (s[i]! == t[j]!)
        · rfl
        · exact False.elim (match_char h)
      exact harray
    rw [isSubseqRec_step_mismatch s t i j hi hj hm, continuation]

end Proof

end IsSubsequence
