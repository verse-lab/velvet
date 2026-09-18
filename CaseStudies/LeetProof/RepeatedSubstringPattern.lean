module

public import Velvet
public meta import Velvet

/-!
## Program description

Given a string `s`, check if it can be constructed by taking a substring of it
and appending multiple copies of the substring together.

The program is expected to run in O(n^1.5) time and O(1) extra space. The input
is an array, so periodicity checks use constant-time indexed access without
materializing a copy.
-/

namespace RepeatedSubstringPattern

section Specs

public def precondition (_s : Array Char) : Prop :=
  True

public def postcondition (s : Array Char) (result : Bool) : Prop :=
  let n := s.size
  (result = true) ↔
    (∃ k : Nat,
      0 < k ∧
      k < n ∧
      n % k = 0 ∧
      (∀ i : Nat, i < n → s[i]! = s[i % k]!))

end Specs

section Implementation

public def arrayPostcondition (s : Array Char) (result : Bool) : Prop :=
  postcondition s result

method repeatedSubstringPattern (s : Array Char)
  returns (result : Bool)
  requires valid: precondition s
  ensures repeated_substring: postcondition s result
do
  let a := s
  let n := a.size
  if small: n ≤ 1 then
    return false
  else
    let mut k : Nat := 1
    let mut found : Bool := false
    while' outer_scan: k < n ∧ found = false
      invariant outer_bounds: 1 ≤ k ∧ k ≤ n
      invariant outer_sound: found = true →
        ∃ kp, 0 < kp ∧ kp < n ∧ n % kp = 0 ∧ (∀ i, i < n → a[i]! = a[i % kp]!)
      invariant outer_complete: found = false →
        ∀ kp, 0 < kp → kp < k → ¬(n % kp = 0 ∧ (∀ i, i < n → a[i]! = a[i % kp]!))
      decreasing outer_remaining: n - k
      done_with outer_done: k = n ∨ found = true
    do
      if div_cond: n % k = 0 then
        let mut j : Nat := k
        let mut match_ok : Bool := true
        while' inner_scan: j < n ∧ match_ok = true
          invariant inner_k_bound: 1 ≤ k ∧ k < n ∧ n % k = 0
          invariant inner_j_bound: k ≤ j ∧ j ≤ n
          invariant inner_match: match_ok = true →
            ∀ m, k ≤ m → m < j → a[m]! = a[m % k]!
          invariant inner_mismatch: match_ok = false →
            ∃ m, m < n ∧ a[m]! ≠ a[m % k]!
          decreasing inner_remaining: n - j
          done_with inner_done: j = n ∨ match_ok = false
        do
          if neq_elem: a[j]! ≠ a[j % k]! then
            match_ok := false
          j := j + 1
        if matched: match_ok = true then
          found := true
      k := k + 1
    return found

end Implementation

section Proof

theorem period_matches_all (s : Array Char) (k : Nat)
    (hmatched : ∀ j, k ≤ j → j < s.size → s[j]! = s[j % k]!) :
    ∀ i < s.size, s[i]! = s[i % k]! := by
  intro i hi
  by_cases hik : i < k
  · rw [Nat.mod_eq_of_lt hik]
  · have hki : k ≤ i := by omega
    exact hmatched i hki hi

theorem small_postcondition (s : Array Char) (h : s.size ≤ 1) :
    arrayPostcondition s false := by
  unfold arrayPostcondition postcondition
  simp only [Bool.false_eq_true, false_iff]
  rintro ⟨k, hk0, hkn, _⟩
  omega

theorem exit_postcondition_true (s : Array Char)
    (hsound : ∃ kp, 0 < kp ∧ kp < s.size ∧ s.size % kp = 0 ∧ (∀ i < s.size, s[i]! = s[i % kp]!)) :
    arrayPostcondition s true := by
  unfold arrayPostcondition postcondition
  simp only [true_iff]
  exact hsound

theorem exit_postcondition_false (s : Array Char) (k : Nat) (hk : k = s.size)
    (hcomplete : ∀ kp, 0 < kp → kp < k → ¬(s.size % kp = 0 ∧ (∀ i < s.size, s[i]! = s[i % kp]!))) :
    arrayPostcondition s false := by
  unfold arrayPostcondition postcondition
  simp only [Bool.false_eq_true, false_iff]
  rintro ⟨kp, hkp0, hkpn, hmod, hmatch⟩
  subst hk
  exact hcomplete kp hkp0 hkpn ⟨hmod, hmatch⟩

theorem exit_postcondition (s : Array Char) (k : Nat) (found : Bool)
    (hsound : found = true → ∃ kp, 0 < kp ∧ kp < s.size ∧ s.size % kp = 0 ∧ (∀ i < s.size, s[i]! = s[i % kp]!))
    (hcomplete : found = false → ∀ kp, 0 < kp → kp < k → ¬(s.size % kp = 0 ∧ (∀ i < s.size, s[i]! = s[i % kp]!)))
    (hdone : k = s.size ∨ found = true) :
    arrayPostcondition s found := by
  cases found with
  | false =>
      have hk : k = s.size := by
        cases hdone with
        | inl h => exact h
        | inr h => contradiction
      exact exit_postcondition_false s k hk (hcomplete rfl)
  | true =>
      exact exit_postcondition_true s (hsound rfl)

theorem outer_complete_step_mismatch (s : Array Char) (k : Nat)
    (hcomplete : ∀ kp, 0 < kp → kp < k → ¬(s.size % kp = 0 ∧ ∀ i < s.size, s[i]! = s[i % kp]!))
    (hmismatch : ∃ m, m < s.size ∧ s[m]! ≠ s[m % k]!) :
    ∀ kp, 0 < kp → kp < k + 1 → ¬(s.size % kp = 0 ∧ ∀ i < s.size, s[i]! = s[i % kp]!) := by
  intro kp hkp0 hkp_lt ⟨hmod, hmatch⟩
  by_cases heq : kp = k
  · subst heq
    rcases hmismatch with ⟨m, hm, hne⟩
    exact hne (hmatch m hm)
  · have hkp_lt_k : kp < k := by omega
    exact hcomplete kp hkp0 hkp_lt_k ⟨hmod, hmatch⟩

theorem outer_complete_step_not_div (s : Array Char) (k : Nat)
    (hcomplete : ∀ kp, 0 < kp → kp < k → ¬(s.size % kp = 0 ∧ ∀ i < s.size, s[i]! = s[i % kp]!))
    (hnot_div : ¬(s.size % k = 0)) :
    ∀ kp, 0 < kp → kp < k + 1 → ¬(s.size % kp = 0 ∧ ∀ i < s.size, s[i]! = s[i % kp]!) := by
  intro kp hkp0 hkp_lt ⟨hmod, hmatch⟩
  by_cases heq : kp = k
  · subst heq
    exact hnot_div hmod
  · have hkp_lt_k : kp < k := by omega
    exact hcomplete kp hkp0 hkp_lt_k ⟨hmod, hmatch⟩

theorem inner_match_step (s : Array Char) (k j : Nat)
    (hmatch : ∀ m, k ≤ m → m < j → s[m]! = s[m % k]!)
    (heq : s[j]! = s[j % k]!) :
    ∀ m, k ≤ m → m < j + 1 → s[m]! = s[m % k]! := by
  intro m hkm hmj1
  by_cases hmj : m < j
  · exact hmatch m hkm hmj
  · have hmeq : m = j := by omega
    subst hmeq
    exact heq

prove_correct repeatedSubstringPattern by
  velvet_vcgen [repeatedSubstringPattern, postcondition] with try finish
  case repeated_substring =>
    rename_i s
    exact small_postcondition s small
  case repeated_substring =>
    rename_i s
    exact exit_postcondition s k found outer_sound outer_complete outer_done
  case outer_sound =>
    rename_i s
    intro _
    have hj : j = s.size := by
      cases inner_done with
      | inl h => exact h
      | inr h => simp [matched] at h
    have hm : ∀ m, k ≤ m → m < s.size →
        s[m]! = s[m % k]! := by
      intro m hkm hmn
      have hmj : m < j := by rw [hj]; exact hmn
      exact inner_match matched m hkm hmj
    exact ⟨k, by omega, inner_k_bound.2.1, inner_k_bound.2.2,
      period_matches_all s k hm⟩

end Proof

end RepeatedSubstringPattern
