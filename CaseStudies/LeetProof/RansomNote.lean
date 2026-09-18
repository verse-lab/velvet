module

public import Velvet
public meta import Velvet

/-!
## Program description

Given two strings `ransomNote` and `magazine`, return `true` if `ransomNote` can
be constructed by using the letters from `magazine` and `false` otherwise. Each
letter in `magazine` can only be used once in `ransomNote`.

The program is expected to run in O(n * (m + n)) time and O(1) extra space.
-/

namespace RansomNote

section Specs

public def canConstructProp (ransomNote : List Char) (magazine : List Char) : Prop :=
  ∀ c : Char, ransomNote.count c ≤ magazine.count c

public def precondition (_ransomNote : List Char) (_magazine : List Char) : Prop :=
  True

public def postcondition (ransomNote : List Char) (magazine : List Char) (result : Bool) : Prop :=
  (result = true ↔ canConstructProp ransomNote magazine)

end Specs

section Implementation

method canConstruct (ransomNote : List Char) (magazine : List Char)
  returns (result : Bool)
  requires valid: precondition ransomNote magazine
  ensures constructible: postcondition ransomNote magazine result
do
  let mut ok : Bool := true
  let mut rs : List Char := ransomNote
  while' checking: ok = true ∧ rs ≠ []
    invariant suffix: ∃ ps : List Char, ps ++ rs = ransomNote
    invariant prefix_checked: ∃ ps : List Char,
      ps ++ rs = ransomNote ∧
      (ok = true → ∀ c : Char, c ∈ ps → ransomNote.count c ≤ magazine.count c)
    invariant false_witness: ok = false →
      ∃ c : Char, magazine.count c < ransomNote.count c
    invariant false_rs_empty: ok = false → rs = []
    decreasing remaining: rs.length
    done_with finished: ok = false ∨ rs = []
  do
    match rs with
    | [] =>
      rs := []
    | c :: cs =>
      if count_ok: rs.count c ≤ magazine.count c then
        rs := cs
      else
        ok := false
        rs := []
  return ok

end Implementation

section Proof

theorem suffix_step (ransomNote : List Char) (c : Char) (cs : List Char)
    (hsuffix : ∃ ps, ps ++ c :: cs = ransomNote) :
    ∃ ps, ps ++ cs = ransomNote := by
  rcases hsuffix with ⟨ps, hps⟩
  refine ⟨ps ++ [c], ?_⟩
  rw [List.append_assoc]
  exact hps

theorem prefix_checked_step (ransomNote magazine : List Char) (c : Char) (cs : List Char)
    (hok : (c :: cs).count c ≤ magazine.count c)
    (hchecked : ∃ ps, ps ++ c :: cs = ransomNote ∧ (∀ d ∈ ps, ransomNote.count d ≤ magazine.count d)) :
    ∃ ps, ps ++ cs = ransomNote ∧ ∀ d ∈ ps, ransomNote.count d ≤ magazine.count d := by
  rcases hchecked with ⟨ps, hps, hbound⟩
  refine ⟨ps ++ [c], ?_, ?_⟩
  · rw [List.append_assoc]
    exact hps
  · intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · exact hbound d hd
    · rw [List.mem_singleton] at hd
      subst d
      by_cases hc_ps : c ∈ ps
      · exact hbound c hc_ps
      · have h0 : ps.count c = 0 := List.count_eq_zero_of_not_mem hc_ps
        have hcount : ransomNote.count c = (c :: cs).count c := by
          rw [← hps, List.count_append, h0, Nat.zero_add]
        rw [hcount]
        exact hok

theorem false_witness_step (ransomNote magazine : List Char) (c : Char) (cs : List Char)
    (hnot : ¬ (c :: cs).count c ≤ magazine.count c)
    (hsuffix : ∃ ps, ps ++ c :: cs = ransomNote) :
    ∃ w : Char, magazine.count w < ransomNote.count w := by
  rcases hsuffix with ⟨ps, hps⟩
  refine ⟨c, ?_⟩
  have hlt : magazine.count c < (c :: cs).count c := by omega
  have hle : (c :: cs).count c ≤ ransomNote.count c := by
    rw [← hps, List.count_append]
    omega
  omega

theorem postcondition_from_invariants (ransomNote magazine : List Char) (ok : Bool) (rs : List Char)
    (hwitness : ok = false → ∃ c, magazine.count c < ransomNote.count c)
    (hchecked : ∃ ps, ps ++ rs = ransomNote ∧ (ok = true → ∀ c ∈ ps, ransomNote.count c ≤ magazine.count c))
    (hdone : ok = false ∨ rs = []) :
    postcondition ransomNote magazine ok := by
  unfold postcondition canConstructProp
  cases ok with
  | false =>
      simp only [Bool.false_eq_true, false_iff]
      rcases hwitness rfl with ⟨w, hw⟩
      intro hcan
      have hle := hcan w
      omega
  | true =>
      have hrs : rs = [] := by
        cases hdone with
        | inl h => contradiction
        | inr h => exact h
      rcases hchecked with ⟨ps, hps, hall⟩
      rw [hrs, List.append_nil] at hps
      subst ps
      have hcan : ∀ c, ransomNote.count c ≤ magazine.count c := by
        intro c
        by_cases hc : c ∈ ransomNote
        · exact hall rfl c hc
        · have h0 : ransomNote.count c = 0 := List.count_eq_zero_of_not_mem hc
          omega
      simp [hcan]

prove_correct canConstruct by
  velvet_vcgen [canConstruct, postcondition] with try finish
  case suffix =>
    exact ⟨[], rfl⟩
  case prefix_checked =>
    exact ⟨[], rfl, by simp⟩
  case constructible =>
    rename_i ransomNote magazine
    exact postcondition_from_invariants ransomNote magazine ok rs false_witness prefix_checked finished
  case suffix =>
    rename_i ransomNote _
    rw [h_cons] at suffix
    exact suffix_step ransomNote c cs suffix
  case prefix_checked =>
    rename_i ransomNote magazine
    rw [h_cons] at prefix_checked count_ok
    have hch : ∃ ps, ps ++ c :: cs = ransomNote ∧ (∀ d ∈ ps, ransomNote.count d ≤ magazine.count d) := by
      rcases prefix_checked with ⟨ps, hps, hchk⟩
      exact ⟨ps, hps, hchk checking.1⟩
    rcases prefix_checked_step ransomNote magazine c cs count_ok hch with ⟨ps, hps, hall⟩
    exact ⟨ps, hps, fun _ => hall⟩
  case suffix =>
    rename_i ransomNote _
    exact ⟨ransomNote, by simp⟩
  case prefix_checked =>
    rename_i ransomNote _
    exact ⟨ransomNote, by simp⟩

end Proof

end RansomNote
