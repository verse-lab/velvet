module

public import Velvet
public meta import Velvet

/-!
## Program description

Given two strings `s` and `t`, determine if they are isomorphic.

Two strings `s` and `t` are isomorphic if the characters in `s` can be replaced
to get `t`.

All occurrences of a character must be replaced with the same character while
preserving the order of characters. No two characters may map to the same
character, but a character may map to itself.

The program is expected to run in O(n^2) time and O(1) extra space.
-/

namespace IsomorphicStrings

section Specs

public def Isomorphic (s : Array Char) (t : Array Char) : Prop :=
  s.size = t.size ∧
    ∀ (i : Nat) (j : Nat),
      i < s.size → j < s.size →
        ((s[i]! = s[j]!) ↔ (t[i]! = t[j]!))

public def precondition (_s : Array Char) (_t : Array Char) : Prop :=
  True

public def postcondition (s : Array Char) (t : Array Char) (result : Bool) : Prop :=
  (result = true ↔ Isomorphic s t)

end Specs

section Implementation

method isIsomorphic (s : Array Char) (t : Array Char)
  returns (result : Bool)
  requires valid: precondition s t
  ensures isomorphic: postcondition s t result
do
  if len_neq: s.size ≠ t.size then
    return false
  let n := s.size
  let mut i : Nat := 0
  let mut ok : Bool := true
  while outer_scan: i < n ∧ ok = true
    invariant outer_bounds: i ≤ n
    invariant outer_checked: ok = true →
      ∀ p q : Nat, p < i → q < n → p < q → ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!))
    invariant outer_cex: ok = false →
      ∃ p q : Nat, p < q ∧ q < n ∧ ¬ ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!))
    decreasing outer_remaining: n - i
    done_with outer_done: i = n ∨ ok = false
  do
    let mut j : Nat := i + 1
    while inner_scan: j < n ∧ ok = true
      invariant inner_bounds: i < n ∧ i + 1 ≤ j ∧ j ≤ n
      invariant inner_prev_outer: ok = true →
        ∀ p q : Nat, p < i → q < n → p < q → ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!))
      invariant inner_checked_i: ok = true →
        ∀ q : Nat, i < q → q < j → ((s[i]! = s[q]!) ↔ (t[i]! = t[q]!))
      invariant inner_cex: ok = false →
        ∃ p q : Nat, p < q ∧ q < n ∧ ¬ ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!))
      decreasing inner_remaining: n - j
      done_with inner_done: j = n ∨ ok = false
    do
      if s_eq: s[i]! = s[j]! then
        if t_ne: t[i]! ≠ t[j]! then
          ok := false
      else
        if t_eq: t[i]! = t[j]! then
          ok := false
      j := j + 1
    i := i + 1
  return ok

end Implementation

section Proof

theorem not_isomorphic_of_len_neq (s t : Array Char)
    (hne : s.size ≠ t.size) :
    postcondition s t false := by
  unfold postcondition Isomorphic
  simp only [Bool.false_eq_true, false_iff]
  rintro ⟨hlen, _⟩
  exact hne hlen

theorem isomorphic_of_checked (s t : Array Char)
    (hlen : s.size = t.size)
    (hchecked : ∀ p q : Nat, p < s.size → q < s.size → p < q →
      ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!))) :
    Isomorphic s t := by
  unfold Isomorphic
  refine ⟨hlen, fun i j hi hj => ?_⟩
  by_cases hij : i < j
  · exact hchecked i j hi hj hij
  · by_cases hji : j < i
    · have h' := hchecked j i hj hi hji
      constructor
      · intro hs
        exact (h'.mp hs.symm).symm
      · intro ht
        exact (h'.mpr ht.symm).symm
    · have : i = j := by omega
      subst j
      simp

theorem not_isomorphic_of_cex (s t : Array Char)
    (hcex : ∃ p q : Nat, p < q ∧ q < s.size ∧
      ¬ ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!))) :
    ¬ Isomorphic s t := by
  intro hiso
  unfold Isomorphic at hiso
  rcases hcex with ⟨p, q, hpq, hq, hnot⟩
  have hq' : q < s.size := hq
  have hp' : p < s.size := Nat.lt_trans hpq hq'
  have hpair := hiso.2 p q hp' hq'
  exact hnot hpair

theorem postcondition_from_loop (s t : Array Char)
    (hlen : s.size = t.size) (ok : Bool) (i : Nat)
    (_hbounds : i ≤ s.size)
    (hchecked : ok = true → ∀ p q : Nat, p < i → q < s.size → p < q →
      ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!)))
    (hcex : ok = false → ∃ p q : Nat, p < q ∧ q < s.size ∧
      ¬ ((s[p]! = s[q]!) ↔ (t[p]! = t[q]!)))
    (hdone : i = s.size ∨ ok = false) :
    postcondition s t ok := by
  unfold postcondition
  cases ok with
  | false =>
      simp only [Bool.false_eq_true, false_iff]
      exact not_isomorphic_of_cex s t (hcex rfl)
  | true =>
      simp only [true_iff]
      have hi : i = s.size := by
        cases hdone with
        | inl h => exact h
        | inr h => contradiction
      subst i
      exact isomorphic_of_checked s t hlen (hchecked rfl)

prove_correct isIsomorphic by
  velvet_vcgen [isIsomorphic, postcondition] with try finish
  case isomorphic =>
    rename_i s t
    exact not_isomorphic_of_len_neq s t len_neq
  case isomorphic =>
    rename_i s t
    have hlen : s.size = t.size := Classical.not_not.mp len_neq
    exact postcondition_from_loop s t hlen ok i outer_bounds outer_checked outer_cex outer_done

end Proof

end IsomorphicStrings
