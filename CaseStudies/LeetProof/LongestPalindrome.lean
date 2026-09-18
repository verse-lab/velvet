module

public import Velvet
public meta import Velvet
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
## Program description

Given a sequence of case-sensitive letters, compute the maximum length of a
palindrome buildable from those letters.

1. Input is a list of characters; characters are case sensitive (e.g., 'A' and 'a' are distinct).
2. We may reorder the input characters and select any multiset of them, using each character at most as many times as it appears in the input.
3. A list of characters is a palindrome exactly when it equals its reverse.
4. A candidate palindrome is buildable from the input when, for every character c, its count in the candidate is at most its count in the input.
5. The function returns the maximum possible length among all buildable palindromes.
6. If the input is empty, the maximum palindrome length is 0.

The program is expected to run in O(n^2) time and O(1) extra space.
-/

namespace LongestPalindrome

section Specs

public def isPalindrome (t : List Char) : Prop :=
  t.reverse = t

public def usesLetters (s : List Char) (t : List Char) : Prop :=
  ∀ (c : Char), t.count c ≤ s.count c

public def buildablePalindrome (s : List Char) (t : List Char) : Prop :=
  isPalindrome t ∧ usesLetters s t

public def precondition (_s : Array Char) : Prop :=
  True

public def postcondition (s : Array Char) (result : Nat) : Prop :=
  (∃ (t : List Char), buildablePalindrome s.toList t ∧ t.length = result) ∧
  (∀ (t : List Char), buildablePalindrome s.toList t → t.length ≤ result)

end Specs

section Implementation

public def pairsCount (s : List Char) : Nat :=
  (s.eraseDups.map (fun c => s.count c / 2)).sum

public def hasOddCount (s : List Char) : Bool :=
  s.eraseDups.any (fun c => s.count c % 2 == 1)

public def maxPalindromeLen (s : List Char) : Nat :=
  2 * pairsCount s + (if hasOddCount s then 1 else 0)

public def pairSumKeys (s keys : List Char) : Nat :=
  (keys.map (fun c => s.count c / 2)).sum

public def oddInKeys (s keys : List Char) : Bool :=
  keys.any (fun c => s.count c % 2 == 1)

public def buildHalf (s : List Char) : List Char :=
  s.eraseDups.flatMap (fun c => List.replicate (s.count c / 2) c)

public def buildMid (s : List Char) : List Char :=
  match s.eraseDups.find? (fun c => s.count c % 2 == 1) with
  | some c => [c]
  | none => []

public def buildCandidate (s : List Char) : List Char :=
  let half := buildHalf s
  half ++ buildMid s ++ half.reverse

method longestPalindrome (s : Array Char)
  returns (result : Nat)
  requires valid: precondition s
  ensures max_len: postcondition s result
do
  let n := s.size
  let mut pairCount : Nat := 0
  let mut hasOdd : Bool := false
  let mut i : Nat := 0
  while scanning: i < n
    invariant i_bound: i ≤ n
    invariant pairs_scanned:
      pairCount = pairSumKeys s.toList (s.toList.take i).eraseDups
    invariant odd_scanned:
      hasOdd = oddInKeys s.toList (s.toList.take i).eraseDups
    decreasing remaining: n - i
    done_with done: i = n
  do
    let c := s[i]!
    let mut seenBefore : Bool := false
    let mut k : Nat := 0
    while checking_seen: k < i ∧ seenBefore = false
      invariant k_bound: k ≤ i
      invariant no_seen:
        seenBefore = false → ∀ p, p < k → s[p]! ≠ c
      invariant did_see:
        seenBefore = true → ∃ p, p < k ∧ s[p]! = c
      decreasing seen_remaining: i - k
      done_with seen_checked:
        seenBefore = true ↔ ∃ p, p < i ∧ s[p]! = c
    do
      if s[k]! = c then
        seenBefore := true
      k := k + 1
    if seenBefore = false then
      let mut cnt : Nat := 0
      let mut j : Nat := 0
      while counting: j < n
        invariant j_bound: j ≤ n
        invariant count_scanned:
          cnt = (s.toList.take j).count c
        decreasing count_decreasing: n - j
        done_with counted: j = n
      do
        if s[j]! = c then
          cnt := cnt + 1
        j := j + 1
      pairCount := pairCount + cnt / 2
      if cnt % 2 = 1 then
        hasOdd := true
    i := i + 1
  return 2 * pairCount + (if hasOdd then 1 else 0)

end Implementation

section Proof

theorem isPalindrome_buildCandidate (s : List Char) :
    isPalindrome (buildCandidate s) := by
  unfold isPalindrome buildCandidate buildMid
  cases s.eraseDups.find? (fun c => s.count c % 2 == 1) <;> simp

theorem length_buildHalf (s : List Char) :
    (buildHalf s).length = pairsCount s := by
  unfold buildHalf pairsCount
  induction s.eraseDups with
  | nil => rfl
  | cons c cs ih =>
    simp [ih]

theorem length_buildMid (s : List Char) :
    (buildMid s).length = if hasOddCount s then 1 else 0 := by
  unfold buildMid hasOddCount
  cases h : s.eraseDups.find? (fun c => s.count c % 2 == 1) with
  | none =>
    have hnone : (s.eraseDups.any (fun c => s.count c % 2 == 1)) = false := by
      rw [List.any_eq_false]
      intro c hc
      have h' := List.find?_eq_none.mp h c hc
      simpa using h'
    simp [hnone]
  | some c =>
    have hsome : (s.eraseDups.any (fun c => s.count c % 2 == 1)) = true := by
      rw [List.any_eq_true]
      have hc_mem := List.mem_of_find?_eq_some h
      have hc_prop := List.find?_some (p := fun c => s.count c % 2 == 1) (l := s.eraseDups) h
      exact ⟨c, hc_mem, hc_prop⟩
    simp [hsome]

theorem length_buildCandidate (s : List Char) :
    (buildCandidate s).length = maxPalindromeLen s := by
  unfold buildCandidate maxPalindromeLen
  simp [length_buildHalf, length_buildMid]
  omega

theorem count_replicate (n : Nat) (x c : Char) :
    (List.replicate n x).count c = if c = x then n else 0 := by
  by_cases hcx : c = x
  · subst hcx
    simp
  · have hne : (x == c) = false := beq_false_of_ne (Ne.symm hcx)
    induction n with
    | zero => simp [hcx]
    | succ n ih =>
      simp [List.replicate_succ, List.count_cons, hne, ih, hcx]

theorem count_flatMap_replicate (l : List Char) (hl : l.Nodup) (c : Char) (f : Char → Nat) :
    (l.flatMap (fun x => List.replicate (f x) x)).count c = if c ∈ l then f c else 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    have hx_not_mem := hl.1
    have hxs_nodup := hl.2
    simp only [List.flatMap_cons, List.count_append, List.mem_cons]
    rw [count_replicate, ih hxs_nodup]
    by_cases hcx : c = x
    · subst hcx
      have hc_not_xs : ¬ c ∈ xs := hx_not_mem
      simp [hc_not_xs]
    · simp [hcx]

theorem nodup_reverse (l : List Char) (h : l.Nodup) : l.reverse.Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    simp only [List.reverse_cons]
    rw [List.nodup_append]
    refine ⟨ih h.2, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    rw [List.mem_reverse] at ha
    intro h_eq
    subst h_eq
    exact h.1 ha

theorem nodup_eraseDupsBy_loop (l acc : List Char) (hacc : acc.Nodup) :
    (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc).Nodup := by
  induction l generalizing acc with
  | nil =>
    simp only [List.eraseDupsBy.loop]
    exact nodup_reverse acc hacc
  | cons x xs ih =>
    simp only [List.eraseDupsBy.loop]
    cases h : acc.any (fun x2 => x == x2)
    · apply ih (x :: acc)
      rw [List.nodup_cons]
      refine ⟨?_, hacc⟩
      intro hx
      rw [List.any_eq_false] at h
      have := h x hx
      simp at this
    · exact ih acc hacc

theorem nodup_eraseDups (l : List Char) : l.eraseDups.Nodup := by
  unfold List.eraseDups List.eraseDupsBy
  exact nodup_eraseDupsBy_loop l [] (by simp)

theorem count_buildHalf (s : List Char) (c : Char) :
    (buildHalf s).count c = s.count c / 2 := by
  unfold buildHalf
  have h_nd : s.eraseDups.Nodup := nodup_eraseDups s
  have h := count_flatMap_replicate s.eraseDups h_nd c (fun x => s.count x / 2)
  rw [h]
  by_cases hc : c ∈ s.eraseDups
  · simp [hc]
  · rw [List.mem_eraseDups] at hc
    have hc0 : s.count c = 0 := List.count_eq_zero_of_not_mem hc
    simp [hc, hc0]

theorem usesLetters_buildCandidate (s : List Char) :
    usesLetters s (buildCandidate s) := by
  intro c
  unfold buildCandidate buildMid
  simp only [List.count_append, List.count_reverse, count_buildHalf]
  cases h : s.eraseDups.find? (fun x => s.count x % 2 == 1) with
  | none =>
    simp
    omega
  | some midChar =>
    simp only
    have hprop := List.find?_some (p := fun x => s.count x % 2 == 1) (l := s.eraseDups) h
    have hodd : s.count midChar % 2 = 1 := by simpa using hprop
    by_cases hc : c = midChar
    · subst hc
      simp
      omega
    · have hne : (midChar == c) = false := beq_false_of_ne (Ne.symm hc)
      simp [List.count_cons, hne]
      omega

theorem sum_map_le (keys : List Char) (f g : Char → Nat) (h : ∀ c ∈ keys, f c ≤ g c) :
    (keys.map f).sum ≤ (keys.map g).sum := by
  induction keys with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h k (by simp)
    have h2 := ih (fun c hc => h c (List.mem_cons_of_mem k hc))
    omega

theorem sum_map_add (keys : List Char) (f g : Char → Nat) :
    (keys.map (fun c => f c + g c)).sum = (keys.map f).sum + (keys.map g).sum := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_if_pos (keys : List Char) (x : Char) (hx : x ∈ keys) :
    1 ≤ (keys.map (fun c => if c = x then 1 else 0)).sum := by
  induction keys with
  | nil => cases hx
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hkx : k = x
    · simp [hkx]
    · have hx_ks : x ∈ ks := by
        cases hx with
        | head => contradiction
        | tail _ h => exact h
      have := ih hx_ks
      omega

theorem count_cons_eq (c x : Char) (xs : List Char) :
    (x :: xs).count c = xs.count c + (if c = x then 1 else 0) := by
  by_cases hcx : c = x
  · subst hcx
    simp
  · have hne : (x == c) = false := beq_false_of_ne (Ne.symm hcx)
    simp [List.count_cons, hne, hcx]

theorem length_le_sum_count (l : List Char) (keys : List Char) (h_sub : ∀ x ∈ l, x ∈ keys) :
    l.length ≤ (keys.map (fun c => l.count c)).sum := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have h_sub_xs : ∀ a ∈ xs, a ∈ keys := fun a ha => h_sub a (List.mem_cons_of_mem x ha)
    have hx_keys : x ∈ keys := h_sub x (by simp)
    have h_map_eq : keys.map (fun c => (x :: xs).count c) = keys.map (fun c => xs.count c + (if c = x then 1 else 0)) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp [count_cons_eq]
    rw [h_map_eq, sum_map_add]
    have h1 := ih h_sub_xs
    have h2 := sum_map_if_pos keys x hx_keys
    simp only [List.length_cons]
    omega

theorem count_take_le (n : Nat) (l : List Char) (c : Char) :
    (l.take n).count c ≤ l.count c := by
  have := (List.count_append (l₁ := l.take n) (l₂ := l.drop n) (a := c)).symm
  rw [List.take_append_drop] at this
  omega

theorem count_take_le_half_count (t : List Char) (ht : isPalindrome t) (c : Char) :
    (t.take (t.length / 2)).count c ≤ t.count c / 2 := by
  have h_rev : t.count c = (t.take (t.length / 2)).count c + (t.drop (t.length / 2)).count c := by
    have := (List.count_append (l₁ := t.take (t.length / 2)) (l₂ := t.drop (t.length / 2)) (a := c)).symm
    rw [List.take_append_drop] at this
    exact this.symm
  have h_drop_ge : (t.take (t.length / 2)).count c ≤ (t.drop (t.length / 2)).count c := by
    unfold isPalindrome at ht
    have h_eq : (t.drop (t.length / 2)).count c = (t.take (t.length - t.length / 2)).count c := by
      rw [← List.count_reverse (l := t.drop (t.length / 2)), List.reverse_drop, ht]
    rw [h_eq]
    have h_le_len : t.length / 2 ≤ t.length - t.length / 2 := by omega
    have h_take_sub : t.take (t.length / 2) = (t.take (t.length - t.length / 2)).take (t.length / 2) := by
      rw [List.take_take, Nat.min_eq_left h_le_len]
    conv => lhs; rw [h_take_sub]
    exact count_take_le (t.length / 2) (t.take (t.length - t.length / 2)) c
  omega

theorem buildablePalindrome_buildCandidate (s : List Char) :
    buildablePalindrome s (buildCandidate s) ∧ (buildCandidate s).length = maxPalindromeLen s := by
  refine ⟨⟨isPalindrome_buildCandidate s, usesLetters_buildCandidate s⟩, length_buildCandidate s⟩

theorem palindrome_length_le_one_more (s t : List Char) (ht : buildablePalindrome s t) :
    t.length ≤ 2 * pairsCount s + 1 := by
  let half := t.take (t.length / 2)
  have hmem : ∀ c ∈ half, c ∈ s.eraseDups := by
    intro c hc
    have hct : c ∈ t := List.mem_of_mem_take hc
    have hpos_t : 0 < t.count c := List.count_pos_iff.mpr hct
    have hpos_s : 0 < s.count c := Nat.lt_of_lt_of_le hpos_t (ht.2 c)
    simpa using (List.count_pos_iff.mp hpos_s)
  have hhalf : half.length ≤ pairsCount s := by
    calc
      half.length ≤ (s.eraseDups.map (fun c => half.count c)).sum :=
        length_le_sum_count half s.eraseDups hmem
      _ ≤ (s.eraseDups.map (fun c => s.count c / 2)).sum := by
        apply sum_map_le
        intro c _hc
        exact Nat.le_trans (count_take_le_half_count t ht.1 c)
          (Nat.div_le_div_right (ht.2 c))
      _ = pairsCount s := rfl
  have hhalf_len : half.length = t.length / 2 := by
    simp [half, Nat.min_eq_left (Nat.div_le_self _ _)]
  omega

theorem length_le_of_usesLetters (s t : List Char) (h : usesLetters s t) :
    t.length ≤ s.length := by
  exact ((List.subperm_iff_count).2 h).length_le

theorem sum_counts_eraseDups (s : List Char) :
    (s.eraseDups.map (fun c => s.count c)).sum = s.length := by
  rw [← List.sum_toFinset (fun c => s.count c) (nodup_eraseDups s)]
  have hkeys : s.eraseDups.toFinset = s.toFinset := by
    ext c
    simp
  rw [hkeys]
  exact List.sum_toFinset_count_eq_length s

theorem counts_even_of_no_odd (s : List Char) (hodd : hasOddCount s = false) :
    ∀ c ∈ s, s.count c % 2 = 0 := by
  intro c hc
  have hc_keys : c ∈ s.eraseDups := by simpa using hc
  unfold hasOddCount at hodd
  rw [List.any_eq_false] at hodd
  have hc_not_odd := hodd c hc_keys
  have hmod_lt : s.count c % 2 < 2 := Nat.mod_lt _ (by omega)
  simp only [beq_iff_eq] at hc_not_odd
  omega

theorem pairs_formula_of_no_odd (s : List Char) (hodd : hasOddCount s = false) :
    2 * pairsCount s = s.length := by
  have heven := counts_even_of_no_odd s hodd
  unfold pairsCount
  have hscale : ∀ keys : List Char,
      2 * (keys.map (fun c => s.count c / 2)).sum =
        (keys.map (fun c => 2 * (s.count c / 2))).sum := by
    intro keys
    induction keys with
    | nil => rfl
    | cons c cs ih =>
        simp only [List.map_cons, List.sum_cons]
        omega
  calc
    2 * (s.eraseDups.map (fun c => s.count c / 2)).sum =
        (s.eraseDups.map (fun c => 2 * (s.count c / 2))).sum := hscale s.eraseDups
    (s.eraseDups.map (fun c => 2 * (s.count c / 2))).sum =
        (s.eraseDups.map (fun c => s.count c)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro c hc
      have hc_s : c ∈ s := by simpa using hc
      exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (heven c hc_s))
    _ = s.length := sum_counts_eraseDups s

theorem take_succ_getD (s : List Char) (i : Nat) (hi : i < s.length) :
    s.take (i + 1) = s.take i ++ [s[i]?.getD 'A'] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp

theorem mem_take_iff_getD (s : List Char) (c : Char) (i : Nat) (hi : i ≤ s.length) :
    c ∈ s.take i ↔ ∃ p, p < i ∧ s[p]?.getD 'A' = c := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨p, hp, heq⟩
    have hp_i : p < i := by omega
    have hp_s : p < s.length := by omega
    refine ⟨p, hp_i, ?_⟩
    simpa [List.getElem?_eq_getElem hp_s] using heq
  · rintro ⟨p, hp, heq⟩
    have hp_s : p < s.length := by omega
    refine ⟨p, by omega, ?_⟩
    simpa [List.getElem?_eq_getElem hp_s] using heq

theorem singleton_removeAll (c : Char) (l : List Char) :
    [c].removeAll l = if c ∈ l then [] else [c] := by
  by_cases h : c ∈ l <;> simp [List.removeAll, h]

theorem singleton_eraseDups (c : Char) : [c].eraseDups = [c] := by
  rfl

theorem pairSum_take_succ_new (s : List Char) (i : Nat) (hi : i < s.length)
    (hnew : s[i]?.getD 'A' ∉ s.take i) :
    pairSumKeys s (s.take (i + 1)).eraseDups =
      pairSumKeys s (s.take i).eraseDups + s.count (s[i]?.getD 'A') / 2 := by
  rw [take_succ_getD s i hi, List.eraseDups_append, singleton_removeAll]
  simp [pairSumKeys, hnew, singleton_eraseDups]

theorem pairSum_take_succ_old (s : List Char) (i : Nat) (hi : i < s.length)
    (hold : s[i]?.getD 'A' ∈ s.take i) :
    pairSumKeys s (s.take (i + 1)).eraseDups = pairSumKeys s (s.take i).eraseDups := by
  rw [take_succ_getD s i hi, List.eraseDups_append, singleton_removeAll]
  simp [pairSumKeys, hold]

theorem odd_take_succ_new (s : List Char) (i : Nat) (hi : i < s.length)
    (hnew : s[i]?.getD 'A' ∉ s.take i) :
    oddInKeys s (s.take (i + 1)).eraseDups =
      (oddInKeys s (s.take i).eraseDups ||
        (s.count (s[i]?.getD 'A') % 2 == 1)) := by
  rw [take_succ_getD s i hi, List.eraseDups_append, singleton_removeAll]
  simp [oddInKeys, hnew, singleton_eraseDups, Bool.or_comm]

theorem odd_take_succ_old (s : List Char) (i : Nat) (hi : i < s.length)
    (hold : s[i]?.getD 'A' ∈ s.take i) :
    oddInKeys s (s.take (i + 1)).eraseDups = oddInKeys s (s.take i).eraseDups := by
  rw [take_succ_getD s i hi, List.eraseDups_append, singleton_removeAll]
  simp [oddInKeys, hold]

@[simp] theorem toList_getElem?_getD (s : Array Char) (i : Nat) (hi : i < s.size) :
    s.toList[i]?.getD 'A' = s[i]! := by
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp [getElem!_pos, hi]

@[simp] theorem array_getElem?_getD (s : Array Char) (i : Nat) (hi : i < s.size) :
    s[i]?.getD 'A' = s[i]! := by
  rw [Array.getElem?_eq_getElem hi]
  simp [getElem!_pos, hi]

@[simp] theorem toList_take_size (s : Array Char) :
    s.toList.take s.size = s.toList := by
  simp

theorem toList_getElem?_eq_some (s : Array Char) (i : Nat) (hi : i < s.size) :
    s.toList[i]? = some s[i] := by
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem maxPalindromeLen_correct (s : List Char) :
    (∃ (t : List Char), buildablePalindrome s t ∧ t.length = maxPalindromeLen s) ∧
    (∀ (t : List Char), buildablePalindrome s t → t.length ≤ maxPalindromeLen s) := by
  refine ⟨⟨buildCandidate s, (buildablePalindrome_buildCandidate s).1,
    length_buildCandidate s⟩, ?_⟩
  intro t ht
  cases hodd : hasOddCount s with
  | false =>
      have hformula := pairs_formula_of_no_odd s hodd
      have hlen := length_le_of_usesLetters s t ht.2
      simp [maxPalindromeLen, hodd]
      omega
  | true =>
      have hlen := palindrome_length_le_one_more s t ht
      simp [maxPalindromeLen, hodd]
      exact hlen

prove_correct longestPalindrome by
  velvet_vcgen [longestPalindrome]
  all_goals simp_all [pairSumKeys, oddInKeys] <;> try omega
  case pairs_scanned =>
    rename_i s
    have hi : i < s.toList.length := by simpa using scanning
    have hnew : s.toList[i]?.getD 'A' ∉ s.toList.take i := by
      rw [mem_take_iff_getD _ _ _ (by omega)]
      rintro ⟨p, hp, heq⟩
      apply seen_checked p hp
      simpa [array_getElem?_getD s p (by omega), array_getElem?_getD s i (by omega),
        getElem!_pos s i scanning] using heq
    simpa [pairSumKeys, array_getElem?_getD s i (by omega), toList_take_size,
      getElem!_pos s i scanning] using
      (pairSum_take_succ_new s.toList i hi hnew).symm
  case odd_scanned =>
    rename_i s
    have hi : i < s.toList.length := by simpa using scanning
    refine ⟨s[i]!, ?_, ?_⟩
    rw [take_succ_getD s.toList i hi]
    simp [array_getElem?_getD s i (by omega)]
    simpa [toList_take_size, getElem!_pos s i scanning] using if_cond_1
  case pairs_scanned =>
    rename_i s
    have hi : i < s.toList.length := by simpa using scanning
    have hnew : s.toList[i]?.getD 'A' ∉ s.toList.take i := by
      rw [mem_take_iff_getD _ _ _ (by omega)]
      rintro ⟨p, hp, heq⟩
      apply seen_checked p hp
      simpa [array_getElem?_getD s p (by omega), array_getElem?_getD s i (by omega),
        getElem!_pos s i scanning] using heq
    simpa [pairSumKeys, array_getElem?_getD s i (by omega), toList_take_size,
      getElem!_pos s i scanning] using
      (pairSum_take_succ_new s.toList i hi hnew).symm
  case odd_scanned =>
    rename_i s
    have hi : i < s.toList.length := by simpa using scanning
    have hnew : s.toList[i]?.getD 'A' ∉ s.toList.take i := by
      rw [mem_take_iff_getD _ _ _ (by omega)]
      rintro ⟨p, hp, heq⟩
      apply seen_checked p hp
      simpa [array_getElem?_getD s p (by omega), array_getElem?_getD s i (by omega),
        getElem!_pos s i scanning] using heq
    simpa [oddInKeys, array_getElem?_getD s i (by omega), toList_take_size,
      getElem!_pos s i scanning, if_cond_1] using
      (odd_take_succ_new s.toList i hi hnew).symm
  case count_scanned =>
    rw [List.take_add_one]
    rw [toList_getElem?_eq_some _ _ counting]
    simp [if_cond_1]
  case count_scanned =>
    rw [List.take_add_one]
    rw [toList_getElem?_eq_some _ _ counting]
    simp [List.count_cons, beq_false_of_ne if_cond_1]
  case pairs_scanned =>
    rename_i s
    have hi : i < s.toList.length := by simpa using scanning
    have hold : s.toList[i]?.getD 'A' ∈ s.toList.take i := by
      rw [mem_take_iff_getD _ _ _ (by omega)]
      rcases seen_checked with ⟨p, hp, heq⟩
      exact ⟨p, hp, by simpa [array_getElem?_getD s p (by omega),
        array_getElem?_getD s i (by omega), getElem!_pos s i scanning] using heq⟩
    simpa [pairSumKeys] using (pairSum_take_succ_old s.toList i hi hold).symm
  case odd_scanned =>
    rename_i s
    have hi : i < s.toList.length := by simpa using scanning
    have hold : s.toList[i]?.getD 'A' ∈ s.toList.take i := by
      rw [mem_take_iff_getD _ _ _ (by omega)]
      rcases seen_checked with ⟨p, hp, heq⟩
      exact ⟨p, hp, by simpa [array_getElem?_getD s p (by omega),
        array_getElem?_getD s i (by omega), getElem!_pos s i scanning] using heq⟩
    simpa [oddInKeys] using (odd_take_succ_old s.toList i hi hold).symm
  case did_see =>
    exact ⟨k, by omega, if_cond⟩
  case no_seen =>
    intro p hp
    by_cases hpk : p < k
    · exact no_seen p hpk
    · have : p = k := by omega
      simpa [this] using if_cond
  case seen_checked =>
    constructor
    · intro h
      rcases did_see h with ⟨p, hp, heq⟩
      exact ⟨p, by omega, heq⟩
    · intro h
      by_contra hn
      have hf : seenBefore = false := by cases seenBefore <;> simp_all
      by_cases hki : k < i
      · have ht := checking_seen hki
        rw [hf] at ht
        contradiction
      · rcases h with ⟨p, hp, heq⟩
        exact no_seen hf p (by omega) heq
  case max_len =>
    rename_i s
    have hcorrect := maxPalindromeLen_correct s.toList
    simpa [postcondition, maxPalindromeLen, pairsCount, hasOddCount,
      List.any_eq_true, toList_take_size] using hcorrect

end Proof

end LongestPalindrome
