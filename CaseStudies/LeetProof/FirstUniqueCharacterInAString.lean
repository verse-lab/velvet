module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Nat.Find

/-!
## Program description

Given a string `s`, find the first non-repeating character in it and return its
index. If it does not exist, return `-1`.

1. The input is a finite sequence of characters `s` indexed from 0.
2. A character at index `i` is non-repeating (unique) if it occurs in `s` exactly once.
3. If there exists at least one index `i` whose character is unique, the function returns the smallest such index.
4. If no unique character exists, the function returns -1.
5. All characters are ASCII, meaning each character code is < 128.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace FirstUniqueCharacterInAString

section Specs

public def charCount (s : Array Char) (c : Char) : Nat :=
  s.countP (fun x => x = c)

public def isASCII (c : Char) : Prop := c.toNat < 128

public def precondition (s : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → isASCII (s[i]!)

public def postcondition (s : Array Char) (result : Int) : Prop :=
  ((∃ (i : Nat), i < s.size ∧ charCount s (s[i]!) = 1) →
      0 ≤ result ∧
      (result.toNat < s.size) ∧
      charCount s (s[result.toNat]!) = 1 ∧
      (∀ (j : Nat), j < result.toNat → charCount s (s[j]!) ≠ 1))
  ∧
  ((¬ (∃ (i : Nat), i < s.size ∧ charCount s (s[i]!) = 1)) →
      result = (-1) ∧
      (∀ (i : Nat), i < s.size → charCount s (s[i]!) ≠ 1))

end Specs

section Implementation

public def countStep (counts : Array Nat) (ch : Char) : Array Nat :=
  if ch.toNat < 128 then counts.set! ch.toNat (counts[ch.toNat]! + 1) else counts

public def countGo (s : Array Char) (i : Nat) (counts : Array Nat) : Array Nat :=
  if i < s.size then countGo s (i + 1) (countStep counts s[i]!) else counts
termination_by s.size - i

public def findFirstGo (s : Array Char) (counts : Array Nat) (j : Nat) : Int :=
  if j < s.size then
    let ch := s[j]!
    if ch.toNat < 128 ∧ counts[ch.toNat]! = 1 then
      Int.ofNat j
    else
      findFirstGo s counts (j + 1)
  else
    -1
termination_by s.size - j

public def firstUniqueCharIndex (s : Array Char) : Int :=
  let counts := countGo s 0 (Array.replicate 128 0)
  findFirstGo s counts 0

method firstUniqChar (s : Array Char)
  returns (result : Int)
  requires valid: precondition s
  ensures first_uniq: postcondition s result
do
  let mut counts : Array Nat := Array.replicate 128 0
  let mut i : Nat := 0
  while' counting: i < s.size
    invariant count_bounds: i ≤ s.size
    invariant count_continuation:
      countGo s i counts = countGo s 0 (Array.replicate 128 0)
    decreasing count_remaining: s.size - i
    done_with counted: i = s.size
  do
    let ch := s[i]!
    let code := ch.toNat
    if in_ascii: code < 128 then
      let cur := counts[code]!
      counts := counts.set! code (cur + 1)
    i := i + 1
  let mut j : Nat := 0
  let mut ans : Int := -1
  let mut found : Bool := false
  while' searching: j < s.size ∧ found = false
    invariant search_bounds: j ≤ s.size
    invariant search_ans: found = true → ans = firstUniqueCharIndex s
    invariant search_continuation:
      found = false → findFirstGo s counts j = firstUniqueCharIndex s
    invariant not_found: found = false → ans = -1
    decreasing search_remaining: if found then 0 else s.size - j
    done_with done_search: j = s.size ∨ found = true
  do
    let ch := s[j]!
    let code := ch.toNat
    if in_ascii2: code < 128 then
      if uniq: counts[code]! = 1 then
        ans := Int.ofNat j
        found := true
      else
        j := j + 1
    else
      j := j + 1
  return ans

end Implementation

section Proof

theorem getElem!_set! (a : Array Nat) (i j v : Nat)
    (hi : i < a.size) (hj : j < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hji : j = i
  · subst j
    simp [Array.set!, Array.setIfInBounds, hi, getElem!_pos]
  · rw [getElem!_pos _ _ (by simpa [Array.size_set!])]
    rw [getElem!_pos a j hj]
    simp only [Array.set!, Array.setIfInBounds, dite_eq_left hi, ite_eq_right hji]
    exact Array.getElem_set_ne hi hj (fun h => hji h.symm)

theorem countGo_eq_drop_foldl (s : Array Char) (i : Nat) (counts : Array Nat) :
    countGo s i counts = (s.toList.drop i).foldl countStep counts := by
  fun_induction countGo s i counts
  case case1 idx arr hscan ih =>
    have hdrop : s.toList.drop idx = s[idx]! :: s.toList.drop (idx + 1) := by
      have hd := List.drop_eq_getElem_cons (l := s.toList) (i := idx) (by simpa using hscan)
      rw [getElem!_pos s idx hscan]
      exact hd
    rw [ih, hdrop, List.foldl_cons]
  case case2 idx arr hscan =>
    have hlen : s.toList.length ≤ idx := by simpa using (Nat.le_of_not_gt hscan)
    simp [List.drop_eq_nil_iff.mpr hlen]

theorem countGo_zero (s : Array Char) :
    countGo s 0 (Array.replicate 128 0) = s.toList.foldl countStep (Array.replicate 128 0) := by
  have h := countGo_eq_drop_foldl s 0 (Array.replicate 128 0)
  simpa using h

theorem char_toNat_inj (a b : Char) (h : a.toNat = b.toNat) : a = b := by
  have h1 : Char.ofNat a.toNat = Char.ofNat b.toNat := congrArg Char.ofNat h
  simpa [Char.ofNat_toNat] using h1

@[simp]
theorem countStep_size (counts : Array Nat) (ch : Char) :
    (countStep counts ch).size = counts.size := by
  unfold countStep
  split_ifs <;> simp

theorem foldl_countStep_size (l : List Char) (counts : Array Nat) :
    (l.foldl countStep counts).size = counts.size := by
  induction l generalizing counts with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldl_cons, ih]

theorem foldl_countStep_acc (l : List Char) (acc : Array Nat) (hacc : acc.size = 128)
    (c : Char) (hc : c.toNat < 128) :
    (l.foldl countStep acc)[c.toNat]! = acc[c.toNat]! + l.count c := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.count_cons]
    have hstep_size : (countStep acc x).size = 128 := by
      rw [countStep_size, hacc]
    rw [ih (countStep acc x) hstep_size]
    unfold countStep
    by_cases hx : x.toNat < 128
    · simp only [hx, ↓reduceIte]
      by_cases heq : x = c
      · subst x
        simp only [beq_self_eq_true, ↓reduceIte]
        have h_get := getElem!_set! acc c.toNat c.toNat (acc[c.toNat]! + 1) (by omega) (by omega)
        simp only [↓reduceIte] at h_get
        rw [h_get]
        omega
      · have hne_nat : x.toNat ≠ c.toNat := fun h => heq (char_toNat_inj x c h)
        have h_beq : (x == c) = false := beq_false_of_ne heq
        simp only [h_beq, Bool.false_eq_true, ↓reduceIte]
        have h_get := getElem!_set! acc x.toNat c.toNat (acc[x.toNat]! + 1) (by omega) (by omega)
        have h_if : (if c.toNat = x.toNat then acc[x.toNat]! + 1 else acc[c.toNat]!) = acc[c.toNat]! := by
          split_ifs with h_eq
          · exact False.elim (hne_nat h_eq.symm)
          · rfl
        rw [h_get, h_if]
        omega
    · simp only [hx, ↓reduceIte]
      have hne : x ≠ c := by
        intro h
        subst h
        exact hx hc
      have h_beq : (x == c) = false := beq_false_of_ne hne
      simp only [h_beq, Bool.false_eq_true, ↓reduceIte]
      omega

theorem foldl_countStep_zero (l : List Char) (c : Char) (hc : c.toNat < 128) :
    (l.foldl countStep (Array.replicate 128 0))[c.toNat]! = l.count c := by
  have h := foldl_countStep_acc l (Array.replicate 128 0) (by simp) c hc
  have hzero : (Array.replicate 128 0)[c.toNat]! = 0 := by
    simp [hc]
  rw [hzero, Nat.zero_add] at h
  exact h

theorem list_countP_eq_count (l : List Char) (c : Char) :
    l.countP (fun x => x = c) = l.count c := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.countP_cons, List.count_cons]
    rw [ih]
    by_cases hx : x = c
    · subst hx
      simp
    · have h_dec : decide (x = c) = false := decide_eq_false hx
      have h_beq : (x == c) = false := beq_false_of_ne hx
      simp [h_dec, h_beq]

theorem charCount_eq_count (s : Array Char) (c : Char) :
    charCount s c = s.toList.count c := by
  unfold charCount
  rw [← Array.countP_toList]
  exact list_countP_eq_count s.toList c

theorem countGo_get_eq_charCount (s : Array Char) (c : Char) (hc : isASCII c) :
    (countGo s 0 (Array.replicate 128 0))[c.toNat]! = charCount s c := by
  rw [countGo_zero, foldl_countStep_zero s.toList c hc, charCount_eq_count]

theorem findFirstGo_eq_m (s : Array Char) (counts : Array Nat) (hpre : precondition s)
    (hcounts : ∀ c, isASCII c → counts[c.toNat]! = charCount s c)
    (m : Nat) (hm_lt : m < s.size) (hm_uniq : charCount s (s[m]!) = 1)
    (hnone : ∀ k, k < m → charCount s (s[k]!) ≠ 1) :
    ∀ j, j ≤ m → findFirstGo s counts j = Int.ofNat m := by
  intro j hj
  generalize hd : m - j = d
  induction d generalizing j with
  | zero =>
    have hjm : j = m := by omega
    rw [hjm, findFirstGo.eq_def]
    have hascii : isASCII (s[m]!) := hpre m hm_lt
    have hcode : s[m]!.toNat < 128 := hascii
    have hcnt : counts[s[m]!.toNat]! = 1 := by
      rw [hcounts (s[m]!) hascii, hm_uniq]
    have hcond : s[m]!.toNat < 128 ∧ counts[s[m]!.toNat]! = 1 := ⟨hcode, hcnt⟩
    rw [getElem!_pos s m hm_lt] at hcond
    simp [hm_lt, hcond]
  | succ d ih =>
    have hj_lt : j < m := by omega
    have hj_sz : j < s.size := Nat.lt_trans hj_lt hm_lt
    have hascii : isASCII (s[j]!) := hpre j hj_sz
    have hne : charCount s (s[j]!) ≠ 1 := hnone j hj_lt
    have hcnt_ne : counts[s[j]!.toNat]! ≠ 1 := by
      rw [hcounts (s[j]!) hascii]
      exact hne
    rw [findFirstGo.eq_def]
    have hcond : ¬ (s[j]!.toNat < 128 ∧ counts[s[j]!.toNat]! = 1) := by
      intro ⟨_, h1⟩
      exact hcnt_ne h1
    rw [getElem!_pos s j hj_sz] at hcond
    simp [hj_sz, hcond]
    have hd' : m - (j + 1) = d := by omega
    exact ih (j + 1) (by omega) hd'

theorem findFirstGo_eq_neg1 (s : Array Char) (counts : Array Nat) (hpre : precondition s)
    (hcounts : ∀ c, isASCII c → counts[c.toNat]! = charCount s c)
    (hnone : ∀ k, k < s.size → charCount s (s[k]!) ≠ 1) :
    ∀ j, j ≤ s.size → findFirstGo s counts j = -1 := by
  intro j hj
  generalize hd : s.size - j = d
  induction d generalizing j with
  | zero =>
    have hj_sz : j = s.size := by omega
    rw [hj_sz, findFirstGo.eq_def]
    simp
  | succ d ih =>
    have hj_lt : j < s.size := by omega
    have hascii : isASCII (s[j]!) := hpre j hj_lt
    have hne : charCount s (s[j]!) ≠ 1 := hnone j hj_lt
    have hcnt_ne : counts[s[j]!.toNat]! ≠ 1 := by
      rw [hcounts (s[j]!) hascii]
      exact hne
    rw [findFirstGo.eq_def]
    have hcond : ¬ (s[j]!.toNat < 128 ∧ counts[s[j]!.toNat]! = 1) := by
      intro ⟨_, h1⟩
      exact hcnt_ne h1
    rw [getElem!_pos s j hj_lt] at hcond
    simp [hj_lt, hcond]
    have hd' : s.size - (j + 1) = d := by omega
    exact ih (j + 1) (by omega) hd'

theorem firstUniqueCharIndex_correct (s : Array Char) (hpre : precondition s) :
    postcondition s (firstUniqueCharIndex s) := by
  classical
  have hcounts : ∀ c, isASCII c → (countGo s 0 (Array.replicate 128 0))[c.toNat]! = charCount s c :=
    fun c hc => countGo_get_eq_charCount s c hc
  unfold firstUniqueCharIndex postcondition
  constructor
  · intro ⟨i, hi_sz, hi_uniq⟩
    have hp : ∃ k, k < s.size ∧ charCount s (s[k]!) = 1 := ⟨i, hi_sz, hi_uniq⟩
    let m := Nat.find hp
    have hm : m < s.size ∧ charCount s (s[m]!) = 1 := Nat.find_spec hp
    have hmin : ∀ k < m, ¬ (k < s.size ∧ charCount s (s[k]!) = 1) := fun k hk => Nat.find_min hp hk
    have hnone : ∀ k < m, charCount s (s[k]!) ≠ 1 := by
      intro k hk hcount
      have hk_sz : k < s.size := Nat.lt_trans hk hm.1
      exact hmin k hk ⟨hk_sz, hcount⟩
    have hres : findFirstGo s (countGo s 0 (Array.replicate 128 0)) 0 = Int.ofNat m :=
      findFirstGo_eq_m s (countGo s 0 (Array.replicate 128 0)) hpre hcounts m hm.1 hm.2 hnone 0 (Nat.zero_le m)
    rw [hres]
    refine ⟨Int.natCast_nonneg m, ?_, ?_, ?_⟩
    · simp [hm.1]
    · simp [hm.2]
    · intro j hj
      have hj' : j < m := by simpa using hj
      exact hnone j hj'
  · intro hnot
    have hnone : ∀ k < s.size, charCount s (s[k]!) ≠ 1 := by
      intro k hk hcount
      exact hnot ⟨k, hk, hcount⟩
    have hres : findFirstGo s (countGo s 0 (Array.replicate 128 0)) 0 = -1 :=
      findFirstGo_eq_neg1 s (countGo s 0 (Array.replicate 128 0)) hpre hcounts hnone 0 (Nat.zero_le s.size)
    rw [hres]
    exact ⟨rfl, hnone⟩

prove_correct firstUniqChar by
  velvet_vcgen [firstUniqChar, postcondition] with try finish
  case count_continuation =>
    rename_i s
    have : countStep counts s[i]! = counts.set! s[i]!.toNat (counts[s[i]!.toNat]! + 1) := by
      simp [countStep, in_ascii]
    rw [← this]
    rw [countGo.eq_def] at count_continuation
    simp only [counting, ↓reduceIte] at count_continuation
    exact count_continuation
  case count_continuation =>
    rename_i s
    have : countStep counts s[i]! = counts := by
      simp [countStep, in_ascii]
    rw [← this]
    rw [countGo.eq_def] at count_continuation
    simp only [counting, ↓reduceIte] at count_continuation
    exact count_continuation
  case search_continuation =>
    rename_i s
    rw [countGo.eq_def] at count_continuation
    simp [counted] at count_continuation
    intro _
    simp [firstUniqueCharIndex, ← count_continuation]
  case search_ans =>
    rename_i s
    intro _
    have hsearch := search_continuation searching.2
    rw [findFirstGo.eq_def] at hsearch
    have hcond : s[j]!.toNat < 128 ∧ counts[s[j]!.toNat]! = 1 := ⟨in_ascii2, uniq⟩
    rw [getElem!_pos s j searching.1] at hcond
    simp [searching.1, hcond] at hsearch
    exact hsearch
  case search_continuation =>
    rename_i s
    intro _
    have hsearch := search_continuation searching.2
    rw [findFirstGo.eq_def] at hsearch
    have hcond : ¬ (s[j]!.toNat < 128 ∧ counts[s[j]!.toNat]! = 1) := fun ⟨_, h1⟩ => uniq h1
    rw [getElem!_pos s j searching.1] at hcond
    simp [searching.1, hcond] at hsearch
    exact hsearch
  case search_continuation =>
    rename_i s
    intro _
    have hsearch := search_continuation searching.2
    rw [findFirstGo.eq_def] at hsearch
    have hcond : ¬ (s[j]!.toNat < 128 ∧ counts[s[j]!.toNat]! = 1) := fun ⟨h0, _⟩ => in_ascii2 h0
    rw [getElem!_pos s j searching.1] at hcond
    simp [searching.1, hcond] at hsearch
    exact hsearch
  case first_uniq =>
    rename_i s
    cases done_search with
    | inl hj =>
      by_cases hf : found = true
      · have hans := search_ans hf
        rw [hans]
        exact firstUniqueCharIndex_correct s valid
      · have hf_false : found = false := by
          cases found
          · rfl
          · contradiction
        have hans := not_found hf_false
        have hsearch := search_continuation hf_false
        rw [findFirstGo.eq_def] at hsearch
        simp [hj] at hsearch
        rw [hans, hsearch]
        exact firstUniqueCharIndex_correct s valid
    | inr hfound =>
      have hans := search_ans hfound
      rw [hans]
      exact firstUniqueCharIndex_correct s valid

end Proof

end FirstUniqueCharacterInAString
