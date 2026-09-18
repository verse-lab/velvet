module

public import Velvet
public meta import Velvet

/-!
## Program description

Given two strings `s1` and `s2`, return `true` if `s2` contains a permutation
of `s1`, or `false` otherwise. In other words, return `true` if one of `s1`'s
permutations is a substring of `s2`.

With `K = 0x110000` Unicode scalar-value slots, the program is expected to run
in O(n + m + K) time and O(K) extra space. The inputs are arrays, and a
fixed-size difference table is updated as the window slides. Since `K` is a
fixed Unicode-domain constant, the auxiliary space is O(1) in the input sizes.
-/

namespace PermutationInString


section Specs

public def window (s : List Char) (i : Nat) (n : Nat) : List Char :=
  (s.drop i).take n

public def isPermutationOf (s1 : List Char) (w : List Char) : Prop :=
  (∀ c : Char, c ∈ s1 → s1.count c = w.count c) ∧
  (∀ c : Char, c ∈ w → c ∈ s1)

public def precondition (_s1 : Array Char) (_s2 : Array Char) : Prop :=
  True

public def postcondition (s1 : Array Char) (s2 : Array Char) (result : Bool) : Prop :=
  result = true ↔
    (∃ i : Nat,
      i + s1.size ≤ s2.size ∧
      isPermutationOf s1.toList (window s2.toList i s1.size))

end Specs

section Implementation

public def unicodeSize : Nat := 0x110000

public def checkPerm (s1 w : List Char) : Bool :=
  s1.all (fun c => s1.count c == w.count c) && w.all (fun c => decide (c ∈ s1))

public def diffModel (diff : Array Int) (s1 w : List Char) : Prop :=
  diff.size = unicodeSize ∧
  ∀ c : Char,
    diff[c.toNat]! = (s1.count c : Int) - (w.count c : Int)

public def invalidSlotsZero (diff : Array Int) : Prop :=
  ∀ t : Nat, t < unicodeSize → (∀ c : Char, c.toNat ≠ t) → diff[t]! = 0

public def allSlotsZero (diff : Array Int) : Prop :=
  ∀ t : Nat, t < unicodeSize → diff[t]! = 0

public def zeroCount (diff : Array Int) : Int :=
  (diff.count 0 : Nat)

public def prefixZeroCount (diff : Array Int) (k : Nat) : Int :=
  ((diff.take k).count 0 : Nat)

public def adjustZeroCount (zeros before after : Int) : Int :=
  zeros - (if before = 0 then 1 else 0) + (if after = 0 then 1 else 0)

method checkInclusion (s1 : Array Char) (s2 : Array Char)
  returns (result : Bool)
  requires valid: precondition s1 s2
  ensures included: postcondition s1 s2 result
do
  let n := s1.size
  let m := s2.size
  if empty_pattern: n = 0 then
    return true
  else
    if too_long: n > m then
      return false
    let K : Nat := unicodeSize
    let kI : Int := K
    let mut diff : Array Int := Array.replicate K 0

    let mut i : Nat := 0
    while' initializing: i < n
      invariant init_bound: i ≤ n
      invariant init_size: diff.size = K
      invariant init_model: diffModel diff (s1.toList.take i) (s2.toList.take i)
      invariant init_invalid: invalidSlotsZero diff
      decreasing init_remaining: n - i
    do
      let k1 := s1[i]!.toNat
      let k2 := s2[i]!.toNat
      diff := diff.set! k1 (diff[k1]! + 1)
      diff := diff.set! k2 (diff[k2]! - 1)
      i := i + 1

    let mut zeros : Int := 0
    let mut j : Nat := 0
    while' count_zeros: j < K
      invariant zero_bound: j ≤ K
      invariant zero_size: diff.size = K
      invariant zeros_exact: zeros = prefixZeroCount diff j
      decreasing zero_remaining: K - j
    do
      if is_zero: diff[j]! = 0 then
        zeros := zeros + 1
      j := j + 1

    if initial_match: zeros = kI then
      return true

    let mut left : Nat := 0
    let mut right : Nat := n
    let mut found : Bool := false
    while' sliding: right < m ∧ found = false
      invariant slide_window: right = left + n
      invariant slide_bounds: left ≤ right ∧ right ≤ m
      invariant slide_size: diff.size = K
      invariant slide_model: diffModel diff s1.toList (window s2.toList left n)
      invariant slide_invalid: invalidSlotsZero diff
      invariant slide_zeros: zeros = zeroCount diff
      invariant slide_not_found: found = false →
        ∀ p : Nat, p ≤ left → ¬ isPermutationOf s1.toList (window s2.toList p n)
      invariant slide_found: found = true →
        ∃ p : Nat, p + n ≤ m ∧ isPermutationOf s1.toList (window s2.toList p n)
      decreasing slide_remaining: m - right
    do
      let kout := s2[left]!.toNat
      let kin := s2[right]!.toNat
      let before := diff[kout]!
      let after := before + 1
      diff := diff.set! kout after
      zeros := adjustZeroCount zeros before after
      let before := diff[kin]!
      let after := before - 1
      diff := diff.set! kin after
      zeros := adjustZeroCount zeros before after
      left := left + 1
      right := right + 1
      if match_found: zeros = kI then
        found := true
    return found

end Implementation

section Proof

theorem char_toNat_lt_unicodeSize (c : Char) : c.toNat < unicodeSize := by
  unfold unicodeSize
  have h := c.valid
  change c.toNat < 55296 ∨ 57343 < c.toNat ∧ c.toNat < 1114112 at h
  omega

theorem toArray_get! (s : List Char) (i : Nat) (hi : i < s.length) :
    s.toArray[i]! = s[i] := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem toList_get! (s : Array Char) (i : Nat) (hi : i < s.size) :
    s.toList[i] = s[i]! := by
  simp [getElem!_pos, hi]

@[simp] theorem toList_take_size (s : Array Char) :
    s.toList.take s.size = s.toList := by
  have hsize : s.size = s.toList.length := by simp
  rw [hsize, List.take_length]

theorem zeroCount_eq_size_iff (diff : Array Int) :
    zeroCount diff = (diff.size : Int) ↔ ∀ t, t < diff.size → diff[t]! = 0 := by
  unfold zeroCount
  rw [Int.ofNat_inj]
  constructor
  · intro h t ht
    have hm : diff[t]! ∈ diff := by
      rw [getElem!_pos diff t ht]
      exact Array.getElem_mem ht
    have hall := (Array.count_eq_size.mp h) diff[t]!
      hm
    exact hall.symm
  · intro h
    apply Array.count_eq_size.mpr
    intro b hb
    rw [Array.mem_iff_getElem] at hb
    rcases hb with ⟨i, hi, rfl⟩
    simpa [getElem!_pos, hi] using (h i hi).symm

theorem allSlotsZero_of_zeroCount (diff : Array Int)
    (hsize : diff.size = unicodeSize)
    (hcount : zeroCount diff = (unicodeSize : Int)) :
    allSlotsZero diff := by
  unfold allSlotsZero
  have hz : ∀ t, t < diff.size → diff[t]! = 0 :=
    (zeroCount_eq_size_iff diff).mp (by simpa [hsize] using hcount)
  intro t ht
  exact hz t (by simpa [hsize] using ht)

theorem counts_equal_of_isPermutation (s1 w : List Char)
    (hperm : isPermutationOf s1 w) (c : Char) :
    s1.count c = w.count c := by
  by_cases hc : c ∈ s1
  · exact hperm.1 c hc
  · have hw : c ∉ w := fun hw => hc (hperm.2 c hw)
    rw [List.count_eq_zero.mpr hc, List.count_eq_zero.mpr hw]

theorem isPermutation_of_counts_equal (s1 w : List Char)
    (hcounts : ∀ c : Char, s1.count c = w.count c) :
    isPermutationOf s1 w := by
  refine ⟨fun c _ => hcounts c, ?_⟩
  intro c hc
  by_cases hs : c ∈ s1
  · exact hs
  · have hs0 : s1.count c = 0 := List.count_eq_zero.mpr hs
    have hw0 : w.count c = 0 := by rw [← hcounts c, hs0]
    exact False.elim ((List.count_eq_zero.mp hw0) hc)

theorem allSlotsZero_iff_isPermutation (diff : Array Int) (s1 w : List Char)
    (hmodel : diffModel diff s1 w) (hinvalid : invalidSlotsZero diff) :
    allSlotsZero diff ↔ isPermutationOf s1 w := by
  constructor
  · intro hall
    apply isPermutation_of_counts_equal
    intro c
    have hz := hall c.toNat (char_toNat_lt_unicodeSize c)
    rw [hmodel.2 c] at hz
    omega
  · intro hperm t ht
    by_cases hex : ∃ c : Char, c.toNat = t
    · rcases hex with ⟨c, rfl⟩
      rw [hmodel.2 c, counts_equal_of_isPermutation s1 w hperm c]
      omega
    · exact hinvalid t ht (by simpa using hex)

theorem zeroCount_iff_isPermutation (diff : Array Int) (s1 w : List Char)
    (hmodel : diffModel diff s1 w) (hinvalid : invalidSlotsZero diff) :
    zeroCount diff = (unicodeSize : Int) ↔ isPermutationOf s1 w := by
  rw [← allSlotsZero_iff_isPermutation diff s1 w hmodel hinvalid]
  constructor
  · exact allSlotsZero_of_zeroCount diff hmodel.1
  · intro hall
    have hz : ∀ t, t < diff.size → diff[t]! = 0 := by
      intro t ht
      exact hall t (by simpa [hmodel.1] using ht)
    have := (zeroCount_eq_size_iff diff).mpr hz
    simpa [hmodel.1] using this

theorem zeroCount_set! (diff : Array Int) (i : Nat) (v : Int)
    (hi : i < diff.size) :
    zeroCount (diff.set! i v) = zeroCount diff -
      (if diff[i]! = 0 then 1 else 0) + (if v = 0 then 1 else 0) := by
  unfold zeroCount
  rw [← Array.count_toList, Array.toList_set!, List.count_set (i := i)
    (a := v) (b := (0 : Int)) (by simpa using hi), Array.count_toList]
  rw [getElem!_pos diff i hi]
  by_cases hold : diff[i] = 0 <;> by_cases hnew : v = 0 <;>
    simp_all [beq_iff_eq]
  all_goals
    have hpos : 0 < diff.count 0 := by
      rw [← Array.count_toList]
      have hm : (0 : Int) ∈ diff.toList := by
        rw [List.mem_iff_get]
        exact ⟨⟨i, by simpa using hi⟩, hold⟩
      exact List.count_pos_iff.mpr hm
    rw [Int.ofNat_sub (by omega)]
    omega

theorem adjustZeroCount_set! (diff : Array Int) (i : Nat) (v : Int)
    (hi : i < diff.size) :
    adjustZeroCount (zeroCount diff) diff[i]! v = zeroCount (diff.set! i v) := by
  rw [zeroCount_set! diff i v hi]
  rfl

theorem slide_zeroCount (diff : Array Int) (zeros : Int) (out incoming : Char)
    (hsize : diff.size = unicodeSize) (hzeros : zeros = zeroCount diff) :
    adjustZeroCount
        (adjustZeroCount zeros diff[out.toNat]! (diff[out.toNat]! + 1))
        (diff.set! out.toNat (diff[out.toNat]! + 1))[incoming.toNat]!
        ((diff.set! out.toNat (diff[out.toNat]! + 1))[incoming.toNat]! - 1) =
      zeroCount
        ((diff.set! out.toNat (diff[out.toNat]! + 1)).set! incoming.toNat
          ((diff.set! out.toNat (diff[out.toNat]! + 1))[incoming.toNat]! - 1)) := by
  have hout : out.toNat < diff.size := by rw [hsize]; exact char_toNat_lt_unicodeSize out
  let d1 := diff.set! out.toNat (diff[out.toNat]! + 1)
  have hd1 : d1.size = unicodeSize := by simp [d1, hsize]
  have hin : incoming.toNat < d1.size := by rw [hd1]; exact char_toNat_lt_unicodeSize incoming
  have h1 := adjustZeroCount_set! diff out.toNat (diff[out.toNat]! + 1) hout
  have h2 := adjustZeroCount_set! d1 incoming.toNat (d1[incoming.toNat]! - 1) hin
  have h1' : adjustZeroCount zeros diff[out.toNat]! (diff[out.toNat]! + 1) =
      zeroCount d1 := by
    rw [hzeros]
    simpa [d1] using h1
  simpa [d1, h1'] using h2

theorem prefixZeroCount_zero (diff : Array Int) : prefixZeroCount diff 0 = 0 := by
  simp [prefixZeroCount]

theorem prefixZeroCount_succ (diff : Array Int) (j : Nat) (hj : j < diff.size) :
    prefixZeroCount diff (j + 1) = prefixZeroCount diff j +
      (if diff[j]! = 0 then 1 else 0) := by
  unfold prefixZeroCount
  rw [← Array.count_toList, ← Array.count_toList]
  simp only [Array.take_eq_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  rw [List.take_succ_eq_append_getElem (by simpa using hj), List.count_append]
  rw [getElem!_pos diff j hj]
  by_cases hz : diff[j] = 0 <;> simp [hz]

theorem prefixZeroCount_size (diff : Array Int) :
    prefixZeroCount diff diff.size = zeroCount diff := by
  unfold prefixZeroCount zeroCount
  simp

theorem diffModel_empty :
    diffModel (Array.replicate unicodeSize (0 : Int)) [] [] := by
  unfold diffModel
  refine ⟨by simp, ?_⟩
  intro c
  rw [getElem!_pos _ _ (by simp [char_toNat_lt_unicodeSize])]
  simp

theorem invalidSlotsZero_replicate :
    invalidSlotsZero (Array.replicate unicodeSize (0 : Int)) := by
  intro t ht _
  simp [getElem!_pos, ht]

theorem diffModel_append_left (diff : Array Int) (xs w : List Char) (c : Char)
    (hmodel : diffModel diff xs w) :
    diffModel (diff.set! c.toNat (diff[c.toNat]! + 1)) (xs ++ [c]) w := by
  have hc : c.toNat < diff.size := by rw [hmodel.1]; exact char_toNat_lt_unicodeSize c
  refine ⟨by simp [hmodel.1], ?_⟩
  intro d
  have hd : d.toNat < diff.size := by rw [hmodel.1]; exact char_toNat_lt_unicodeSize d
  by_cases hdc : d = c
  · subst d
    have hmc : diff[c.toNat] = (xs.count c : Int) - (w.count c : Int) := by
      simpa [getElem!_pos diff c.toNat hc] using hmodel.2 c
    unfold Array.set!
    rw [getElem!_pos _ _ (by simpa using hd)]
    rw [Array.getElem_setIfInBounds]
    simp only [ite_true]
    rw [getElem!_pos diff c.toNat hc, hmc]
    simp [List.count_append]
    omega
    all_goals assumption
  · have hidx : c.toNat ≠ d.toNat := by
      intro h
      exact hdc (Char.toNat_inj.mp h.symm)
    unfold Array.set!
    rw [getElem!_pos _ _ (by simpa using hd)]
    rw [Array.getElem_setIfInBounds]
    simp only [hidx, ite_false]
    have hmd := hmodel.2 d
    rw [getElem!_pos diff d.toNat hd] at hmd
    rw [hmd]
    have hcd : c ≠ d := Ne.symm hdc
    simp [List.count_append, hcd]
    all_goals assumption

theorem diffModel_append_right (diff : Array Int) (xs w : List Char) (c : Char)
    (hmodel : diffModel diff xs w) :
    diffModel (diff.set! c.toNat (diff[c.toNat]! - 1)) xs (w ++ [c]) := by
  have hc : c.toNat < diff.size := by rw [hmodel.1]; exact char_toNat_lt_unicodeSize c
  refine ⟨by simp [hmodel.1], ?_⟩
  intro d
  have hd : d.toNat < diff.size := by rw [hmodel.1]; exact char_toNat_lt_unicodeSize d
  by_cases hdc : d = c
  · subst d
    have hmc : diff[c.toNat] = (xs.count c : Int) - (w.count c : Int) := by
      simpa [getElem!_pos diff c.toNat hc] using hmodel.2 c
    unfold Array.set!
    rw [getElem!_pos _ _ (by simpa using hd)]
    rw [Array.getElem_setIfInBounds]
    simp only [ite_true]
    rw [getElem!_pos diff c.toNat hc, hmc]
    simp [List.count_append]
    omega
    all_goals assumption
  · have hidx : c.toNat ≠ d.toNat := by
      intro h
      exact hdc (Char.toNat_inj.mp h.symm)
    unfold Array.set!
    rw [getElem!_pos _ _ (by simpa using hd)]
    rw [Array.getElem_setIfInBounds]
    simp only [hidx, ite_false]
    have hmd := hmodel.2 d
    rw [getElem!_pos diff d.toNat hd] at hmd
    rw [hmd]
    have hcd : c ≠ d := Ne.symm hdc
    simp [List.count_append, hcd]
    all_goals assumption

theorem invalidSlotsZero_set_char (diff : Array Int) (c : Char) (v : Int)
    (hsize : diff.size = unicodeSize) (hinvalid : invalidSlotsZero diff) :
    invalidSlotsZero (diff.set! c.toNat v) := by
  intro t ht hnot
  have hc : c.toNat < diff.size := by
    rw [hsize]
    exact char_toNat_lt_unicodeSize c
  have hne : c.toNat ≠ t := hnot c
  have ht' : t < diff.size := by simpa [hsize] using ht
  unfold Array.set!
  rw [getElem!_pos _ _ (by simpa using ht')]
  rw [Array.getElem_setIfInBounds]
  simp only [hne, ite_false]
  have hinv := hinvalid t ht hnot
  rw [getElem!_pos diff t ht'] at hinv
  exact hinv

theorem window_cons (s : List Char) (left n : Nat)
    (hn : 0 < n) (hleft : left < s.length) :
    window s left n = s[left] :: (s.drop (left + 1)).take (n - 1) := by
  unfold window
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one]
    calc
      (s.drop left).take (n + 1) =
          (s[left] :: s.drop (left + 1)).take (n + 1) := by
            rw [List.drop_eq_getElem_cons hleft]
      _ = s[left] :: (s.drop (left + 1)).take n := List.take_succ_cons

theorem window_succ (s : List Char) (left n : Nat)
    (hn : 0 < n) (hbound : left + n < s.length) :
    window s (left + 1) n =
      (s.drop (left + 1)).take (n - 1) ++ [s[left + n]] := by
  unfold window
  cases n with
  | zero => omega
  | succ n =>
    have hi : n < (s.drop (left + 1)).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hi]
    congr 2
    simp only [List.getElem_drop]
    congr 1
    omega

theorem diffModel_remove_head (diff : Array Int) (xs w : List Char) (c : Char)
    (hmodel : diffModel diff xs (c :: w)) :
    diffModel (diff.set! c.toNat (diff[c.toNat]! + 1)) xs w := by
  have hc : c.toNat < diff.size := by rw [hmodel.1]; exact char_toNat_lt_unicodeSize c
  refine ⟨by simp [hmodel.1], ?_⟩
  intro d
  have hd : d.toNat < diff.size := by rw [hmodel.1]; exact char_toNat_lt_unicodeSize d
  by_cases hdc : d = c
  · subst d
    have hm := hmodel.2 c
    rw [getElem!_pos diff c.toNat hc] at hm
    unfold Array.set!
    rw [getElem!_pos _ _ (by simpa using hd), Array.getElem_setIfInBounds]
    simp only [ite_true]
    rw [getElem!_pos diff c.toNat hc, hm]
    simp
    omega
    all_goals assumption
  · have hidx : c.toNat ≠ d.toNat := by
      intro h
      exact hdc (Char.toNat_inj.mp h.symm)
    unfold Array.set!
    rw [getElem!_pos _ _ (by simpa using hd), Array.getElem_setIfInBounds]
    simp only [hidx, ite_false]
    have hm := hmodel.2 d
    rw [getElem!_pos diff d.toNat hd] at hm
    rw [hm]
    have hcd : c ≠ d := Ne.symm hdc
    simp [hcd]
    all_goals assumption

theorem slide_diff_model (diff : Array Int) (s1 s2 : List Char) (left n : Nat)
    (hn : 0 < n) (hbound : left + n < s2.length)
    (hmodel : diffModel diff s1 (window s2 left n)) :
    diffModel
      ((diff.set! s2[left].toNat (diff[s2[left].toNat]! + 1)).set!
        s2[left + n].toNat
        ((diff.set! s2[left].toNat (diff[s2[left].toNat]! + 1))[s2[left + n].toNat]! - 1))
      s1 (window s2 (left + 1) n) := by
  rw [window_cons s2 left n hn (by omega)] at hmodel
  have hremove := diffModel_remove_head diff s1
    ((s2.drop (left + 1)).take (n - 1)) s2[left] hmodel
  have hadd := diffModel_append_right
    (diff.set! s2[left].toNat (diff[s2[left].toNat]! + 1)) s1
    ((s2.drop (left + 1)).take (n - 1)) s2[left + n] hremove
  rw [window_succ s2 left n hn hbound]
  exact hadd

theorem checkPerm_iff (s1 w : List Char) :
    checkPerm s1 w = true ↔ isPermutationOf s1 w := by
  unfold checkPerm isPermutationOf
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_iff]

theorem not_found_step (s1 s2 : List Char) (n : Nat) (i : Nat)
    (hprev : ∀ j : Nat, j < i → ¬ isPermutationOf s1 (window s2 j n))
    (hnot : checkPerm s1 (window s2 i n) ≠ true) :
    ∀ j : Nat, j < i + 1 → ¬ isPermutationOf s1 (window s2 j n) := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
  · exact hprev j hj_lt
  · subst j
    intro hperm
    have hhit : checkPerm s1 (window s2 i n) = true := (checkPerm_iff s1 (window s2 i n)).mpr hperm
    exact hnot hhit

theorem postcondition_too_long (s1 s2 : Array Char) (h : s1.size > s2.size) :
    postcondition s1 s2 false := by
  unfold postcondition
  simp only [Bool.false_eq_true, false_iff]
  intro ⟨i, hi, _⟩
  omega

theorem postcondition_false (s1 s2 : Array Char) (limit : Nat) (hlimit : limit = s2.size - s1.size + 1)
    (hnone : ∀ j : Nat, j < limit →
      ¬ isPermutationOf s1.toList (window s2.toList j s1.size)) :
    postcondition s1 s2 false := by
  unfold postcondition
  simp only [Bool.false_eq_true, false_iff]
  intro ⟨j, hj_len, hj_perm⟩
  have hj_lt : j < limit := by
    subst hlimit
    omega
  exact hnone j hj_lt hj_perm

theorem postcondition_true (s1 s2 : Array Char)
    (hwitness : ∃ j : Nat, j + s1.size ≤ s2.size ∧
      isPermutationOf s1.toList (window s2.toList j s1.size)) :
    postcondition s1 s2 true := by
  unfold postcondition
  simp only [true_iff]
  exact hwitness

theorem postcondition_from_loop (s1 s2 : Array Char) (n m limit i : Nat) (found : Bool)
    (hn : n = s1.size) (hm : m = s2.size) (hlimit : limit = m - n + 1)
    (hnot_found : found = false → ∀ j : Nat, j < i →
      ¬ isPermutationOf s1.toList (window s2.toList j n))
    (hfound_witness : found = true → ∃ j : Nat, j + n ≤ m ∧
      isPermutationOf s1.toList (window s2.toList j n))
    (hdone : i = limit ∨ found = true) :
    postcondition s1 s2 found := by
  cases found with
  | false =>
    have hi : i = limit := by
      cases hdone with
      | inl h => exact h
      | inr h => contradiction
    subst hn hm
    have hnone : ∀ j : Nat, j < limit →
        ¬ isPermutationOf s1.toList (window s2.toList j s1.size) := by
      intro j hj
      rw [← hi] at hj
      exact hnot_found rfl j hj
    exact postcondition_false s1 s2 limit hlimit hnone
  | true =>
    subst hn hm
    have hwit := hfound_witness rfl
    exact postcondition_true s1 s2 hwit

prove_correct checkInclusion by
  velvet_vcgen [checkInclusion, postcondition] with try finish
  case included =>
    rename_i s1 s2
    have hs1 : s1 = #[] := Array.size_eq_zero_iff.mp empty_pattern
    subst s1
    unfold postcondition
    simp only [true_iff]
    refine ⟨0, by simp, ?_⟩
    unfold isPermutationOf window
    simp
  case included =>
    exact postcondition_too_long _ _ too_long
  case init_model =>
    simpa using diffModel_empty
  case init_invalid =>
    exact invalidSlotsZero_replicate
  case zeros_exact =>
    exact (prefixZeroCount_zero _).symm
  case included =>
    rename_i s1 s2
    have hi : i = s1.size := by omega
    have hj : j = unicodeSize := by omega
    have hmodel : diffModel diff s1.toList (window s2.toList 0 s1.size) := by
      rw [hi] at init_model
      simpa [window, toList_take_size] using init_model
    have hz : zeros = zeroCount diff := by
      calc
        zeros = prefixZeroCount diff j := zeros_exact
        _ = prefixZeroCount diff diff.size := by rw [hj, zero_size]
        _ = zeroCount diff := prefixZeroCount_size diff
    have hzeroCount : zeroCount diff = (unicodeSize : Int) := by
      rw [← hz]
      exact initial_match
    have hall := allSlotsZero_of_zeroCount diff zero_size hzeroCount
    have hperm := (allSlotsZero_iff_isPermutation diff s1.toList
      (window s2.toList 0 s1.size) hmodel init_invalid).mp hall
    exact postcondition_true s1 s2 ⟨0, by omega, hperm⟩
  case slide_model =>
    rename_i s1 s2
    have hi : i = s1.size := by omega
    rw [hi] at init_model
    simpa [window, toList_take_size] using init_model
  case slide_zeros =>
    rename_i s1 s2
    have hj : j = unicodeSize := by omega
    calc
      zeros = prefixZeroCount diff j := zeros_exact
      _ = prefixZeroCount diff diff.size := by rw [hj, zero_size]
      _ = zeroCount diff := prefixZeroCount_size diff
  case slide_not_found =>
    rename_i s1 s2
    intro _ p hp hperm
    have hi : i = s1.size := by omega
    have hj : j = unicodeSize := by omega
    have hp0 : p = 0 := by omega
    subst p
    have hmodel : diffModel diff s1.toList (window s2.toList 0 s1.size) := by
      rw [hi] at init_model
      simpa [window, toList_take_size] using init_model
    have hz : zeros = zeroCount diff := by
      calc
        zeros = prefixZeroCount diff j := zeros_exact
        _ = prefixZeroCount diff diff.size := by rw [hj, zero_size]
        _ = zeroCount diff := prefixZeroCount_size diff
    apply initial_match
    rw [hz]
    exact (zeroCount_iff_isPermutation diff s1.toList
      (window s2.toList 0 s1.size) hmodel init_invalid).mpr hperm
  case slide_model =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hn : 0 < s1.size := by omega
    have hb : left + s1.size < s2.size := by omega
    have h := slide_diff_model diff s1.toList s2.toList left s1.size hn hb slide_model
    simpa [toList_get! s2 left (by omega),
      toList_get! s2 (left + s1.size) (by omega)] using h
  case slide_model =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hn : 0 < s1.size := by omega
    have hb : left + s1.size < s2.size := by omega
    have h := slide_diff_model diff s1.toList s2.toList left s1.size hn hb slide_model
    simpa [toList_get! s2 left (by omega),
      toList_get! s2 (left + s1.size) (by omega)] using h
  case slide_invalid =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hleft : left < s2.size := by omega
    have hout := invalidSlotsZero_set_char diff s2[left]!
      (diff[s2[left]!.toNat]! + 1) slide_size slide_invalid
    have hd1 : (diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1)).size = unicodeSize := by
      simp [slide_size]
    have hin := invalidSlotsZero_set_char
      (diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1)) s2[left + s1.size]!
      ((diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1))[s2[left + s1.size]!.toNat]! - 1)
      hd1 hout
    exact hin
  case slide_invalid =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hleft : left < s2.size := by omega
    have hout := invalidSlotsZero_set_char diff s2[left]!
      (diff[s2[left]!.toNat]! + 1) slide_size slide_invalid
    have hd1 : (diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1)).size = unicodeSize := by
      simp [slide_size]
    have hin := invalidSlotsZero_set_char
      (diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1)) s2[left + s1.size]!
      ((diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1))[s2[left + s1.size]!.toNat]! - 1)
      hd1 hout
    exact hin
  case slide_zeros =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hleft : left < s2.size := by omega
    have h := slide_zeroCount diff zeros s2[left]! s2[left + s1.size]! slide_size slide_zeros
    exact h
  case slide_zeros =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hleft : left < s2.size := by omega
    have h := slide_zeroCount diff zeros s2[left]! s2[left + s1.size]! slide_size slide_zeros
    exact h
  case slide_found =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hleft : left < s2.size := by omega
    intro _
    let d1 := diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1)
    let d2 := d1.set! s2[left + s1.size]!.toNat (d1[s2[left + s1.size]!.toNat]! - 1)
    let newZeros := adjustZeroCount
      (adjustZeroCount zeros diff[s2[left]!.toNat]! (diff[s2[left]!.toNat]! + 1))
      d1[s2[left + s1.size]!.toNat]! (d1[s2[left + s1.size]!.toNat]! - 1)
    have hmodelNew : diffModel d2 s1.toList (window s2.toList (left + 1) s1.size) := by
      have h := slide_diff_model diff s1.toList s2.toList left s1.size
        (by omega) (by simpa using (show left + s1.size < s2.size by omega)) slide_model
      simpa [d1, d2, getElem!_pos, hleft,
        show left + s1.size < s2.size by omega,
        toList_get! s2 left (by omega),
        toList_get! s2 (left + s1.size) (by omega)] using h
    have hinvalidNew : invalidSlotsZero d2 := by
      have h1 := invalidSlotsZero_set_char diff s2[left]!
        (diff[s2[left]!.toNat]! + 1) slide_size slide_invalid
      have hs1 : d1.size = unicodeSize := by simp [d1, slide_size]
      exact invalidSlotsZero_set_char d1 s2[left + s1.size]!
        (d1[s2[left + s1.size]!.toNat]! - 1) hs1 (by simpa [d1] using h1)
    have hzeroNew : newZeros = zeroCount d2 := by
      simpa [newZeros, d1, d2, getElem!_pos, hleft,
        show left + s1.size < s2.size by omega] using
        (slide_zeroCount diff zeros s2[left]! s2[left + s1.size]! slide_size slide_zeros)
    refine ⟨left + 1, by omega, ?_⟩
    apply (zeroCount_iff_isPermutation d2 s1.toList
      (window s2.toList (left + 1) s1.size) hmodelNew hinvalidNew).mp
    rw [← hzeroNew]
    simpa [newZeros, d1, getElem!_pos, hleft,
      show left + s1.size < s2.size by omega,
      toList_get! s2 left (by omega),
      toList_get! s2 (left + s1.size) (by omega)] using match_found
  case slide_not_found =>
    rename_i s1 s2 diff0 zeros0
    subst right
    have hleft : left < s2.size := by omega
    intro _ p hp hperm
    by_cases hple : p ≤ left
    · exact slide_not_found sliding.2 p hple hperm
    · have hpnext : p = left + 1 := by omega
      subst p
      let d1 := diff.set! s2[left]!.toNat (diff[s2[left]!.toNat]! + 1)
      let d2 := d1.set! s2[left + s1.size]!.toNat (d1[s2[left + s1.size]!.toNat]! - 1)
      let newZeros := adjustZeroCount
        (adjustZeroCount zeros diff[s2[left]!.toNat]! (diff[s2[left]!.toNat]! + 1))
        d1[s2[left + s1.size]!.toNat]! (d1[s2[left + s1.size]!.toNat]! - 1)
      have hmodelNew : diffModel d2 s1.toList (window s2.toList (left + 1) s1.size) := by
        have h := slide_diff_model diff s1.toList s2.toList left s1.size
          (by omega) (by simpa using (show left + s1.size < s2.size by omega)) slide_model
        simpa [d1, d2, getElem!_pos, hleft,
          show left + s1.size < s2.size by omega,
          toList_get! s2 left (by omega),
          toList_get! s2 (left + s1.size) (by omega)] using h
      have hinvalidNew : invalidSlotsZero d2 := by
        have h1 := invalidSlotsZero_set_char diff s2[left]!
          (diff[s2[left]!.toNat]! + 1) slide_size slide_invalid
        have hs1 : d1.size = unicodeSize := by simp [d1, slide_size]
        exact invalidSlotsZero_set_char d1 s2[left + s1.size]!
          (d1[s2[left + s1.size]!.toNat]! - 1) hs1 (by simpa [d1] using h1)
      have hzeroNew : newZeros = zeroCount d2 := by
        simpa [newZeros, d1, d2, getElem!_pos, hleft,
          show left + s1.size < s2.size by omega] using
          (slide_zeroCount diff zeros s2[left]! s2[left + s1.size]! slide_size slide_zeros)
      apply match_found
      have heq : newZeros = (unicodeSize : Int) := by
        rw [hzeroNew]
        exact (zeroCount_iff_isPermutation d2 s1.toList
          (window s2.toList (left + 1) s1.size) hmodelNew hinvalidNew).mpr hperm
      simpa [newZeros, d1, getElem!_pos, hleft,
        show left + s1.size < s2.size by omega,
        toList_get! s2 left (by omega),
        toList_get! s2 (left + s1.size) (by omega)] using heq
  case included =>
    rename_i s1 s2 diff0 zeros0
    unfold postcondition
    constructor
    · intro hf
      exact slide_found hf
    · rintro ⟨p, hp, hperm⟩
      cases found with
      | true => rfl
      | false =>
        have hnlt : ¬ right < s2.size := by
          intro h
          exact h_done_with_2 ⟨h, rfl⟩
        have hr : right = s2.size := by omega
        have hpl : p ≤ left := by omega
        exact False.elim (slide_not_found rfl p hpl hperm)
  case init_model =>
    rename_i s1 s2
    have hi2 : i < s2.size := by omega
    have ht1 := List.take_succ_eq_append_getElem (l := s1.toList) (by simpa using initializing)
    have ht2 := List.take_succ_eq_append_getElem (l := s2.toList) (by simpa using hi2)
    have hleft := diffModel_append_left diff (s1.toList.take i) (s2.toList.take i)
      s1[i]! init_model
    have hboth := diffModel_append_right
      (diff.set! s1[i]!.toNat (diff[s1[i]!.toNat]! + 1))
      (s1.toList.take i ++ [s1[i]!]) (s2.toList.take i) s2[i]! hleft
    simpa [ht1, ht2, toList_get! s1 i initializing, toList_get! s2 i hi2] using hboth
  case init_invalid =>
    rename_i s1 s2
    have h1 := invalidSlotsZero_set_char diff s1[i]!
      (diff[s1[i]!.toNat]! + 1)
      init_model.1 init_invalid
    have hsize1 : (diff.set! s1[i]!.toNat (diff[s1[i]!.toNat]! + 1)).size = unicodeSize := by
      simp [init_model.1]
    have h2 := invalidSlotsZero_set_char
      (diff.set! s1[i]!.toNat (diff[s1[i]!.toNat]! + 1)) s2[i]!
      ((diff.set! s1[i]!.toNat (diff[s1[i]!.toNat]! + 1))[s2[i]!.toNat]! - 1)
      hsize1 h1
    exact h2
  case zeros_exact =>
    rw [prefixZeroCount_succ diff j (by omega), ← zeros_exact]
    simp [is_zero]
  case zeros_exact =>
    rw [prefixZeroCount_succ diff j (by omega), ← zeros_exact]
    simp [is_zero]

end Proof

end PermutationInString
