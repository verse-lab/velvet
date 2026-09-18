module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Order.Basic

/-!
## Program description

Given a nondecreasing integer array, keep each value at most twice and return
the length of the relevant prefix together with the modified array. The program
is expected to run in O(n) time and O(1) extra space.
-/

namespace RemoveDuplicatesFromSortedArrayII

section Specs

public def sortedPrefix (a : Array Int) (k : Nat) : Prop :=
  ∀ i, i + 1 < k → a[i]! ≤ a[i + 1]!
public def countInPrefix (arr : Array Int) (k : Nat) (x : Int) : Nat :=
  (arr.take k).count x
public def precondition (nums : Array Int) : Prop := sortedPrefix nums nums.size

public def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  let k := result.1
  let out := result.2
  out.size = nums.size ∧
  k ≤ nums.size ∧
  sortedPrefix out k ∧
  ∀ x, countInPrefix out k x = Nat.min 2 (countInPrefix nums nums.size x)

end Specs

section Implementation

public def CompactTwiceInvariant (nums : Array Int) (i write : Nat)
    (out : Array Int) : Prop :=
  i ≤ nums.size ∧ write ≤ i ∧ out.size = nums.size ∧
  sortedPrefix out write ∧
  (∀ x, countInPrefix out write x = Nat.min 2 (countInPrefix nums i x)) ∧
  (∀ j, j < write → ∃ t, t < i ∧ out[j]! = nums[t]!)

method removeDuplicatesTwice (nums : Array Int)
  returns (result : Nat × Array Int)
  requires sorted: precondition nums
  ensures compacted: postcondition nums result
do
  let mut i : Nat := 0
  let mut write : Nat := 0
  let mut out := nums
  while' scanning: i < nums.size
    invariant correct_prefix: CompactTwiceInvariant nums i write out
    decreasing remaining: nums.size - i
  do
    if room: write < 2 then
      out := out.set! write nums[i]!
      write := write + 1
    else
      if distinct: nums[i]! ≠ out[write - 2]! then
        out := out.set! write nums[i]!
        write := write + 1
    i := i + 1
  let mut j : Nat := write
  while' normalizing: j < out.size
    invariant suffix_bounds: write ≤ j ∧ j ≤ out.size
    invariant suffix_size: out.size = nums.size
    invariant suffix_counts: ∀ x,
      countInPrefix out write x = Nat.min 2 (countInPrefix nums nums.size x)
    invariant suffix_sorted: sortedPrefix out write
    decreasing suffix_remaining: out.size - j
  do
    out := out.set! j 0
    j := j + 1
  return (write, out)

end Implementation

section Proof

theorem countInPrefix_eq_list (a : Array Int) (k : Nat) (x : Int) :
    countInPrefix a k x = (a.toList.take k).count x := by
  unfold countInPrefix
  rw [← Array.count_toList]
  simp [Array.take_eq_extract, List.extract_eq_take_drop]

theorem countInPrefix_succ (a : Array Int) (k : Nat) (x : Int)
    (hk : k < a.size) :
    countInPrefix a (k + 1) x =
      countInPrefix a k x + if a[k]! = x then 1 else 0 := by
  rw [countInPrefix_eq_list, countInPrefix_eq_list,
    List.take_succ_eq_append_getElem (by simpa using hk)]
  by_cases h : a[k]! = x <;>
    simp_all [List.count_append, getElem!_pos]

theorem countInPrefix_set_succ (a : Array Int) (k : Nat) (v x : Int)
    (hk : k < a.size) :
    countInPrefix (a.set! k v) (k + 1) x =
      countInPrefix a k x + if v = x then 1 else 0 := by
  rw [countInPrefix_eq_list, countInPrefix_eq_list, Array.toList_set!]
  rw [List.take_succ_eq_append_getElem (by simpa [Array.size_set!] using hk)]
  rw [List.take_set_of_le (show k ≤ k by omega)]
  by_cases h : v = x <;> simp_all [List.count_append]

theorem sortedPrefix_le_of_lt (a : Array Int) (h : sortedPrefix a a.size)
    {i j : Nat} (hij : i < j) (hj : j < a.size) : a[i]! ≤ a[j]! := by
  have chain : ∀ d k, k + d < a.size → a[k]! ≤ a[k + d]! := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro k hkd
        cases d with
        | zero => simpa using h k (by omega)
        | succ d => exact (ih k (by omega)).trans (h (k + d + 1) (by omega))
  have heq : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  have hc := chain (j - i) i (by simpa [heq] using hj)
  simpa [heq] using hc

theorem sortedPrefix_le_of_lt_bound (a : Array Int) (k : Nat) (h : sortedPrefix a k)
    {i j : Nat} (hij : i < j) (hj : j < k) : a[i]! ≤ a[j]! := by
  have chain : ∀ d q, q + d < k → a[q]! ≤ a[q + d]! := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro q hqd
        cases d with
        | zero => simpa using h q (by omega)
        | succ d => exact (ih q (by omega)).trans (h (q + d + 1) (by omega))
  have heq : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  simpa [heq] using chain (j - i) i (by simpa [heq] using hj)

theorem countInPrefix_le (a : Array Int) (k : Nat) (x : Int) (hk : k ≤ a.size) :
    countInPrefix a k x ≤ k := by
  unfold countInPrefix
  exact Array.count_le_size.trans (by simp [hk])

theorem current_count_lt_two_iff (a : Array Int) (h : sortedPrefix a a.size)
    (i : Nat) (hi : i < a.size) :
    countInPrefix a i a[i]! < 2 ↔ i < 2 ∨ a[i - 2]! ≠ a[i]! := by
  let x := a[i]!
  constructor
  · intro hc
    by_cases hi2 : i < 2
    · exact Or.inl hi2
    · refine Or.inr ?_
      intro heq
      have him1 : i - 1 < a.size := by omega
      have him2 : i - 2 < a.size := by omega
      have hle1 : a[i - 2]! ≤ a[i - 1]! := sortedPrefix_le_of_lt a h (by omega) him1
      have hle2 : a[i - 1]! ≤ a[i]! := sortedPrefix_le_of_lt a h (by omega) hi
      have heq1 : a[i - 1]! = x := by
        dsimp [x]
        omega
      have heq2 : a[i - 2]! = x := by simpa [x] using heq
      have hc1 := countInPrefix_succ a (i - 1) x him1
      have hc2 := countInPrefix_succ a (i - 2) x him2
      have hidx1 : i - 1 + 1 = i := by omega
      have hidx2 : i - 2 + 1 = i - 1 := by omega
      change countInPrefix a i x < 2 at hc
      rw [hidx1, heq1] at hc1
      simp at hc1
      rw [hidx2, heq2] at hc2
      simp at hc2
      omega
  · rintro (hi2 | hneq)
    · exact (countInPrefix_le a i a[i]! (by omega)).trans_lt hi2
    · by_cases hi2 : i < 2
      · exact (countInPrefix_le a i a[i]! (by omega)).trans_lt hi2
      · have him1 : i - 1 < a.size := by omega
        have him2 : i - 2 < a.size := by omega
        have hle : a[i - 2]! ≤ a[i]! := sortedPrefix_le_of_lt a h (by omega) hi
        have hlt : a[i - 2]! < a[i]! := lt_of_le_of_ne hle hneq
        have hnotmem : a[i]! ∉ a.take (i - 1) := by
          intro hm
          simp [Array.mem_iff_getElem] at hm
          rcases hm with ⟨j, hj, heq⟩
          have hjold : j < a.size := by omega
          have heq' : a[j]! = a[i]! := by
            simpa [getElem!_pos, hjold] using heq
          have hjle : a[j]! ≤ a[i - 2]! := by
            by_cases hj_eq : j = i - 2
            · subst j; exact le_rfl
            · exact sortedPrefix_le_of_lt a h (by omega) him2
          omega
        have hz : countInPrefix a (i - 1) a[i]! = 0 := by
          exact Array.count_eq_zero.mpr hnotmem
        have hc := countInPrefix_succ a (i - 1) a[i]! him1
        have hidx : i - 1 + 1 = i := by omega
        rw [hidx, hz] at hc
        split at hc <;> omega

theorem prefix_count_lt_two_iff (a : Array Int) (k : Nat) (x : Int)
    (hk : k ≤ a.size) (hsorted : sortedPrefix a k)
    (hupper : ∀ j, j < k → a[j]! ≤ x) :
    countInPrefix a k x < 2 ↔ k < 2 ∨ a[k - 2]! ≠ x := by
  constructor
  · intro hc
    by_cases hk2 : k < 2
    · exact Or.inl hk2
    · right
      intro heq
      have hkm1 : k - 1 < a.size := by omega
      have hkm2 : k - 2 < a.size := by omega
      have hstep := hsorted (k - 2) (by omega)
      have hidx : k - 2 + 1 = k - 1 := by omega
      rw [hidx] at hstep
      have hbetween : a[k - 2]! ≤ a[k - 1]! := hstep
      have hlast : a[k - 1]! = x := by
        have := hupper (k - 1) (by omega)
        omega
      have hc1 := countInPrefix_succ a (k - 1) x hkm1
      have hc2 := countInPrefix_succ a (k - 2) x hkm2
      have hidx1 : k - 1 + 1 = k := by omega
      have hidx2 : k - 2 + 1 = k - 1 := by omega
      rw [hidx1, hlast] at hc1
      simp at hc1
      rw [hidx2, heq] at hc2
      simp at hc2
      omega
  · rintro (hk2 | hneq)
    · exact (countInPrefix_le a k x hk).trans_lt hk2
    · by_cases hk2 : k < 2
      · exact (countInPrefix_le a k x hk).trans_lt hk2
      · have hkm1 : k - 1 < a.size := by omega
        have hkm2 : k - 2 < a.size := by omega
        have hlt : a[k - 2]! < x := lt_of_le_of_ne (hupper (k - 2) (by omega)) hneq
        have hnotmem : x ∉ a.take (k - 1) := by
          intro hm
          simp [Array.mem_iff_getElem] at hm
          rcases hm with ⟨j, hj, heq⟩
          have hjold : j < a.size := by omega
          have heq' : a[j]! = x := by simpa [getElem!_pos, hjold] using heq
          have hjle : a[j]! ≤ a[k - 2]! := by
            by_cases hj_eq : j = k - 2
            · subst j; exact le_rfl
            · exact sortedPrefix_le_of_lt_bound a k hsorted (by omega) (by omega)
          omega
        have hz : countInPrefix a (k - 1) x = 0 := Array.count_eq_zero.mpr hnotmem
        have hc := countInPrefix_succ a (k - 1) x hkm1
        have hidx : k - 1 + 1 = k := by omega
        rw [hidx, hz] at hc
        split at hc <;> omega

theorem compact_output_le_current (nums out : Array Int) (i write : Nat)
    (hsorted : precondition nums) (hi : i < nums.size)
    (hinv : CompactTwiceInvariant nums i write out) :
    ∀ j, j < write → out[j]! ≤ nums[i]! := by
  intro j hj
  rcases hinv.2.2.2.2.2 j hj with ⟨t, ht, heq⟩
  rw [heq]
  exact sortedPrefix_le_of_lt nums hsorted ht hi

theorem compact_allowed_iff (nums out : Array Int) (i write : Nat)
    (hsorted : precondition nums) (hi : i < nums.size)
    (hinv : CompactTwiceInvariant nums i write out) :
    countInPrefix nums i nums[i]! < 2 ↔
      write < 2 ∨ nums[i]! ≠ out[write - 2]! := by
  have hprefix := prefix_count_lt_two_iff out write nums[i]!
    (by
      have hw : write ≤ i := hinv.2.1
      have hs : out.size = nums.size := hinv.2.2.1
      omega)
    hinv.2.2.2.1 (compact_output_le_current nums out i write hsorted hi hinv)
  rw [hinv.2.2.2.2.1] at hprefix
  have hminiff : Nat.min 2 (countInPrefix nums i nums[i]!) < 2 ↔
      countInPrefix nums i nums[i]! < 2 := by
    simp only [Nat.min_def]
    split <;> omega
  constructor
  · intro h
    rcases hprefix.mp (hminiff.mpr h) with hw | hne
    · exact Or.inl hw
    · exact Or.inr (Ne.symm hne)
  · rintro (hw | hne)
    · exact hminiff.mp (hprefix.mpr (Or.inl hw))
    · exact hminiff.mp (hprefix.mpr (Or.inr (Ne.symm hne)))

theorem compact_step_write (nums out : Array Int) (i write : Nat)
    (hsorted : precondition nums) (hi : i < nums.size)
    (hinv : CompactTwiceInvariant nums i write out)
    (hcur : countInPrefix nums i nums[i]! < 2) :
    CompactTwiceInvariant nums (i + 1) (write + 1) (out.set! write nums[i]!) := by
  rcases hinv with ⟨hib, hwritei, hsize, houtsorted, hcounts, horigin⟩
  have hwrite : write < out.size := by omega
  refine ⟨by omega, by omega, by simpa [Array.size_set!] using hsize, ?_, ?_, ?_⟩
  · intro j hj
    have hjw : j < write := by omega
    rw [Array.getElem!_set!_ne out write j _ (by omega)]
    by_cases hnext : j + 1 < write
    · rw [Array.getElem!_set!_ne out write (j + 1) _ (by omega)]
      exact houtsorted j hnext
    · have hnext_eq : j + 1 = write := by omega
      rw [hnext_eq, Array.getElem!_set!_self out write _ hwrite]
      rcases horigin j hjw with ⟨t, ht, heq⟩
      rw [heq]
      exact sortedPrefix_le_of_lt nums hsorted ht hi
  · intro x
    rw [countInPrefix_set_succ out write nums[i]! x hwrite,
      countInPrefix_succ nums i x hi, hcounts]
    by_cases hx : nums[i]! = x
    · subst x
      simp only [ite_true]
      have hc : countInPrefix nums i nums[i]! = 0 ∨
          countInPrefix nums i nums[i]! = 1 := by omega
      rcases hc with hc | hc <;> simp [hc]
    · simp [hx]
  · intro j hj
    by_cases hjw : j < write
    · rcases horigin j hjw with ⟨t, ht, heq⟩
      refine ⟨t, by omega, ?_⟩
      rw [Array.getElem!_set!_ne out write j _ (by omega)]
      exact heq
    · have hjeq : j = write := by omega
      subst j
      refine ⟨i, by omega, ?_⟩
      rw [Array.getElem!_set!_self out write _ hwrite]

theorem compact_step_skip (nums out : Array Int) (i write : Nat)
    (hi : i < nums.size) (hinv : CompactTwiceInvariant nums i write out)
    (hcur : ¬countInPrefix nums i nums[i]! < 2) :
    CompactTwiceInvariant nums (i + 1) write out := by
  rcases hinv with ⟨hib, hwritei, hsize, houtsorted, hcounts, horigin⟩
  refine ⟨by omega, by omega, hsize, houtsorted, ?_, ?_⟩
  · intro x
    rw [countInPrefix_succ nums i x hi, hcounts]
    by_cases hx : nums[i]! = x
    · subst x
      simp only [ite_true]
      have hc : 2 ≤ countInPrefix nums i nums[i]! := by omega
      exact (Nat.min_eq_left hc).trans (Nat.min_eq_left (by omega)).symm
    · simp [hx]
  · intro j hj
    rcases horigin j hj with ⟨t, ht, heq⟩
    exact ⟨t, by omega, heq⟩

theorem current_count_zero_of_new_value (nums : Array Int) (i : Nat)
    (hsorted : precondition nums) (hi : i < nums.size) (hipos : 0 < i)
    (hne : nums[i]! ≠ nums[i - 1]!) :
    countInPrefix nums i nums[i]! = 0 := by
  have him1 : i - 1 < nums.size := by omega
  have hlt : nums[i - 1]! < nums[i]! :=
    lt_of_le_of_ne (sortedPrefix_le_of_lt nums hsorted (by omega) hi) (Ne.symm hne)
  unfold countInPrefix
  apply Array.count_eq_zero.mpr
  intro hm
  simp [Array.mem_iff_getElem] at hm
  rcases hm with ⟨j, hj, heq⟩
  have hjnums : j < nums.size := by omega
  have hjeq : nums[j]! = nums[i]! := by
    simpa [getElem!_pos, hjnums] using heq
  have hjle : nums[j]! ≤ nums[i - 1]! := by
    by_cases hji : j = i - 1
    · subst j; exact le_rfl
    · exact sortedPrefix_le_of_lt nums hsorted (by omega) him1
  omega

theorem countInPrefix_set_outside (a : Array Int) (k j : Nat) (v x : Int)
    (hkj : k ≤ j) :
    countInPrefix (a.set! j v) k x = countInPrefix a k x := by
  rw [countInPrefix_eq_list, countInPrefix_eq_list, Array.toList_set!]
  rw [List.take_set_of_le hkj]

theorem sortedPrefix_set_outside (a : Array Int) (k j : Nat) (v : Int)
    (hkj : k ≤ j) (hsorted : sortedPrefix a k) :
    sortedPrefix (a.set! j v) k := by
  intro q hq
  rw [Array.getElem!_set!_ne a j q v (by omega),
    Array.getElem!_set!_ne a j (q + 1) v (by omega)]
  exact hsorted q hq

prove_correct removeDuplicatesTwice by
  velvet_vcgen [removeDuplicatesTwice, postcondition] with try finish
  case correct_prefix =>
    unfold CompactTwiceInvariant sortedPrefix countInPrefix
    simp
  case suffix_bounds =>
    unfold CompactTwiceInvariant at correct_prefix
    constructor
    · omega
    · rw [correct_prefix.2.2.1]
      omega
  case suffix_size => exact correct_prefix.2.2.1
  case suffix_counts =>
    rename_i nums
    unfold CompactTwiceInvariant at correct_prefix
    intro x
    have hi : i = nums.size := by omega
    subst i
    exact correct_prefix.2.2.2.2.1 x
  case suffix_sorted => exact correct_prefix.2.2.2.1
  case compacted =>
    exact ⟨suffix_size, by omega, suffix_sorted, suffix_counts⟩
  case suffix_counts =>
    intro x
    rw [countInPrefix_set_outside out write j 0 x suffix_bounds.1]
    exact suffix_counts x
  case suffix_sorted =>
    exact sortedPrefix_set_outside out write j 0 suffix_bounds.1 suffix_sorted
  case correct_prefix =>
    rename_i nums
    have hcur : countInPrefix nums i nums[i]! < 2 :=
      (compact_allowed_iff nums out i write sorted scanning correct_prefix).2 (Or.inl room)
    exact compact_step_write nums out i write sorted scanning correct_prefix hcur
  case correct_prefix =>
    rename_i nums
    have hcur : countInPrefix nums i nums[i]! < 2 :=
      (compact_allowed_iff nums out i write sorted scanning correct_prefix).2 (Or.inr distinct)
    exact compact_step_write nums out i write sorted scanning correct_prefix hcur
  case correct_prefix =>
    rename_i nums
    have hnot : ¬countInPrefix nums i nums[i]! < 2 := by
      intro hc
      rcases (compact_allowed_iff nums out i write sorted scanning correct_prefix).1 hc with
        hroom | hdistinct
      · exact room hroom
      · exact distinct hdistinct
    exact compact_step_skip nums out i write scanning correct_prefix hnot

end Proof

end RemoveDuplicatesFromSortedArrayII
