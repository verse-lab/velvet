module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range
public import Mathlib.Order.Interval.Finset.Nat

/-!
## Program description

Given a strictly increasing array of positive integers `arr` and a positive
integer `k`, return the kth positive integer that does not appear in `arr`.

The program is expected to run in O(log n) time and O(1) extra space.
-/

namespace KthMissingPositiveNumber

section Specs

public def inArrayB (arr : Array Nat) (x : Nat) : Bool :=
  arr.any (fun y => y == x)

public def strictlyIncreasing (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! < arr[i + 1]!

public def allPositive (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i < arr.size → 0 < arr[i]!

public def missingUpTo (arr : Array Nat) (n : Nat) : Nat :=
  ((Finset.Icc (1 : Nat) n).filter (fun m => !(inArrayB arr m))).card

public def precondition (arr : Array Nat) (k : Nat) : Prop :=
  k > 0 ∧ strictlyIncreasing arr ∧ allPositive arr

public def postcondition (arr : Array Nat) (k : Nat) (result : Nat) : Prop :=
  0 < result ∧
  inArrayB arr result = false ∧
  missingUpTo arr (Nat.pred result) = k - 1 ∧
  missingUpTo arr result = k

end Specs

section Implementation

method findKthPositive (arr : Array Nat) (k : Nat)
  returns (result : Nat)
  requires valid: precondition arr k
  ensures kth_missing: postcondition arr k result
do
  let mut lo : Nat := 0
  let mut hi : Nat := arr.size
  while' active: lo < hi
    invariant bounds: lo ≤ hi ∧ hi ≤ arr.size
    invariant all_lt: ∀ j, j < lo → arr[j]! - (j + 1) < k
    invariant ge_hi: hi < arr.size → k ≤ arr[hi]! - (hi + 1)
    decreasing width: hi - lo
    done_with done: lo = hi
  do
    let mid := lo + (hi - lo) / 2
    if arr[mid]! - (mid + 1) < k then
      lo := mid + 1
    else
      hi := mid
  return lo + k

end Implementation

section Proof

theorem arr_strict_mono (arr : Array Nat) (h : strictlyIncreasing arr)
    (i j : Nat) (hij : i < j) (hj : j < arr.size) : arr[i]! < arr[j]! := by
  have h_strict : ∀ k, k + 1 < arr.size → arr[k]! < arr[k + 1]! := h
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
    · have hj_lt : j < arr.size := by omega
      have h1 := ih i hlt hj_lt
      have h2 := h_strict j hj
      exact lt_trans h1 h2
    · subst heq
      exact h_strict i hj

theorem arr_ge_succ (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (i : Nat) (hi : i < arr.size) : arr[i]! ≥ i + 1 := by
  induction i with
  | zero =>
    have h0 := h_pos 0 hi
    omega
  | succ i ih =>
    have hi' : i < arr.size := by omega
    have h1 := ih hi'
    have h2 := h_inc i hi
    omega

theorem missingAt_mono (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (i j : Nat) (hij : i ≤ j) (hj : j < arr.size) :
    arr[i]! - (i + 1) ≤ arr[j]! - (j + 1) := by
  have h_arr_step : arr[i]! + (j - i) ≤ arr[j]! := by
    induction j generalizing i with
    | zero =>
      have : i = 0 := by omega
      subst this
      omega
    | succ j ih =>
      rcases Nat.lt_or_eq_of_le hij with hlt | heq
      · have hle_j : i ≤ j := Nat.le_of_lt_succ hlt
        have hj_lt : j < arr.size := by omega
        have h1 := ih i hle_j hj_lt
        have h2 := h_inc j hj
        omega
      · subst heq
        omega
  omega

theorem inArrayB_eq_true_iff (arr : Array Nat) (x : Nat) :
    inArrayB arr x = true ↔ ∃ i, i < arr.size ∧ arr[i]! = x := by
  unfold inArrayB
  rw [Array.any_eq_true]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, ?_⟩
    rw [getElem!_pos arr i hi]
    exact heq
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, ?_⟩
    rw [getElem!_pos arr i hi] at heq
    exact heq

theorem not_inArrayB_iff (arr : Array Nat) (x : Nat) :
    inArrayB arr x = false ↔ ∀ i, i < arr.size → arr[i]! ≠ x := by
  unfold inArrayB
  rw [Array.any_eq_false]
  simp only [beq_iff_eq]
  constructor
  · intro h i hi heq
    have := h i hi
    rw [getElem!_pos arr i hi] at heq
    exact this heq
  · intro h i hi heq
    have := h i hi
    rw [getElem!_pos arr i hi] at this
    exact this heq

theorem count_arr_in_icc (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (n : Nat) :
    ((Finset.Icc 1 n).filter (fun m => inArrayB arr m)).card =
    ((Finset.range arr.size).filter (fun i => arr[i]! ≤ n)).card := by
  classical
  have h_bij : (Finset.Icc 1 n).filter (fun m => inArrayB arr m = true) =
      Finset.image (fun i => arr[i]!) ((Finset.range arr.size).filter (fun i => arr[i]! ≤ n)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hin⟩
      rw [inArrayB_eq_true_iff] at hin
      rcases hin with ⟨i, hi, heq⟩
      subst heq
      refine ⟨i, ⟨hi, h2⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hle⟩, rfl⟩
      have hpos_i := h_pos i hi
      have h1 : 1 ≤ arr[i]! := by omega
      have hin : inArrayB arr arr[i]! = true := by
        rw [inArrayB_eq_true_iff]
        exact ⟨i, hi, rfl⟩
      exact ⟨⟨h1, hle⟩, hin⟩
  have h_filt_eq : (Finset.Icc 1 n).filter (fun m => inArrayB arr m) =
      (Finset.Icc 1 n).filter (fun m => inArrayB arr m = true) := rfl
  rw [h_filt_eq, h_bij, Finset.card_image_of_injOn]
  intro i hi j hj heq
  dsimp at heq
  have hi_sz : i < arr.size := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hj_sz : j < arr.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  rcases lt_trichotomy i j with hlt | heq_ij | hgt
  · have := arr_strict_mono arr h_inc i j hlt hj_sz
    omega
  · exact heq_ij
  · have := arr_strict_mono arr h_inc j i hgt hi_sz
    omega

theorem count_le_indices (arr : Array Nat) (_h_inc : strictlyIncreasing arr)
    (n idx : Nat) (hidx : idx ≤ arr.size)
    (h_below : ∀ i, i < idx → arr[i]! ≤ n)
    (h_above : ∀ i, idx ≤ i → i < arr.size → n < arr[i]!) :
    ((Finset.range arr.size).filter (fun i => arr[i]! ≤ n)).card = idx := by
  have h_set : (Finset.range arr.size).filter (fun i => arr[i]! ≤ n) = Finset.range idx := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi_sz, hle⟩
      by_contra h_ge
      have h_ge' : idx ≤ i := by omega
      have h_gt := h_above i h_ge' hi_sz
      omega
    · intro hi_idx
      have hi_sz : i < arr.size := by omega
      exact ⟨hi_sz, h_below i hi_idx⟩
  rw [h_set, Finset.card_range]

theorem missingUpTo_with_cutoff (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (h_pos : allPositive arr) (n idx : Nat) (hidx : idx ≤ arr.size)
    (h_below : ∀ i, i < idx → arr[i]! ≤ n)
    (h_above : ∀ i, idx ≤ i → i < arr.size → n < arr[i]!) :
    missingUpTo arr n = n - idx := by
  classical
  unfold missingUpTo
  have h_sdiff : (Finset.Icc 1 n).filter (fun m => !(inArrayB arr m)) =
      (Finset.Icc 1 n) \ (Finset.Icc 1 n).filter (fun m => inArrayB arr m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro ⟨hm, hb⟩
      refine ⟨hm, fun ⟨_, hb'⟩ => ?_⟩
      cases hb'' : inArrayB arr m
      · rw [hb''] at hb'
        contradiction
      · rw [hb''] at hb
        contradiction
    · rintro ⟨hm, hnot⟩
      refine ⟨hm, ?_⟩
      cases hb : inArrayB arr m
      · rfl
      · exfalso; exact hnot ⟨hm, hb⟩
  have h_sub : ((Finset.Icc 1 n) \ (Finset.Icc 1 n).filter (fun m => inArrayB arr m)).card =
      (Finset.Icc 1 n).card - ((Finset.Icc 1 n).filter (fun m => inArrayB arr m)).card :=
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  rw [h_sdiff, h_sub, Nat.card_Icc, count_arr_in_icc arr h_inc h_pos n,
      count_le_indices arr h_inc n idx hidx h_below h_above]
  omega

theorem below_cutoff_le (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (idx : Nat) (hidx : 0 < idx) (_hidx2 : idx ≤ arr.size)
    (n : Nat) (hn : arr[idx - 1]! ≤ n) (i : Nat) (hi : i < idx) :
    arr[i]! ≤ n := by
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (show i < (idx - 1) + 1 by omega)) with hlt | heq
  · have h1 := arr_strict_mono arr h_inc i (idx - 1) hlt (by omega)
    omega
  · subst heq
    exact hn

theorem above_cutoff_gt (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (idx : Nat) (_hidx2 : idx < arr.size)
    (n : Nat) (hn : n < arr[idx]!) (i : Nat) (hi : idx ≤ i)
    (hi2 : i < arr.size) :
    n < arr[i]! := by
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · have h1 := arr_strict_mono arr h_inc idx i hlt hi2
    omega
  · subst heq
    exact hn

theorem result_not_in_arr (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (idx : Nat) (hidx : 0 < idx) (_hidx2 : idx ≤ arr.size)
    (result : Nat)
    (hgt : arr[idx - 1]! < result)
    (hlt : idx = arr.size ∨ result < arr[idx]!) :
    inArrayB arr result = false := by
  rw [not_inArrayB_iff]
  intro i hi
  by_cases h_lt : i < idx
  · have hle : arr[i]! ≤ arr[idx - 1]! := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (show i < (idx - 1) + 1 by omega)) with hlt' | heq'
      · exact le_of_lt (arr_strict_mono arr h_inc i (idx - 1) hlt' (by omega))
      · subst heq'; rfl
    omega
  · have h_ge : idx ≤ i := by omega
    rcases hlt with heq_sz | hlt_idx
    · omega
    · have hgt_i : arr[idx]! ≤ arr[i]! := by
        rcases Nat.lt_or_eq_of_le h_ge with hlt' | heq'
        · exact le_of_lt (arr_strict_mono arr h_inc idx i hlt' hi)
        · subst heq'; rfl
      omega

theorem postcondition_of_bs (arr : Array Nat) (k : Nat) (hpre : precondition arr k)
    (idx : Nat) (hidx_le : idx ≤ arr.size)
    (hall_lt : ∀ j, j < idx → arr[j]! - (j + 1) < k)
    (hge_hi : idx < arr.size → k ≤ arr[idx]! - (idx + 1)) :
    postcondition arr k (idx + k) := by
  obtain ⟨hk_pos, h_inc, h_pos⟩ := hpre
  by_cases hidx0 : idx = 0
  · subst hidx0
    have hmiss_pred : missingUpTo arr (Nat.pred (0 + k)) = k - 1 := by
      simp only [Nat.pred_eq_sub_one]
      have hpred_eq : 0 + k - 1 = k - 1 := by omega
      rw [hpred_eq]
      unfold missingUpTo
      by_cases hk1 : k - 1 = 0
      · simp [hk1]
      · have h_all_notin : ∀ m, 1 ≤ m → m ≤ k - 1 → inArrayB arr m = false := by
          intro m _ hmk
          rw [not_inArrayB_iff]
          intro i hi
          by_cases hsz : 0 < arr.size
          · have h0_ge : k ≤ arr[0]! - 1 := by
              have := hge_hi hsz
              simpa using this
            have hi_ge : arr[0]! ≤ arr[i]! := by
              rcases Nat.eq_zero_or_pos i with rfl | hi_pos
              · rfl
              · exact le_of_lt (arr_strict_mono arr h_inc 0 i hi_pos hi)
            omega
          · omega
        have h_filt : (Finset.Icc 1 (k - 1)).filter (fun m => !(inArrayB arr m)) = Finset.Icc 1 (k - 1) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro ⟨hm, _⟩; exact hm
          · intro ⟨hm1, hmk⟩
            exact ⟨⟨hm1, hmk⟩, by simp [h_all_notin m hm1 hmk]⟩
        rw [h_filt, Nat.card_Icc]
        omega
    have h_all_notin_k : ∀ m, 1 ≤ m → m ≤ k → inArrayB arr m = false := by
      intro m _ hmk
      rw [not_inArrayB_iff]
      intro i hi
      by_cases hsz : 0 < arr.size
      · have h0_ge : k ≤ arr[0]! - 1 := by
          have := hge_hi hsz
          simpa using this
        have hi_ge : arr[0]! ≤ arr[i]! := by
          rcases Nat.eq_zero_or_pos i with rfl | hi_pos
          · rfl
          · exact le_of_lt (arr_strict_mono arr h_inc 0 i hi_pos hi)
        omega
      · omega
    have hmiss_k : missingUpTo arr (0 + k) = k := by
      have h_eq : 0 + k = k := by omega
      rw [h_eq]
      unfold missingUpTo
      have h_filt : (Finset.Icc 1 k).filter (fun m => !(inArrayB arr m)) = Finset.Icc 1 k := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro ⟨hm, _⟩; exact hm
        · intro ⟨hm1, hmk⟩
          exact ⟨⟨hm1, hmk⟩, by simp [h_all_notin_k m hm1 hmk]⟩
      rw [h_filt, Nat.card_Icc]
      omega
    have hnot_in_k : inArrayB arr (0 + k) = false := by
      have h_eq : 0 + k = k := by omega
      rw [h_eq]
      exact h_all_notin_k k (by omega) (by omega)
    unfold postcondition
    exact ⟨by omega, hnot_in_k, hmiss_pred, hmiss_k⟩
  · have hidx_pos : 0 < idx := Nat.pos_of_ne_zero hidx0
    have hmiss_prev_lt : arr[idx - 1]! - idx < k := by
      have := hall_lt (idx - 1) (by omega)
      have h_sub : (idx - 1) + 1 = idx := Nat.sub_add_cancel hidx_pos
      rwa [h_sub] at this
    have _h_arr_ge_idx : arr[idx - 1]! ≥ idx := by
      have h1 := arr_ge_succ arr h_inc h_pos (idx - 1) (by omega)
      have h2 : (idx - 1) + 1 = idx := Nat.sub_add_cancel hidx_pos
      rwa [h2] at h1
    have hresult_gt : arr[idx - 1]! < idx + k := by omega
    have hresult_lt : idx = arr.size ∨ idx + k < arr[idx]! := by
      by_cases hsz : idx < arr.size
      · have _hge := hge_hi hsz
        have _h_ge_succ := arr_ge_succ arr h_inc h_pos idx hsz
        right
        omega
      · left; omega
    have hnot_in : inArrayB arr (idx + k) = false :=
      result_not_in_arr arr h_inc idx hidx_pos hidx_le (idx + k) hresult_gt hresult_lt
    have hmiss_res : missingUpTo arr (idx + k) = k := by
      have h_below : ∀ i, i < idx → arr[i]! ≤ idx + k := by
        intro i hi
        exact below_cutoff_le arr h_inc idx hidx_pos hidx_le (idx + k) (by omega) i hi
      have h_above : ∀ i, idx ≤ i → i < arr.size → idx + k < arr[i]! := by
        intro i hi hi_sz
        rcases hresult_lt with _heq_sz | hlt
        · omega
        · exact above_cutoff_gt arr h_inc idx (by omega) (idx + k) hlt i hi hi_sz
      have hcut := missingUpTo_with_cutoff arr h_inc h_pos (idx + k) idx hidx_le h_below h_above
      omega
    have hmiss_pred : missingUpTo arr (Nat.pred (idx + k)) = k - 1 := by
      simp only [Nat.pred_eq_sub_one]
      have h_below : ∀ i, i < idx → arr[i]! ≤ idx + k - 1 := by
        intro i hi
        exact below_cutoff_le arr h_inc idx hidx_pos hidx_le (idx + k - 1) (by omega) i hi
      have h_above : ∀ i, idx ≤ i → i < arr.size → idx + k - 1 < arr[i]! := by
        intro i hi hi_sz
        rcases hresult_lt with _heq_sz | hlt
        · omega
        · have := above_cutoff_gt arr h_inc idx (by omega) (idx + k) hlt i hi hi_sz
          omega
      have hcut := missingUpTo_with_cutoff arr h_inc h_pos (idx + k - 1) idx hidx_le h_below h_above
      omega
    unfold postcondition
    exact ⟨by omega, hnot_in, hmiss_pred, hmiss_res⟩

prove_correct findKthPositive by
  velvet_vcgen [findKthPositive, precondition, postcondition]
  case bounds => omega
  case all_lt => intro j hj; omega
  case ge_hi => intro h; omega
  case kth_missing =>
    rename_i arr k
    have hidx_eq : lo = hi := done
    subst hidx_eq
    exact postcondition_of_bs arr k valid lo bounds.2 all_lt ge_hi
  case width => omega
  case bounds => omega
  case all_lt =>
    rename_i arr k
    intro j hj
    let mid := lo + (hi - lo) / 2
    rcases Nat.lt_or_ge j lo with hj_lt | _
    · exact all_lt j hj_lt
    · have hmid_sz : mid < arr.size := by omega
      have _h_mono := missingAt_mono arr valid.2.1 j mid (by omega) hmid_sz
      have _if_cond' : arr[mid]! - (mid + 1) < k := by simpa [mid] using if_cond
      omega
  case ge_hi => intro h; exact ge_hi h
  case width => omega
  case bounds => omega
  case all_lt => exact all_lt
  case ge_hi =>
    intro _
    omega
  case bounds => omega
  case all_lt => exact all_lt
  case ge_hi => exact ge_hi
  case done => omega

end Proof

end KthMissingPositiveNumber
