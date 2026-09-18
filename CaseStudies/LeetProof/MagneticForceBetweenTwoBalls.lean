module

public import Velvet
public meta import Velvet

/-!
## Program description

In the Magnetic Force Between Two Balls problem, we are given `n` basket
positions in an array `position` sorted in ascending order and an integer `m`.
We must place `m` balls into `m` distinct baskets such that the minimum
magnetic force (distance) between any two balls is maximized.

The program is expected to run in O(n log(max - min)) time and O(1) extra space.
-/

namespace MagneticForceBetweenTwoBalls

section Specs

public def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size → idxs[i]! < idxs[j]!

public def IndicesInRange (pos : Array Nat) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k < idxs.size → idxs[k]! < pos.size

public def PairwiseDistGE (pos : Array Nat) (idxs : Array Nat) (d : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size →
    d ≤ (pos[idxs[j]!]!) - (pos[idxs[i]!]!)

public def Feasible (pos : Array Nat) (m : Nat) (d : Nat) : Prop :=
  ∃ (idxs : Array Nat),
    idxs.size = m ∧
    StrictlyIncreasing idxs ∧
    IndicesInRange pos idxs ∧
    PairwiseDistGE pos idxs d

public def precondition (position : Array Nat) (m : Nat) : Prop :=
  m ≥ 2 ∧ m ≤ position.size ∧ StrictlyIncreasing position

public def postcondition (position : Array Nat) (m : Nat) (result : Nat) : Prop :=
  Feasible position m result ∧
  (∀ (d' : Nat), result < d' → ¬ Feasible position m d')

end Specs

section Implementation

method maxDistance (position : Array Nat) (m : Nat)
  returns (result : Nat)
  requires valid: precondition position m
  ensures max_force: postcondition position m result
do
  let n := position.size
  let loInit : Nat := 0
  let hiInit : Nat := position[n - 1]! - position[0]!
  let mut lo := loInit
  let mut hi := hiInit

  while' searching: lo < hi
    invariant bs_bounds: lo ≤ hi ∧ hi ≤ position[position.size - 1]! - position[0]!
    invariant bs_lo_feasible: Feasible position m lo
    invariant bs_hi1_infeasible: ¬ Feasible position m (hi + 1)
    invariant bs_mono: ∀ (d1 d2 : Nat), d1 ≤ d2 → Feasible position m d2 → Feasible position m d1
    decreasing remaining_range: hi - lo
    done_with bs_done: lo = hi
  do
    let mid := (lo + hi + 1) / 2
    let mut cnt : Nat := 1
    let mut lastPos : Nat := position[0]!
    let mut i : Nat := 1
    while' greedy: i < n ∧ cnt < m
      invariant gr_i_bounds: 1 ≤ i ∧ i ≤ n
      invariant gr_cnt_bounds: 1 ≤ cnt ∧ cnt ≤ m ∧ cnt ≤ i
      invariant gr_witness:
        ∃ (idxs : Array Nat),
          idxs.size = cnt ∧
          StrictlyIncreasing idxs ∧
          IndicesInRange position idxs ∧
          PairwiseDistGE position idxs mid ∧
          idxs[cnt - 1]! < i ∧
          lastPos = position[idxs[cnt - 1]!]!
      invariant gr_min_extend_prefix:
        ∀ (idxs2 : Array Nat), cnt < idxs2.size →
          StrictlyIncreasing idxs2 →
          IndicesInRange position idxs2 →
          PairwiseDistGE position idxs2 mid →
          lastPos ≤ position[idxs2[cnt - 1]!]!
      invariant gr_no_more_prefix:
        ∀ (idxs2 : Array Nat), cnt < idxs2.size →
          StrictlyIncreasing idxs2 →
          IndicesInRange position idxs2 →
          PairwiseDistGE position idxs2 mid →
          i ≤ idxs2[cnt]!
      decreasing greedy_remaining: n - i
      done_with greedy_done: i ≥ n ∨ cnt ≥ m
    do
      let p := position[i]!
      if can_place: mid ≤ p - lastPos then
        cnt := cnt + 1
        lastPos := p
      i := i + 1

    if place_enough: cnt ≥ m then
      lo := mid
    else
      hi := mid - 1

  return lo

end Implementation

section Proof

theorem getElem!_push_lt (arr : Array Nat) (x : Nat) (k : Nat) (hk : k < arr.size) :
    (arr.push x)[k]! = arr[k]! := by
  have hk_push : k < (arr.push x).size := by
    rw [Array.size_push]
    omega
  rw [getElem!_pos (arr.push x) k hk_push, getElem!_pos arr k hk]
  exact Array.getElem_push_lt hk

theorem getElem!_push_eq (arr : Array Nat) (x : Nat) :
    (arr.push x)[arr.size]! = x := by
  have hk_push : arr.size < (arr.push x).size := by
    rw [Array.size_push]
    omega
  rw [getElem!_pos (arr.push x) arr.size hk_push]
  exact Array.getElem_push_eq

theorem pos_mono (position : Array Nat) (hinc : StrictlyIncreasing position)
    (i j : Nat) (hij : i ≤ j) (hj : j < position.size) :
    position[i]! ≤ position[j]! := by
  by_cases heq : i = j
  · subst heq; exact Nat.le_refl _
  · have hlt : i < j := Nat.lt_of_le_of_ne hij heq
    exact Nat.le_of_lt (hinc i j hlt hj)

theorem idxs_mono (idxs : Array Nat) (hinc : StrictlyIncreasing idxs)
    (i j : Nat) (hij : i ≤ j) (hj : j < idxs.size) :
    idxs[i]! ≤ idxs[j]! := by
  by_cases heq : i = j
  · subst heq; exact Nat.le_refl _
  · have hlt : i < j := Nat.lt_of_le_of_ne hij heq
    exact Nat.le_of_lt (hinc i j hlt hj)

theorem feasible_mono (position : Array Nat) (m : Nat) :
    ∀ (d1 d2 : Nat), d1 ≤ d2 → Feasible position m d2 → Feasible position m d1 := by
  intro d1 d2 hle ⟨idxs, hsize, hinc, hinrange, hdist⟩
  refine ⟨idxs, hsize, hinc, hinrange, ?_⟩
  intro i j hij hj
  exact Nat.le_trans hle (hdist i j hij hj)

theorem feasible_zero (position : Array Nat) (m : Nat) (hpre : precondition position m) :
    Feasible position m 0 := by
  let idxs : Array Nat := (List.range m).toArray
  have hsize : idxs.size = m := by
    simp [idxs]
  refine ⟨idxs, hsize, ?_, ?_, ?_⟩
  · intro i j hij hj
    have hjm : j < m := by simpa [hsize] using hj
    have him : i < m := Nat.lt_trans hij hjm
    have hgi : idxs[i]! = i := by
      rw [getElem!_pos idxs i (by simpa [hsize] using him)]
      simp [idxs]
    have hgj : idxs[j]! = j := by
      rw [getElem!_pos idxs j (by simpa [hsize] using hjm)]
      simp [idxs]
    rw [hgi, hgj]
    exact hij
  · intro k hk
    have hkm : k < m := by simpa [hsize] using hk
    have hgk : idxs[k]! = k := by
      rw [getElem!_pos idxs k (by simpa [hsize] using hkm)]
      simp [idxs]
    rw [hgk]
    exact Nat.lt_of_lt_of_le hkm hpre.2.1
  · intro i j hij hj
    exact Nat.zero_le _

theorem not_feasible_above_range (position : Array Nat) (m : Nat)
    (hpre : precondition position m) :
    ¬ Feasible position m (position[position.size - 1]! - position[0]! + 1) := by
  intro ⟨idxs, hsize, hinc, hinrange, hdist⟩
  have hm2 : 2 ≤ m := hpre.1
  have h0_lt : 0 < m - 1 := by omega
  have hm1_lt : m - 1 < idxs.size := by omega
  have hdist0 := hdist 0 (m - 1) h0_lt hm1_lt
  have h0_range : idxs[0]! < position.size := hinrange 0 (by omega)
  have hm1_range : idxs[m - 1]! < position.size := hinrange (m - 1) (by omega)
  have hpos0 : position[0]! ≤ position[idxs[0]!]! :=
    pos_mono position hpre.2.2 0 (idxs[0]!) (Nat.zero_le _) h0_range
  have hposm1 : position[idxs[m - 1]!]! ≤ position[position.size - 1]! :=
    pos_mono position hpre.2.2 (idxs[m - 1]!) (position.size - 1)
      (Nat.le_pred_of_lt hm1_range) (by have : 2 ≤ position.size := Nat.le_trans hpre.1 hpre.2.1; omega)
  omega

theorem greedy_init_witness (position : Array Nat) (hpre : precondition position m) (d : Nat) :
    ∃ (idxs : Array Nat),
      idxs.size = 1 ∧
      StrictlyIncreasing idxs ∧
      IndicesInRange position idxs ∧
      PairwiseDistGE position idxs d ∧
      idxs[0]! < 1 ∧
      position[0]! = position[idxs[0]!]! := by
  refine ⟨#[0], rfl, ?_, ?_, ?_, by simp, rfl⟩
  · intro i j hij hj
    simp at hj
    omega
  · intro k hk
    simp at hk
    subst hk
    simp
    have : 2 ≤ position.size := Nat.le_trans hpre.1 hpre.2.1
    omega
  · intro i j hij hj
    simp at hj
    omega

theorem greedy_step_witness
    (position : Array Nat) (hpos_inc : StrictlyIncreasing position)
    (d cnt i : Nat) (lastPos : Nat)
    (idxs : Array Nat)
    (hsize : idxs.size = cnt)
    (hinc : StrictlyIncreasing idxs)
    (hinrange : IndicesInRange position idxs)
    (hdist : PairwiseDistGE position idxs d)
    (hlast_idx : idxs[cnt - 1]! < i)
    (hlast_pos : lastPos = position[idxs[cnt - 1]!]!)
    (hi_lt : i < position.size)
    (hcnt_pos : 1 ≤ cnt)
    (hcan : d ≤ position[i]! - lastPos) :
    ∃ (idxs' : Array Nat),
      idxs'.size = cnt + 1 ∧
      StrictlyIncreasing idxs' ∧
      IndicesInRange position idxs' ∧
      PairwiseDistGE position idxs' d ∧
      idxs'[cnt + 1 - 1]! < i + 1 ∧
      position[i]! = position[idxs'[cnt + 1 - 1]!]! := by
  let idxs' := idxs.push i
  have hsize' : idxs'.size = cnt + 1 := by
    simp [idxs', hsize]
  have hget_lt : ∀ k, k < cnt → idxs'[k]! = idxs[k]! := by
    intro k hk
    simp [idxs', getElem!_push_lt idxs i k (by omega)]
  have hget_cnt : idxs'[cnt]! = i := by
    have : idxs.size = cnt := hsize
    rw [← this]
    exact getElem!_push_eq idxs i
  refine ⟨idxs', hsize', ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab hb
    have hb' : b < cnt + 1 := by simpa [hsize'] using hb
    by_cases hb_lt : b < cnt
    · rw [hget_lt a (Nat.lt_trans hab hb_lt), hget_lt b hb_lt]
      exact hinc a b hab (by omega)
    · have hbeq : b = cnt := by omega
      rw [hbeq, hget_cnt, hget_lt a (by omega)]
      by_cases ha_eq : a = cnt - 1
      · rw [ha_eq]
        exact hlast_idx
      · have ha_lt : a < cnt - 1 := by omega
        have : idxs[a]! < idxs[cnt - 1]! := hinc a (cnt - 1) ha_lt (by omega)
        exact Nat.lt_trans this hlast_idx
  · intro k hk
    have hk' : k < cnt + 1 := by simpa [hsize'] using hk
    by_cases hk_lt : k < cnt
    · rw [hget_lt k hk_lt]
      exact hinrange k (by omega)
    · have hkeq : k = cnt := by omega
      rw [hkeq, hget_cnt]
      exact hi_lt
  · intro a b hab hb
    have hb' : b < cnt + 1 := by simpa [hsize'] using hb
    by_cases hb_lt : b < cnt
    · rw [hget_lt a (Nat.lt_trans hab hb_lt), hget_lt b hb_lt]
      exact hdist a b hab (by omega)
    · have hbeq : b = cnt := by omega
      rw [hbeq, hget_cnt, hget_lt a (by omega)]
      have ha_le : a ≤ cnt - 1 := by omega
      have hidx_le : idxs[a]! ≤ idxs[cnt - 1]! :=
        idxs_mono idxs hinc a (cnt - 1) ha_le (by omega)
      have hpos_le : position[idxs[a]!]! ≤ position[idxs[cnt - 1]!]! :=
        pos_mono position hpos_inc (idxs[a]!) (idxs[cnt - 1]!) hidx_le (hinrange (cnt - 1) (by omega))
      omega
  · have hidx_last : idxs'[cnt + 1 - 1]! = i := by
      have : cnt + 1 - 1 = cnt := by omega
      rw [this, hget_cnt]
    rw [hidx_last]
    omega
  · have hidx_last : idxs'[cnt + 1 - 1]! = i := by
      have : cnt + 1 - 1 = cnt := by omega
      rw [this, hget_cnt]
    rw [hidx_last]

prove_correct maxDistance by
  velvet_vcgen [maxDistance]
  case bs_bounds =>
    have : 2 ≤ _ := Nat.le_trans valid.1 valid.2.1
    omega
  case bs_lo_feasible =>
    rename_i position m
    exact feasible_zero position m valid
  case bs_hi1_infeasible =>
    rename_i position m
    exact not_feasible_above_range position m valid
  case bs_mono =>
    rename_i position m
    exact feasible_mono position m
  case max_force =>
    rename_i position m
    refine ⟨bs_lo_feasible, ?_⟩
    intro d' hd' hfeas'
    have hle : lo + 1 ≤ d' := by omega
    have hfeas_hi1 := bs_mono (lo + 1) d' hle hfeas'
    have : lo + 1 = hi + 1 := by omega
    rw [this] at hfeas_hi1
    exact bs_hi1_infeasible hfeas_hi1
  case gr_i_bounds =>
    have : 2 ≤ _ := Nat.le_trans valid.1 valid.2.1
    omega
  case gr_cnt_bounds =>
    have : 2 ≤ _ := valid.1
    omega
  case gr_witness =>
    rename_i position m
    exact greedy_init_witness position valid ((lo + hi + 1) / 2)
  case gr_min_extend_prefix =>
    rename_i position m
    intro idxs2 hlen2 hinc2 hinrange2 hdist2
    have h0 : 0 ≤ idxs2[0]! := Nat.zero_le _
    have h_idx0 : idxs2[0]! < position.size := hinrange2 0 (by omega)
    exact pos_mono position valid.2.2 0 (idxs2[0]!) h0 h_idx0
  case gr_no_more_prefix =>
    intro idxs2 hlen2 hinc2 hinrange2 hdist2
    have : idxs2[0]! < idxs2[1]! := hinc2 0 1 (by omega) (by omega)
    omega
  case remaining_range =>
    omega
  case bs_bounds =>
    omega
  case bs_lo_feasible =>
    rename_i position m
    have hcnteq : cnt = m := by omega
    rcases gr_witness with ⟨idxs, hsize, hinc, hinrange, hdist, _⟩
    rw [hcnteq] at hsize
    exact ⟨idxs, hsize, hinc, hinrange, hdist⟩
  case bs_hi1_infeasible =>
    exact bs_hi1_infeasible
  case bs_mono =>
    exact bs_mono
  case remaining_range =>
    omega
  case bs_bounds =>
    omega
  case bs_lo_feasible =>
    exact bs_lo_feasible
  case bs_hi1_infeasible =>
    have hmid_eq : (lo + hi + 1) / 2 - 1 + 1 = (lo + hi + 1) / 2 := by omega
    rw [hmid_eq]
    intro ⟨idxs, hsize, hinc, hinrange, hdist⟩
    have hcnt_lt : cnt < idxs.size := by omega
    have h_i : i ≤ idxs[cnt]! := gr_no_more_prefix idxs hcnt_lt hinc hinrange hdist
    have h_in_range : idxs[cnt]! < _ := hinrange cnt (by omega)
    omega
  case bs_mono =>
    exact bs_mono
  case greedy_remaining =>
    omega
  case gr_i_bounds =>
    omega
  case gr_cnt_bounds =>
    omega
  case gr_witness =>
    rename_i position m
    rcases gr_witness with ⟨idxs, hsize, hinc, hinrange, hdist, hlast_idx, hlast_pos⟩
    exact greedy_step_witness position valid.2.2 ((lo + hi + 1) / 2) cnt i lastPos
      idxs hsize hinc hinrange hdist hlast_idx hlast_pos (by omega) (by omega) can_place
  case gr_min_extend_prefix =>
    rename_i position m
    intro idxs2 hlen2 hinc2 hinrange2 hdist2
    have : i ≤ idxs2[cnt]! := gr_no_more_prefix idxs2 (by omega) hinc2 hinrange2 hdist2
    have h_idx_range : idxs2[cnt]! < position.size := hinrange2 cnt (by omega)
    have : cnt + 1 - 1 = cnt := by omega
    rw [this]
    exact pos_mono position valid.2.2 i (idxs2[cnt]!) (by omega) h_idx_range
  case gr_no_more_prefix =>
    intro idxs2 hlen2 hinc2 hinrange2 hdist2
    have h_i : i ≤ idxs2[cnt]! := gr_no_more_prefix idxs2 (by omega) hinc2 hinrange2 hdist2
    have h_inc : idxs2[cnt]! < idxs2[cnt + 1]! := hinc2 cnt (cnt + 1) (by omega) (by omega)
    omega
  case greedy_remaining =>
    omega
  case gr_i_bounds =>
    omega
  case gr_cnt_bounds =>
    omega
  case gr_witness =>
    rcases gr_witness with ⟨idxs, hsize, hinc, hinrange, hdist, hlast_idx, hlast_pos⟩
    refine ⟨idxs, hsize, hinc, hinrange, hdist, by omega, hlast_pos⟩
  case gr_min_extend_prefix =>
    intro idxs2 hlen2 hinc2 hinrange2 hdist2
    exact gr_min_extend_prefix idxs2 hlen2 hinc2 hinrange2 hdist2
  case gr_no_more_prefix =>
    intro idxs2 hlen2 hinc2 hinrange2 hdist2
    have h_i : i ≤ idxs2[cnt]! := gr_no_more_prefix idxs2 hlen2 hinc2 hinrange2 hdist2
    by_cases heq : idxs2[cnt]! = i
    · have hdist_cnt := hdist2 (cnt - 1) cnt (by omega) (by omega)
      have hmin := gr_min_extend_prefix idxs2 hlen2 hinc2 hinrange2 hdist2
      rw [heq] at hdist_cnt
      omega
    · omega
  case gr_i_bounds =>
    omega
  case gr_cnt_bounds =>
    omega
  case gr_witness =>
    exact gr_witness
  case gr_min_extend_prefix =>
    exact gr_min_extend_prefix
  case gr_no_more_prefix =>
    exact gr_no_more_prefix
  case greedy_done =>
    omega
  case bs_bounds =>
    exact bs_bounds
  case bs_lo_feasible =>
    exact bs_lo_feasible
  case bs_hi1_infeasible =>
    exact bs_hi1_infeasible
  case bs_mono =>
    exact bs_mono
  case bs_done =>
    omega

end Proof

end MagneticForceBetweenTwoBalls
