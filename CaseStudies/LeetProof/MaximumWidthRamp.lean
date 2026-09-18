module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an integer array `nums`, return the maximum width of a ramp in `nums`.
If there is no ramp, return `0`.

A ramp in an integer array `nums` is a pair `(i, j)` for which `i < j` and
`nums[i] ≤ nums[j]`. The width of such a ramp is `j - i`.

The program is expected to run in O(n) time and O(n) extra space.
-/

namespace MaximumWidthRamp

section Specs

public def IsRamp (nums : Array Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! ≤ nums[j]!

public def IsRampWidth (nums : Array Int) (w : Nat) : Prop :=
  ∃ (i : Nat) (j : Nat), IsRamp nums i j ∧ w = j - i

public def precondition (_nums : Array Int) : Prop :=
  True

public def postcondition (nums : Array Int) (result : Nat) : Prop :=
  (result = 0 ∨ IsRampWidth nums result) ∧
  (∀ (w : Nat), IsRampWidth nums w → w ≤ result)

end Specs

section Implementation

public def buildStackStep (nums : Array Int) (i : Nat) (st : List Nat) : List Nat :=
  match st with
  | [] => [i]
  | top :: _ =>
    if nums[i]! < nums[top]! then i :: st
    else st

public def popWhile (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) : List Nat × Nat :=
  match st with
  | [] => ([], best)
  | i :: rest =>
    if nums[i]! ≤ nums[j]! then
      popWhile nums j rest (Nat.max best (j - i))
    else
      (st, best)

public def CanPop (nums : Array Int) (j : Nat) (st : List Nat) : Bool :=
  match st with
  | [] => false
  | i :: _ => decide (nums[i]! ≤ nums[j]!)

public def StackBounded (i : Nat) (st : List Nat) : Prop :=
  ∀ s ∈ st, s < i

public def StackCovers (nums : Array Int) (i : Nat) (st : List Nat) : Prop :=
  ∀ k < i, ∃ s ∈ st, s ≤ k ∧ nums[s]! ≤ nums[k]!

public def StackSorted (nums : Array Int) (st : List Nat) : Prop :=
  List.Pairwise (fun a b => a > b ∧ nums[a]! < nums[b]!) st

public def StackInvariant (nums : Array Int) (i : Nat) (st : List Nat) : Prop :=
  StackCovers nums i st ∧ StackBounded i st

public def ScanInvariant (nums : Array Int) (st0 : List Nat) (j : Int) (cur_st : List Nat) (best : Nat) : Prop :=
  StackSorted nums cur_st ∧
  cur_st ⊆ st0 ∧
  (best = 0 ∨ IsRampWidth nums best) ∧
  (∀ u ∈ cur_st, ∀ v : Nat, j < (v : Int) → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ k ∈ st0, k ∉ cur_st → ∃ v : Nat, j < (v : Int) ∧ v < nums.size ∧ nums[k]! ≤ nums[v]! ∧ v - k ≤ best) ∧
  (∀ k ∈ st0, ∀ v : Nat, j < (v : Int) → v < nums.size → IsRamp nums k v → v - k ≤ best)

method maximumWidthRamp (nums : Array Int)
  returns (result : Nat)
  requires valid: precondition nums
  ensures max_ramp: postcondition nums result
do
  let n := nums.size
  if small: n ≤ 1 then
    return 0
  else
    let mut st : List Nat := []
    let mut i : Nat := 0
    while building: i < n
      invariant i_bound: i ≤ n
      invariant st_inv: StackInvariant nums i st
      invariant st_sorted: StackSorted nums st
      decreasing dec_i: n - i
      done_with done_i: i = n
    do
      st := buildStackStep nums i st
      i := i + 1

    let mut j : Nat := n
    let mut cur_st : List Nat := st
    let mut best : Nat := 0
    while scanning: j > 0
      invariant j_bound: j ≤ n
      invariant scan_inv: ScanInvariant nums st ((j : Int) - 1) cur_st best
      decreasing dec_j: j
      done_with done_j: j = 0
    do
      j := j - 1
      let target := popWhile nums j cur_st best
      while popping:
          CanPop nums j cur_st
        invariant continuation:
          popWhile nums j cur_st best = target
        decreasing stack_size: cur_st.length
        done_with popped: (cur_st, best) = target
      do
        match cur_st with
        | [] => pure ()
        | left :: rest =>
          best := Nat.max best (j - left)
          cur_st := rest

    return best

end Implementation

section Proof

theorem popWhile_cons_le (nums : Array Int) (j i best : Nat) (rest : List Nat)
    (h : nums[i]! ≤ nums[j]!) :
    popWhile nums j (i :: rest) best =
      popWhile nums j rest (Nat.max best (j - i)) := by
  simp [popWhile, h]

theorem popWhile_cons_not_le (nums : Array Int) (j i best : Nat) (rest : List Nat)
    (h : ¬nums[i]! ≤ nums[j]!) :
    popWhile nums j (i :: rest) best = (i :: rest, best) := by
  simp [popWhile, h]

theorem small_postcondition (nums : Array Int) (h : nums.size ≤ 1) :
    postcondition nums 0 := by
  unfold postcondition
  refine ⟨Or.inl rfl, ?_⟩
  intro w hw
  obtain ⟨i, j, hij, _⟩ := hw
  have : i < j ∧ j < nums.size := ⟨hij.1, hij.2.1⟩
  omega

theorem stackInvariant_init (nums : Array Int) :
    StackInvariant nums 0 [] := by
  unfold StackInvariant StackCovers StackBounded
  refine ⟨?_, ?_⟩
  · intro k hk; omega
  · intro s hs; cases hs

theorem stackSorted_init (nums : Array Int) :
    StackSorted nums [] := by
  unfold StackSorted
  exact List.Pairwise.nil

theorem buildStackStep_sorted (nums : Array Int) (i : Nat) (st : List Nat)
    (hinv : StackInvariant nums i st) (hsorted : StackSorted nums st) :
    StackSorted nums (buildStackStep nums i st) := by
  cases st with
  | nil =>
    unfold buildStackStep StackSorted
    exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
  | cons top tail =>
    unfold buildStackStep
    by_cases hlt : nums[i]! < nums[top]!
    · simp only [hlt, ↓reduceIte]
      unfold StackSorted at *
      refine List.Pairwise.cons ?_ hsorted
      intro s hs
      have hs_lt_i : s < i := hinv.2 s hs
      cases hs with
      | head =>
        exact ⟨hs_lt_i, hlt⟩
      | tail _ hs_tail =>
        have h_pair := (List.pairwise_cons.mp hsorted).1 s hs_tail
        have : nums[top]! < nums[s]! := h_pair.2
        exact ⟨hs_lt_i, by omega⟩
    · simp only [hlt, ↓reduceIte]
      exact hsorted

theorem buildStackStep_invariant (nums : Array Int) (i : Nat) (st : List Nat)
    (hinv : StackInvariant nums i st) :
    StackInvariant nums (i + 1) (buildStackStep nums i st) := by
  obtain ⟨hcovers, hbounded⟩ := hinv
  cases st with
  | nil =>
    unfold buildStackStep StackInvariant StackCovers StackBounded
    refine ⟨?_, ?_⟩
    · intro k hk
      have hi0 : i = 0 := by
        by_cases h : i = 0
        · exact h
        · have := hcovers 0 (by omega)
          obtain ⟨s, hs, _⟩ := this
          cases hs
      have hk0 : k = 0 := by omega
      subst hi0 hk0
      exact ⟨0, List.mem_singleton_self 0, by omega, by omega⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      omega
  | cons top tail =>
    unfold buildStackStep
    by_cases hlt : nums[i]! < nums[top]!
    · simp only [hlt, ↓reduceIte]
      unfold StackInvariant StackCovers StackBounded
      refine ⟨?_, ?_⟩
      · intro k hk
        by_cases hki : k < i
        · obtain ⟨s, hs, hsk, hsval⟩ := hcovers k hki
          refine ⟨s, List.mem_cons_of_mem i hs, hsk, hsval⟩
        · have hkeq : k = i := by omega
          subst k
          refine ⟨i, List.mem_cons.2 (Or.inl rfl), by omega, by omega⟩
      · intro s hs
        cases hs with
        | head => omega
        | tail _ hs_tail =>
          have : s < i := hbounded s hs_tail
          omega
    · simp only [hlt, ↓reduceIte]
      unfold StackInvariant StackCovers StackBounded
      refine ⟨?_, ?_⟩
      · intro k hk
        by_cases hki : k < i
        · exact hcovers k hki
        · have hkeq : k = i := by omega
          subst k
          have htop_in : top ∈ top :: tail := List.mem_cons.2 (Or.inl rfl)
          have htop_lt : top < i := hbounded top htop_in
          have htop_le : nums[top]! ≤ nums[i]! := by omega
          exact ⟨top, htop_in, by omega, htop_le⟩
      · intro s hs
        have : s < i := hbounded s hs
        omega

theorem scanInvariant_init (nums : Array Int) (st : List Nat)
    (hsorted : StackSorted nums st) :
    ScanInvariant nums st ((nums.size : Int) - 1) st 0 := by
  refine ⟨hsorted, List.Subset.refl _, Or.inl rfl, ?_, ?_, ?_⟩
  · intro u _ v hv1 hv2; omega
  · intro k _ hk_not; exact False.elim (hk_not (by assumption))
  · intro k _ v hv1 hv2 _; omega

theorem popWhile_subset (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
    (popWhile nums j st best).1 ⊆ st := by
  induction st generalizing best with
  | nil =>
    unfold popWhile
    exact List.Subset.refl _
  | cons i rest ih =>
    unfold popWhile
    by_cases hle : nums[i]! ≤ nums[j]!
    · simp only [hle, ↓reduceIte]
      intro x hx
      exact List.mem_cons_of_mem i (ih (best.max (j - i)) hx)
    · simp only [hle, ↓reduceIte]
      exact List.Subset.refl _

theorem popWhile_sorted (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat)
    (h : StackSorted nums st) :
    StackSorted nums (popWhile nums j st best).1 := by
  induction st generalizing best with
  | nil =>
    unfold popWhile
    exact h
  | cons i rest ih =>
    unfold popWhile
    by_cases hle : nums[i]! ≤ nums[j]!
    · simp only [hle, ↓reduceIte]
      unfold StackSorted at h
      exact ih (best.max (j - i)) (List.Pairwise.of_cons h)
    · simp only [hle, ↓reduceIte]
      exact h

theorem popWhile_keeps_greater (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat)
    (h : StackSorted nums st) :
    ∀ u ∈ (popWhile nums j st best).1, nums[u]! > nums[j]! := by
  induction st generalizing best with
  | nil =>
    unfold popWhile
    intro u hu
    cases hu
  | cons i rest ih =>
    unfold popWhile
    by_cases hle : nums[i]! ≤ nums[j]!
    · simp only [hle, ↓reduceIte]
      unfold StackSorted at h
      exact ih (best.max (j - i)) (List.Pairwise.of_cons h)
    · simp only [hle, ↓reduceIte]
      intro u hu
      have hgt : nums[i]! > nums[j]! := by omega
      cases hu with
      | head => exact hgt
      | tail _ hu_rest =>
        unfold StackSorted at h
        have h_pair := (List.pairwise_cons.mp h).1 u hu_rest
        have : nums[u]! > nums[i]! := h_pair.2
        omega

theorem popWhile_best_ge (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
    best ≤ (popWhile nums j st best).2 := by
  induction st generalizing best with
  | nil =>
    unfold popWhile
    omega
  | cons i rest ih =>
    unfold popWhile
    by_cases hle : nums[i]! ≤ nums[j]!
    · simp only [hle, ↓reduceIte]
      have h1 : best ≤ best.max (j - i) := Nat.le_max_left _ _
      have h2 := ih (best.max (j - i))
      omega
    · simp only [hle, ↓reduceIte]
      omega

theorem popWhile_popped_le (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
    ∀ k ∈ st, k ∉ (popWhile nums j st best).1 →
      nums[k]! ≤ nums[j]! ∧ j - k ≤ (popWhile nums j st best).2 := by
  induction st generalizing best with
  | nil =>
    intro k hk
    cases hk
  | cons i rest ih =>
    intro k hk hk_not
    unfold popWhile at hk_not ⊢
    by_cases hle : nums[i]! ≤ nums[j]!
    · simp only [hle, ↓reduceIte] at hk_not ⊢
      cases hk with
      | head =>
        refine ⟨hle, ?_⟩
        have h_step : j - i ≤ best.max (j - i) := Nat.le_max_right _ _
        have h_ind := popWhile_best_ge nums j rest (best.max (j - i))
        omega
      | tail _ hk_tail =>
        exact ih (best.max (j - i)) k hk_tail hk_not
    · simp only [hle, ↓reduceIte] at hk_not ⊢
      exact False.elim (hk_not hk)

theorem popWhile_feasible (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat)
    (hj : j < nums.size)
    (hbounded : ∀ s ∈ st, s < nums.size)
    (hbest : best = 0 ∨ IsRampWidth nums best) :
    (popWhile nums j st best).2 = 0 ∨ IsRampWidth nums (popWhile nums j st best).2 := by
  induction st generalizing best with
  | nil =>
    unfold popWhile
    exact hbest
  | cons i rest ih =>
    unfold popWhile
    by_cases hle : nums[i]! ≤ nums[j]!
    · simp only [hle, ↓reduceIte]
      have hi_lt : i < nums.size := hbounded i (List.mem_cons.2 (Or.inl rfl))
      have hrest_bounded : ∀ s ∈ rest, s < nums.size := fun s hs => hbounded s (List.mem_cons.2 (Or.inr hs))
      have hbest1 : best.max (j - i) = 0 ∨ IsRampWidth nums (best.max (j - i)) := by
        by_cases hij : i < j
        · right
          by_cases hle_best : j - i ≤ best
          · have : best.max (j - i) = best := Nat.max_eq_left hle_best
            rw [this]
            cases hbest with
            | inl h0 => exfalso; omega
            | inr h_ramp => exact h_ramp
          · have hbest_le : best ≤ j - i := by omega
            have : best.max (j - i) = j - i := Nat.max_eq_right hbest_le
            rw [this]
            exact ⟨i, j, ⟨hij, hj, hle⟩, rfl⟩
        · have hji : j - i = 0 := by omega
          have : best.max (j - i) = best := by simp [hji]
          rw [this]
          exact hbest
      exact ih (best.max (j - i)) hrest_bounded hbest1
    · simp only [hle, ↓reduceIte]
      exact hbest

theorem scanInvariant_step (nums : Array Int) (st0 : List Nat) (j : Nat) (cur_st : List Nat) (best : Nat)
    (hinv : ScanInvariant nums st0 (j : Int) cur_st best)
    (hj : j < nums.size)
    (hbounded : ∀ s ∈ st0, s < nums.size) :
    ScanInvariant nums st0 ((j : Int) - 1) (popWhile nums j cur_st best).1 (popWhile nums j cur_st best).2 := by
  obtain ⟨hsorted, hsub, hbest, hgt, hpop, hramp⟩ := hinv
  have hsub_step := popWhile_subset nums j cur_st best
  have hsorted_step := popWhile_sorted nums j cur_st best hsorted
  have hbounded_cur : ∀ s ∈ cur_st, s < nums.size := fun s hs => hbounded s (hsub hs)
  have hbest_step := popWhile_feasible nums j cur_st best hj hbounded_cur hbest
  refine ⟨hsorted_step, fun x hx => hsub (hsub_step hx), hbest_step, ?_, ?_, ?_⟩
  · intro u hu v hv1 hv2
    have hv_cases : v = j ∨ (j : Int) < (v : Int) := by omega
    cases hv_cases with
    | inl heq =>
      subst v
      exact popWhile_keeps_greater nums j cur_st best hsorted u hu
    | inr hgt_v =>
      exact hgt u (hsub_step hu) v hgt_v hv2
  · intro k hk_st0 hk_not_step
    by_cases hk_cur : k ∈ cur_st
    · have h_popped := popWhile_popped_le nums j cur_st best k hk_cur hk_not_step
      refine ⟨j, by omega, hj, h_popped.1, h_popped.2⟩
    · obtain ⟨v, hv_gt, hv_sz, hle_v, hdiff_v⟩ := hpop k hk_st0 hk_cur
      have hbest_le := popWhile_best_ge nums j cur_st best
      refine ⟨v, by omega, hv_sz, hle_v, by omega⟩
  · intro k hk_st0 v hv1 hv2 h_isramp
    have hv_cases : v = j ∨ (j : Int) < (v : Int) := by omega
    cases hv_cases with
    | inl heq =>
      subst v
      by_cases hk_step : k ∈ (popWhile nums j cur_st best).1
      · have h_gt := popWhile_keeps_greater nums j cur_st best hsorted k hk_step
        have h_le := h_isramp.2.2
        omega
      · by_cases hk_cur : k ∈ cur_st
        · have h_popped := popWhile_popped_le nums j cur_st best k hk_cur hk_step
          exact h_popped.2
        · obtain ⟨v_prev, hv_prev_gt, _, _, hdiff_prev⟩ := hpop k hk_st0 hk_cur
          have hbest_le := popWhile_best_ge nums j cur_st best
          omega
    | inr hgt_v =>
      have hbound_prev := hramp k hk_st0 v hgt_v hv2 h_isramp
      have hbest_le := popWhile_best_ge nums j cur_st best
      omega

theorem exit_postcondition (nums : Array Int) (st0 cur_st : List Nat) (best : Nat)
    (hst_inv : StackInvariant nums nums.size st0)
    (hscan_inv : ScanInvariant nums st0 (-1) cur_st best) :
    postcondition nums best := by
  obtain ⟨hcovers, _⟩ := hst_inv
  obtain ⟨_, _, hbest, _, _, hramp⟩ := hscan_inv
  unfold postcondition
  refine ⟨hbest, ?_⟩
  intro w hw
  obtain ⟨i, j, ⟨hij1, hij2, hij3⟩, rfl⟩ := hw
  have hi_lt : i < nums.size := by omega
  obtain ⟨s, hs_st0, hsi, hs_val⟩ := hcovers i hi_lt
  have hs_ramp : IsRamp nums s j := by
    refine ⟨by omega, hij2, ?_⟩
    have : nums[s]! ≤ nums[i]! := hs_val
    have : nums[i]! ≤ nums[j]! := hij3
    omega
  have hj_bound : -1 < (j : Int) := by omega
  have hs_le := hramp s hs_st0 j hj_bound hij2 hs_ramp
  omega

prove_correct maximumWidthRamp by
  velvet_vcgen [maximumWidthRamp, precondition, postcondition] with try finish
  case max_ramp =>
    exact small_postcondition _ small
  case st_inv =>
    exact stackInvariant_init _
  case st_sorted =>
    exact stackSorted_init _
  case scan_inv =>
    exact scanInvariant_init _ _ st_sorted
  case max_ramp =>
    subst done_i
    have hdone_j : (j : Int) - 1 = -1 := by omega
    rw [hdone_j] at scan_inv
    exact exit_postcondition _ _ _ _ st_inv scan_inv
  case stack_size =>
    subst cur_st
    simp [CanPop] at popping
  case continuation =>
    subst cur_st
    unfold CanPop at popping
    simp only [decide_eq_true_eq] at popping
    exact (popWhile_cons_le _ _ _ _ _ popping).symm.trans continuation
  case popped =>
    cases cur_st with
    | nil =>
      simpa [popWhile] using continuation
    | cons left rest =>
      unfold CanPop at popping
      simp only [decide_eq_true_eq] at popping
      exact (popWhile_cons_not_le _ _ _ _ _ popping).symm.trans continuation
  case scan_inv =>
    have hj_lt : j - 1 < i := by omega
    subst done_i
    have hj_eq : (j : Int) - 1 = ((j - 1 : Nat) : Int) := by omega
    rw [hj_eq] at scan_inv
    have hstep := scanInvariant_step _ st (j - 1) _ _ scan_inv hj_lt st_inv.2
    have hst := congrArg Prod.fst popped
    have hbest := congrArg Prod.snd popped
    simp only at hst hbest
    rw [hst, hbest]
    exact hstep
  case st_inv =>
    exact buildStackStep_invariant _ _ _ st_inv
  case st_sorted =>
    exact buildStackStep_sorted _ _ _ st_inv st_sorted

end Proof

end MaximumWidthRamp
