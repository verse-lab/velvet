module

public import Velvet
public meta import Velvet
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.SplitIfs

/-!
## Program description

Given a fixed-length integer array `arr`, duplicate each occurrence of zero,
shifting the remaining elements to the right. Elements beyond the original length
of the array are truncated.

The program is expected to run in O(n) time and O(1) extra space, excluding the returned array.
-/

namespace DuplicateZeros

section Specs

public def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

public def precondition (_arr : Array Int) : Prop :=
  True

public def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))

end Specs

section Implementation

public def countZerosGo (arr : Array Int) (i : Nat) (zeros : Nat) : Nat :=
  if i < arr.size then
    countZerosGo arr (i + 1) (if arr[i]! = 0 then zeros + 1 else zeros)
  else
    zeros
termination_by arr.size - i

public def duplicateZerosStep (arr : Array Int) (limit : Nat) (i' : Nat) (j : Nat) (res : Array Int) : Nat × Array Int :=
  let x := arr[i']!
  let res1 := if j > 0 ∧ j - 1 < limit then res.set! (j - 1) x else res
  if x = 0 then
    let res2 := if j > 1 ∧ j - 2 < limit then res1.set! (j - 2) 0 else res1
    (j - 2, res2)
  else
    (j - 1, res1)

public def duplicateZerosGo (arr : Array Int) (limit : Nat) (i : Nat) (j : Nat) (res : Array Int) : Array Int :=
  match i with
  | 0 => res
  | i' + 1 =>
      let step := duplicateZerosStep arr limit i' j res
      duplicateZerosGo arr limit i' step.1 step.2

public def duplicateZerosFun (arr : Array Int) : Array Int :=
  let zeros := countZerosGo arr 0 0
  duplicateZerosGo arr arr.size arr.size (arr.size + zeros) arr

method duplicateZeros (arr : Array Int)
  returns (result : Array Int)
  requires valid: precondition arr
  ensures duplicated: postcondition arr result
do
  let n := arr.size
  let mut i : Nat := 0
  let mut zeros : Nat := 0
  while' counting: i < n
    invariant count_index: i ≤ n
    invariant count_continuation: countZerosGo arr i zeros = countZerosGo arr 0 0
    decreasing count_remaining: n - i
    done_with counted: i = n
  do
    if is_zero: arr[i]! = 0 then
      zeros := zeros + 1
    i := i + 1

  let mut j : Nat := n + zeros
  let mut idx : Nat := n
  let mut res : Array Int := arr
  while' writing: idx > 0
    invariant write_index: idx ≤ n
    invariant write_continuation: duplicateZerosGo arr n idx j res = duplicateZerosFun arr
    decreasing write_remaining: idx
    done_with written: idx = 0
  do
    let step := duplicateZerosStep arr n (idx - 1) j res
    j := step.1
    res := step.2
    idx := idx - 1
  return res

end Implementation

section Proof

theorem getElem!_set!_eq (a : Array Int) (i : Nat) (v : Int) (hi : i < a.size) :
    (a.set! i v)[i]! = v := by
  simp [Array.set!, Array.setIfInBounds, hi, getElem!_pos]

theorem getElem!_set!_ne_any (a : Array Int) (i j : Nat) (v : Int) (h : j ≠ i) :
    (a.set! i v)[j]! = a[j]! := by
  by_cases hj : j < a.size
  · by_cases hi : i < a.size
    · rw [getElem!_pos _ _ (by simpa [Array.size_set!])]
      rw [getElem!_pos a j hj]
      simp only [Array.set!, Array.setIfInBounds, dite_eq_left hi]
      exact Array.getElem_set_ne hi hj (fun heq => h heq.symm)
    · simp [Array.set!, Array.setIfInBounds, hi]
  · rw [getElem!_neg (a.set! i v) j (by simp; omega)]
    rw [getElem!_neg a j (by omega)]

lemma producedLen_zero (arr : Array Int) : producedLen arr 0 = 0 := by
  simp [producedLen]

lemma producedLen_succ (arr : Array Int) (i : Nat) (h : i < arr.size) :
    producedLen arr (i + 1) = producedLen arr i + if arr[i]! = 0 then 2 else 1 := by
  have hextract : arr.extract 0 (i + 1) = arr.extract 0 i ++ #[arr[i]!] := by
    apply Array.ext
    · simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size),
        Nat.min_eq_left (by omega : i ≤ arr.size)]
    · intro j hj1 hj2
      simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size)] at hj1
      by_cases hji : j < i
      · rw [Array.getElem_append_left (by simpa [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)])]
        simp [Array.getElem_extract]
      · have hj_eq : j = i := by omega
        subst j
        have hlen : (arr.extract 0 i).size = i := by
          simp [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)]
        rw [Array.getElem_append_right (by rw [hlen]; omega)]
        simp [hlen, getElem!_pos arr i h]
  unfold producedLen
  change (arr.extract 0 (i + 1)).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0 =
    (arr.extract 0 i).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0 + (if arr[i]! = 0 then 2 else 1)
  rw [hextract, Array.foldl_append]
  simp
  split_ifs <;> rfl

lemma producedLen_mono (arr : Array Int) (i k : Nat) (h : i ≤ k) :
    producedLen arr i ≤ producedLen arr k := by
  have h_le : ∀ d, producedLen arr i ≤ producedLen arr (i + d) := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      have h_step : producedLen arr (i + d) ≤ producedLen arr (i + d + 1) := by
        by_cases hk' : i + d < arr.size
        · rw [producedLen_succ arr (i + d) hk']
          split_ifs <;> omega
        · have h_take : arr.take (i + d + 1) = arr.take (i + d) := by
            unfold Array.take
            apply Array.ext
            · simp [Array.size_extract, Nat.min_eq_right (by omega : arr.size ≤ i + d + 1),
                Nat.min_eq_right (by omega : arr.size ≤ i + d)]
            · intro j hj1 hj2
              simp [Array.getElem_extract]
          unfold producedLen
          rw [h_take]
          exact Nat.le_refl _
      exact Nat.le_trans ih h_step
  have heq : k = i + (k - i) := by omega
  have hle := h_le (k - i)
  rw [← heq] at hle
  exact hle

lemma duplicateZerosGo_preserves (arr : Array Int) (limit : Nat) (i : Nat) (j : Nat) (res : Array Int) (k : Nat) (hk : k ≥ j) :
    (duplicateZerosGo arr limit i j res)[k]! = res[k]! := by
  induction i generalizing j res with
  | zero => rfl
  | succ i ih =>
    rw [duplicateZerosGo]
    by_cases hx : arr[i]! = 0
    · simp only [duplicateZerosStep, hx, ite_true]
      rw [ih _ _ (by omega)]
      split_ifs with h1 h2
      · rw [getElem!_set!_ne_any _ _ _ _ (by omega), getElem!_set!_ne_any _ _ _ _ (by omega)]
      · rw [getElem!_set!_ne_any _ _ _ _ (by omega)]
      · rw [getElem!_set!_ne_any _ _ _ _ (by omega)]
      · rfl
    · simp only [duplicateZerosStep, hx, ite_false]
      rw [ih _ _ (by omega)]
      split_ifs with h1
      · rw [getElem!_set!_ne_any _ _ _ _ (by omega)]
      · rfl

lemma duplicateZerosGo_size (arr : Array Int) (limit : Nat) (i : Nat) (j : Nat) (res : Array Int) :
    (duplicateZerosGo arr limit i j res).size = res.size := by
  induction i generalizing j res with
  | zero => rfl
  | succ i ih =>
    rw [duplicateZerosGo]
    rw [ih]
    simp only [duplicateZerosStep]
    split_ifs <;> simp

lemma duplicateZerosGo_succ_zero (arr : Array Int) (limit : Nat) (i : Nat) (res : Array Int) (hx : arr[i]! = 0) (hi : i < arr.size) :
    duplicateZerosGo arr limit (i + 1) (producedLen arr (i + 1)) res =
      let res1 := if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res
      let res2 := if producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit then res1.set! (producedLen arr (i + 1) - 2) 0 else res1
      duplicateZerosGo arr limit i (producedLen arr i) res2 := by
  have hsucc := producedLen_succ arr i hi
  simp only [hx, ite_true] at hsucc
  rw [duplicateZerosGo]
  dsimp only [duplicateZerosStep]
  rw [hx]
  simp only [ite_true]
  have hj : producedLen arr (i + 1) - 2 = producedLen arr i := by omega
  rw [hj]

lemma duplicateZerosGo_succ_nonzero (arr : Array Int) (limit : Nat) (i : Nat) (res : Array Int) (hx : ¬arr[i]! = 0) (hi : i < arr.size) :
    duplicateZerosGo arr limit (i + 1) (producedLen arr (i + 1)) res =
      let res1 := if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) arr[i]! else res
      duplicateZerosGo arr limit i (producedLen arr i) res1 := by
  have hsucc := producedLen_succ arr i hi
  simp only [hx, ite_false] at hsucc
  rw [duplicateZerosGo]
  dsimp only [duplicateZerosStep]
  simp only [hx, ite_false]
  have hj : producedLen arr (i + 1) - 1 = producedLen arr i := by omega
  rw [hj]

theorem duplicateZerosGo_correct_lt (arr : Array Int) (limit : Nat) (i : Nat) (hi : i ≤ arr.size)
    (res : Array Int) (h_res_size : res.size = limit) (k : Nat) (hk_lim : k < limit) (hk_j : k < producedLen arr i) :
    ∃ i_k, i_k < i ∧ producedLen arr i_k ≤ k ∧ k < producedLen arr (i_k + 1) ∧
      (duplicateZerosGo arr limit i (producedLen arr i) res)[k]! = (if arr[i_k]! = 0 then 0 else arr[i_k]!) := by
  induction i generalizing res with
  | zero =>
    rw [producedLen_zero] at hk_j
    omega
  | succ i ih =>
    have hi_le : i ≤ arr.size := by omega
    have hi_lt : i < arr.size := by omega
    have hsucc := producedLen_succ arr i hi_lt
    by_cases hx : arr[i]! = 0
    · simp only [hx, ite_true] at hsucc
      have hj_eq : producedLen arr (i + 1) = producedLen arr i + 2 := hsucc
      have hstep := duplicateZerosGo_succ_zero arr limit i res hx hi_lt
      rw [hstep]
      by_cases hk_lt_i : k < producedLen arr i
      · have h_sz : (if producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit then (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).set! (producedLen arr (i + 1) - 2) 0 else if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).size = limit := by
          split_ifs <;> simp [h_res_size]
        obtain ⟨i_k, hi_k1, hi_k2, hi_k3, hi_k4⟩ := ih hi_le _ h_sz hk_lt_i
        exact ⟨i_k, by omega, hi_k2, hi_k3, hi_k4⟩
      · have hk_cases : k = producedLen arr i ∨ k = producedLen arr i + 1 := by omega
        refine ⟨i, by omega, by omega, by rw [hj_eq]; omega, ?_⟩
        rw [duplicateZerosGo_preserves arr limit i (producedLen arr i) _ k (by omega)]
        cases hk_cases with
        | inl hk0 =>
          subst k
          have hj_sub2 : producedLen arr (i + 1) - 2 = producedLen arr i := by omega
          by_cases hc2 : producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit
          · have h_if2 : (if producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit then (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).set! (producedLen arr (i + 1) - 2) 0 else if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res) =
              (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).set! (producedLen arr (i + 1) - 2) 0 := by
              split_ifs <;> rfl
            rw [h_if2, hj_sub2]
            have h_sz' : (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).size = limit := by
              split_ifs <;> simp [h_res_size]
            rw [getElem!_set!_eq _ _ _ (by rw [h_sz']; omega)]
            simp [hx]
          · omega
        | inr hk1 =>
          subst k
          have hj_sub1 : producedLen arr (i + 1) - 1 = producedLen arr i + 1 := by omega
          have hne : producedLen arr i + 1 ≠ producedLen arr (i + 1) - 2 := by omega
          by_cases hc2 : producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit
          · have h_if2 : (if producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit then (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).set! (producedLen arr (i + 1) - 2) 0 else if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res) =
              (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).set! (producedLen arr (i + 1) - 2) 0 := by
              split_ifs <;> rfl
            rw [h_if2]
            rw [getElem!_set!_ne_any _ _ _ _ hne]
            by_cases hc1 : producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit
            · have h_if1 : (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res) =
                res.set! (producedLen arr (i + 1) - 1) 0 := by
                split_ifs <;> rfl
              rw [h_if1, hj_sub1]
              rw [getElem!_set!_eq _ _ _ (by simp [h_res_size]; omega)]
              simp [hx]
            · omega
          · have h_if2 : (if producedLen arr (i + 1) > 1 ∧ producedLen arr (i + 1) - 2 < limit then (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res).set! (producedLen arr (i + 1) - 2) 0 else if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res) =
              if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res := by
              split_ifs <;> rfl
            rw [h_if2]
            by_cases hc1 : producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit
            · have h_if1 : (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) 0 else res) =
                res.set! (producedLen arr (i + 1) - 1) 0 := by
                split_ifs <;> rfl
              rw [h_if1, hj_sub1]
              rw [getElem!_set!_eq _ _ _ (by simp [h_res_size]; omega)]
              simp [hx]
            · omega
    · simp only [hx, ite_false] at hsucc
      have hj_eq : producedLen arr (i + 1) = producedLen arr i + 1 := hsucc
      have hstep := duplicateZerosGo_succ_nonzero arr limit i res hx hi_lt
      rw [hstep]
      by_cases hk_lt_i : k < producedLen arr i
      · have h_sz : (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) arr[i]! else res).size = limit := by
          split_ifs <;> simp [h_res_size]
        obtain ⟨i_k, hi_k1, hi_k2, hi_k3, hi_k4⟩ := ih hi_le _ h_sz hk_lt_i
        exact ⟨i_k, by omega, hi_k2, hi_k3, hi_k4⟩
      · have hk_eq : k = producedLen arr i := by omega
        subst k
        refine ⟨i, by omega, by omega, by rw [hj_eq]; omega, ?_⟩
        rw [duplicateZerosGo_preserves arr limit i (producedLen arr i) _ (producedLen arr i) (by omega)]
        by_cases hc1 : producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit
        · have h_if1 : (if producedLen arr (i + 1) > 0 ∧ producedLen arr (i + 1) - 1 < limit then res.set! (producedLen arr (i + 1) - 1) arr[i]! else res) =
            res.set! (producedLen arr (i + 1) - 1) arr[i]! := by
            split_ifs <;> rfl
          rw [h_if1]
          have hj_sub1 : producedLen arr (i + 1) - 1 = producedLen arr i := by omega
          rw [hj_sub1]
          rw [getElem!_set!_eq _ _ _ (by simp [h_res_size]; omega)]
          simp [hx]
        · omega

theorem countZerosGo_add (arr : Array Int) (i : Nat) (zeros : Nat) :
    countZerosGo arr i zeros = zeros + countZerosGo arr i 0 := by
  have h : ∀ k i zeros, arr.size - i ≤ k → countZerosGo arr i zeros = zeros + countZerosGo arr i 0 := by
    intro k
    induction k with
    | zero =>
      intro i zeros hi
      have hnot : ¬(i < arr.size) := by omega
      rw [countZerosGo.eq_def (i := i), countZerosGo.eq_def (i := i)]
      simp [hnot]
    | succ k ih =>
      intro i zeros hi
      rw [countZerosGo.eq_def (i := i), countZerosGo.eq_def (i := i)]
      by_cases hlt : i < arr.size
      · simp only [hlt, ite_true]
        by_cases hz : arr[i]! = 0
        · simp only [hz, ite_true]
          have h1 := ih (i + 1) (zeros + 1) (by omega)
          have h2 := ih (i + 1) (0 + 1) (by omega)
          rw [h1, h2]
          omega
        · simp only [hz, ite_false]
          have h1 := ih (i + 1) zeros (by omega)
          rw [h1]
      · simp only [hlt, ite_false]
        omega
  exact h (arr.size - i) i zeros (by omega)

theorem producedLen_eq_count (arr : Array Int) (i : Nat) (hi : i ≤ arr.size) :
    producedLen arr i = i + (arr.take i).foldl (fun acc x => if x = 0 then acc + 1 else acc) 0 := by
  induction i with
  | zero => simp [producedLen]
  | succ i ih =>
    have hi_lt : i < arr.size := by omega
    rw [producedLen_succ arr i hi_lt, ih (by omega)]
    have hextract : arr.take (i + 1) = arr.take i ++ #[arr[i]!] := by
      unfold Array.take
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size),
          Nat.min_eq_left (by omega : i ≤ arr.size)]
      · intro j hj1 hj2
        simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size)] at hj1
        by_cases hji : j < i
        · rw [Array.getElem_append_left (by simpa [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)])]
          simp [Array.getElem_extract]
        · have hj_eq : j = i := by omega
          subst j
          have hlen : (arr.extract 0 i).size = i := by
            simp [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)]
          rw [Array.getElem_append_right (by rw [hlen]; omega)]
          simp [hlen, getElem!_pos arr i hi_lt]
    rw [hextract, Array.foldl_append]
    simp
    by_cases hz : arr[i]! = 0 <;> simp [hz] <;> omega

theorem countZerosGo_eq_foldl (arr : Array Int) (i : Nat) (hi : i ≤ arr.size) :
    countZerosGo arr 0 0 = (arr.take i).foldl (fun acc x => if x = 0 then acc + 1 else acc) 0 + countZerosGo arr i 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi_lt : i < arr.size := by omega
    rw [ih (by omega)]
    rw [countZerosGo.eq_def (i := i)]
    simp only [hi_lt, ite_true]
    have hextract : arr.take (i + 1) = arr.take i ++ #[arr[i]!] := by
      unfold Array.take
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size),
          Nat.min_eq_left (by omega : i ≤ arr.size)]
      · intro j hj1 hj2
        simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size)] at hj1
        by_cases hji : j < i
        · rw [Array.getElem_append_left (by simpa [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)])]
          simp [Array.getElem_extract]
        · have hj_eq : j = i := by omega
          subst j
          have hlen : (arr.extract 0 i).size = i := by
            simp [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)]
          rw [Array.getElem_append_right (by rw [hlen]; omega)]
          simp [hlen, getElem!_pos arr i hi_lt]
    rw [hextract, Array.foldl_append]
    simp
    by_cases hz : arr[i]! = 0
    · simp only [hz, ite_true]
      rw [countZerosGo_add arr (i + 1) 1]
      omega
    · simp only [hz, ite_false]

theorem producedLen_size_eq (arr : Array Int) :
    producedLen arr arr.size = arr.size + countZerosGo arr 0 0 := by
  have hpl := producedLen_eq_count arr arr.size (by omega)
  have hcz := countZerosGo_eq_foldl arr arr.size (by omega)
  have hend : countZerosGo arr arr.size 0 = 0 := by
    rw [countZerosGo.eq_def]
    simp
  rw [hend] at hcz
  omega

theorem duplicateZerosFun_correct (arr : Array Int) :
    postcondition arr (duplicateZerosFun arr) := by
  have hsz : (duplicateZerosFun arr).size = arr.size := by
    unfold duplicateZerosFun
    rw [duplicateZerosGo_size]
  refine ⟨hsz, ?_⟩
  intro j hj
  have hlen_ge : j < producedLen arr arr.size := by
    rw [producedLen_size_eq]
    omega
  have hpl := duplicateZerosGo_correct_lt arr arr.size arr.size (by omega) arr rfl j hj hlen_ge
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hpl
  have h_unique : ∀ (y : Nat), (y < arr.size ∧ producedLen arr y ≤ j ∧ j < producedLen arr (y + 1) ∧
      (duplicateZerosFun arr)[j]! = (if arr[y]! = 0 then 0 else arr[y]!)) → y = i := by
    intro y hy
    by_cases hlt : y < i
    · have hmono := producedLen_mono arr (y + 1) i (by omega)
      have hy3 := hy.2.2.1
      omega
    · by_cases hgt : i < y
      · have hmono := producedLen_mono arr (i + 1) y (by omega)
        have hy2 := hy.2.1
        omega
      · omega
  have h_final : (duplicateZerosFun arr)[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
    change (duplicateZerosGo arr arr.size arr.size (arr.size + countZerosGo arr 0 0) arr)[j]! = _
    have heq : arr.size + countZerosGo arr 0 0 = producedLen arr arr.size := (producedLen_size_eq arr).symm
    rw [heq]
    exact hi4
  refine ⟨i, ⟨hi1, hi2, hi3, h_final⟩, h_unique⟩

prove_correct duplicateZeros by
  velvet_vcgen [duplicateZeros, postcondition] with try finish
  case write_continuation =>
    rename_i arr
    unfold duplicateZerosFun
    rw [countZerosGo.eq_def (i := i)] at count_continuation
    simp [counted] at count_continuation
    rw [count_continuation]
  case duplicated =>
    rename_i arr
    rw [duplicateZerosGo.eq_def] at write_continuation
    simp [written] at write_continuation
    rw [write_continuation]
    exact duplicateZerosFun_correct arr
  case write_continuation =>
    rename_i arr
    have hidx : idx = (idx - 1) + 1 := by omega
    have hstep : duplicateZerosGo arr arr.size idx j res =
        duplicateZerosGo arr arr.size (idx - 1)
          (duplicateZerosStep arr arr.size (idx - 1) j res).1
          (duplicateZerosStep arr arr.size (idx - 1) j res).2 := by
      conv =>
        lhs
        rw [hidx]
      rfl
    rw [hstep] at write_continuation
    exact write_continuation
  case count_continuation =>
    rw [countZerosGo.eq_def (i := i)] at count_continuation
    simp only [counting, ite_true, is_zero] at count_continuation
    exact count_continuation
  case count_continuation =>
    rw [countZerosGo.eq_def (i := i)] at count_continuation
    simp only [counting, ite_true, is_zero, ite_false] at count_continuation
    exact count_continuation


end Proof

end DuplicateZeros


