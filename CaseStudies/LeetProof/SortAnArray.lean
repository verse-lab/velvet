module

public import Velvet
public meta import Velvet
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Perm.Basic
import Batteries.Data.Array.Lemmas

/-!
## Program description

Given an array of integers `nums`, sort the array in ascending order and return
it.

The program is expected to run in O(n + k) time and O(k) extra space, where
`k = 100001` is the size of the value range `[-50000, 50000]`.
-/

namespace SortAnArray

section Specs

public def minVal : Int := -50000

public def maxVal : Int := 50000

public def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

public def allInRange (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → minVal ≤ arr[i]! ∧ arr[i]! ≤ maxVal

public def precondition (nums : Array Int) : Prop :=
  allInRange nums

public def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  isSortedNondecreasing result ∧
  allInRange result ∧
  (∀ (v : Int), result.count v = nums.count v)

end Specs

section Implementation

public def rangeSize : Nat := 100001

public def idxOf (v : Int) : Nat := (v - minVal).toNat

public def countStep (counts : Array Nat) (x : Int) : Array Nat :=
  let idx : Nat := idxOf x
  counts.set! idx (counts[idx]! + 1)

public def countGo (nums : Array Int) (i : Nat) (counts : Array Nat) : Array Nat :=
  if i < nums.size then
    countGo nums (i + 1) (countStep counts nums[i]!)
  else counts
termination_by nums.size - i

public def pushMany (v : Int) (n : Nat) (acc : Array Int) : Array Int :=
  match n with
  | 0 => acc
  | n + 1 => pushMany v n (acc.push v)

public def emitGo (counts : Array Nat) (cIdx : Nat) (acc : Array Int) : Array Int :=
  if cIdx < rangeSize then
    let v : Int := minVal + (cIdx : Int)
    emitGo counts (cIdx + 1) (pushMany v counts[cIdx]! acc)
  else acc
termination_by rangeSize - cIdx

public def countSort (nums : Array Int) : Array Int :=
  let counts := countGo nums 0 (Array.replicate rangeSize 0)
  emitGo counts 0 #[]

method sortArray (nums : Array Int)
  returns (result : Array Int)
  requires valid: precondition nums
  ensures sorted: postcondition nums result
do
  let mut counts : Array Nat := Array.replicate rangeSize 0
  let mut i : Nat := 0
  while counting: i < nums.size
    invariant count_bounds: i ≤ nums.size
    invariant count_continuation:
      countGo nums i counts = countGo nums 0 (Array.replicate rangeSize 0)
    decreasing count_remaining: nums.size - i
    done_with counted: i = nums.size
  do
    let v : Int := nums[i]!
    let idx : Nat := (v - minVal).toNat
    counts := counts.set! idx (counts[idx]! + 1)
    i := i + 1
  let mut out : Array Int := #[]
  let mut cIdx : Nat := 0
  while emitting: cIdx < rangeSize
    invariant emit_bounds: cIdx ≤ rangeSize
    invariant emit_continuation:
      emitGo counts cIdx out = emitGo counts 0 #[]
    decreasing emit_remaining: rangeSize - cIdx
    done_with emitted: cIdx = rangeSize
  do
    let mut remaining : Nat := counts[cIdx]!
    let v : Int := minVal + (cIdx : Int)
    let mut cur : Array Int := out
    while pushing: remaining > 0
      invariant push_continuation:
        pushMany v remaining cur = pushMany v counts[cIdx]! out
      decreasing push_remaining: remaining
      done_with pushed: remaining = 0
    do
      cur := cur.push v
      remaining := remaining - 1
    out := cur
    cIdx := cIdx + 1
  return out

end Implementation

section Proof

lemma idxOf_lt (v : Int) (h1 : minVal ≤ v) (h2 : v ≤ maxVal) : idxOf v < rangeSize := by
  unfold idxOf rangeSize minVal maxVal at *
  omega

lemma idxOf_inj (u v : Int) (hu1 : minVal ≤ u) (hu2 : u ≤ maxVal)
    (hv1 : minVal ≤ v) (hv2 : v ≤ maxVal) (h : idxOf u = idxOf v) : u = v := by
  unfold idxOf minVal maxVal at *
  omega

lemma countStep_size (counts : Array Nat) (x : Int) :
    (countStep counts x).size = counts.size := by
  simp [countStep]

lemma countGo_size (nums : Array Int) (i : Nat) (counts : Array Nat) :
    (countGo nums i counts).size = counts.size := by
  fun_induction countGo nums i counts
  case case1 i c hi ih =>
    rw [ih, countStep_size]
  case case2 i c hi =>
    rfl

theorem drop_succ_getElem! (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    nums.toList.drop i = nums[i]! :: nums.toList.drop (i + 1) := by
  have hlen : i < nums.toList.length := by simpa using hi
  have hd := List.drop_eq_getElem_cons (l := nums.toList) (i := i) hlen
  have hget : nums.toList[i] = nums[i]! := by
    rw [getElem!_pos nums i hi]
    rfl
  rw [← hget]
  exact hd

lemma countGo_getElem! (nums : Array Int) (i : Nat) (counts : Array Nat)
    (hsz : counts.size = rangeSize) (hpre : precondition nums)
    (v : Int) (hvLo : minVal ≤ v) (hvHi : v ≤ maxVal) :
    (countGo nums i counts)[idxOf v]! = counts[idxOf v]! + (nums.toList.drop i).count v := by
  fun_induction countGo nums i counts
  case case1 i c hi ih =>
    have hx_range : minVal ≤ nums[i]! ∧ nums[i]! ≤ maxVal := hpre i hi
    have hx_lt : idxOf nums[i]! < c.size := by
      rw [hsz]
      exact idxOf_lt nums[i]! hx_range.1 hx_range.2
    have hv_lt : idxOf v < c.size := by
      rw [hsz]
      exact idxOf_lt v hvLo hvHi
    have hstep_sz : (countStep c nums[i]!).size = rangeSize := by
      rw [countStep_size, hsz]
    rw [ih hstep_sz]
    have hdrop := drop_succ_getElem! nums i hi
    rw [hdrop, List.count_cons]
    unfold countStep
    by_cases heq : nums[i]! = v
    · have h_idx_eq : idxOf nums[i]! = idxOf v := by rw [heq]
      rw [h_idx_eq]
      rw [Array.getElem!_set!_self c (idxOf v) (c[idxOf v]! + 1) hv_lt]
      simp [heq]
      omega
    · have h_idx_ne : idxOf nums[i]! ≠ idxOf v := by
        intro h
        exact heq (idxOf_inj nums[i]! v hx_range.1 hx_range.2 hvLo hvHi h)
      rw [Array.getElem!_set!_ne c (idxOf nums[i]!) (idxOf v) (c[idxOf nums[i]!]! + 1) h_idx_ne]
      simp [heq]
  case case2 i c hi =>
    have hlen : nums.toList.length ≤ i := by simpa using (Nat.le_of_not_gt hi)
    simp [List.drop_eq_nil_iff.mpr hlen]

lemma count_eq_zero_of_not_in_range (nums : Array Int) (hpre : precondition nums)
    (v : Int) (hv : v < minVal ∨ maxVal < v) : nums.count v = 0 := by
  rw [Array.count_eq_zero]
  intro hmem
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hmem
  have hrange := hpre i hi
  rw [getElem!_pos nums i hi] at hrange
  rcases hv with hlt | hgt
  · unfold minVal at *; omega
  · unfold maxVal at *; omega

@[simp] lemma pushMany_zero (v : Int) (acc : Array Int) :
    pushMany v 0 acc = acc := rfl

@[simp] lemma pushMany_succ (v : Int) (n : Nat) (acc : Array Int) :
    pushMany v (n + 1) acc = pushMany v n (acc.push v) := rfl

lemma pushMany_toList (v : Int) (n : Nat) (acc : Array Int) :
    (pushMany v n acc).toList = acc.toList ++ List.replicate n v := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    simp [ih (acc.push v), List.replicate_succ]

public def emitList (counts : Array Nat) (cIdx : Nat) : List Int :=
  if cIdx < rangeSize then
    List.replicate counts[cIdx]! (minVal + (cIdx : Int)) ++ emitList counts (cIdx + 1)
  else []
termination_by rangeSize - cIdx

lemma emitList_ind {P : Nat → Prop} (h_base : ∀ cIdx, ¬ cIdx < rangeSize → P cIdx)
    (h_step : ∀ cIdx, cIdx < rangeSize → P (cIdx + 1) → P cIdx) (cIdx : Nat) : P cIdx := by
  have : ∀ n cIdx, rangeSize - cIdx ≤ n → P cIdx := by
    intro n; induction n with
    | zero =>
      intro cIdx hle
      apply h_base
      unfold rangeSize at *; omega
    | succ n ih =>
      intro cIdx hle
      by_cases hscan : cIdx < rangeSize
      · apply h_step cIdx hscan (ih (cIdx + 1) (by unfold rangeSize at *; omega))
      · exact h_base cIdx hscan
  exact this (rangeSize - cIdx) cIdx (by unfold rangeSize at *; omega)

lemma emitGo_toList (counts : Array Nat) (cIdx : Nat) (acc : Array Int) :
    (emitGo counts cIdx acc).toList = acc.toList ++ emitList counts cIdx := by
  induction cIdx using emitList_ind generalizing acc with
  | h_base cIdx hscan =>
    rw [emitGo.eq_def, emitList.eq_def]
    simp [hscan]
  | h_step cIdx hscan ih =>
    rw [emitGo.eq_def]
    simp only [hscan, ↓reduceIte]
    rw [ih (pushMany (minVal + (cIdx : Int)) counts[cIdx]! acc), pushMany_toList]
    rw [emitList.eq_def (cIdx := cIdx)]
    simp only [hscan, ↓reduceIte]
    simp [List.append_assoc]

lemma emitList_count_outside_gt (counts : Array Nat) (w : Int) (hw_hi : maxVal < w) (cIdx : Nat) :
    (emitList counts cIdx).count w = 0 := by
  induction cIdx using emitList_ind with
  | h_base cIdx hscan =>
    rw [emitList.eq_def]
    simp [hscan]
  | h_step cIdx hscan ih =>
    rw [emitList.eq_def]
    simp only [hscan, ↓reduceIte, List.count_append]
    have hne : minVal + (cIdx : Int) ≠ w := by
      unfold minVal maxVal rangeSize at *
      omega
    have hrep : (List.replicate counts[cIdx]! (minVal + (cIdx : Int))).count w = 0 := by
      rw [List.count_replicate]
      split_ifs with h
      · exfalso; apply hne; rw [beq_iff_eq] at h; exact h
      · rfl
    rw [hrep, ih, Nat.zero_add]

lemma emitList_count_outside_lt (counts : Array Nat) (w : Int) (cIdx : Nat)
    (hw_lt : w < minVal + (cIdx : Int)) :
    (emitList counts cIdx).count w = 0 := by
  induction cIdx using emitList_ind with
  | h_base cIdx hscan =>
    rw [emitList.eq_def]
    simp [hscan]
  | h_step cIdx hscan ih =>
    rw [emitList.eq_def]
    simp only [hscan, ↓reduceIte, List.count_append]
    have hne : minVal + (cIdx : Int) ≠ w := by
      unfold minVal at *; omega
    have hrep : (List.replicate counts[cIdx]! (minVal + (cIdx : Int))).count w = 0 := by
      rw [List.count_replicate]
      split_ifs with h
      · exfalso; apply hne; rw [beq_iff_eq] at h; exact h
      · rfl
    have hw_next : w < minVal + ((cIdx + 1 : Nat) : Int) := by
      unfold minVal at *; omega
    have hrest : (emitList counts (cIdx + 1)).count w = 0 := ih hw_next
    rw [hrep, hrest, Nat.zero_add]

lemma emitList_count_inside (counts : Array Nat) (w : Int) (hwHi : w ≤ maxVal) (cIdx : Nat)
    (hwLo : minVal + (cIdx : Int) ≤ w) :
    (emitList counts cIdx).count w = counts[idxOf w]! := by
  induction cIdx using emitList_ind with
  | h_base cIdx hscan =>
    have : False := by
      unfold minVal maxVal rangeSize at *
      omega
    contradiction
  | h_step cIdx hscan ih =>
    rw [emitList.eq_def]
    simp only [hscan, ↓reduceIte, List.count_append]
    have hj_val : w = minVal + ((idxOf w : Nat) : Int) := by
      unfold idxOf minVal maxVal at *
      omega
    by_cases heq : cIdx = idxOf w
    · subst heq
      have heq' : minVal + ((idxOf w : Nat) : Int) = w := hj_val.symm
      have hrep : (List.replicate counts[idxOf w]! (minVal + ((idxOf w : Nat) : Int))).count w = counts[idxOf w]! := by
        rw [List.count_replicate]
        split_ifs with h
        · rfl
        · exfalso; apply h; rw [beq_iff_eq]; exact heq'
      have hw_out : w < minVal + (((idxOf w + 1) : Nat) : Int) := by
        unfold idxOf minVal maxVal at *
        omega
      have hrest : (emitList counts (idxOf w + 1)).count w = 0 :=
        emitList_count_outside_lt counts w (idxOf w + 1) hw_out
      rw [hrep, hrest, Nat.add_zero]
    · have hne : minVal + (cIdx : Int) ≠ w := by
        intro h
        have : cIdx = idxOf w := by
          unfold idxOf minVal maxVal at *
          omega
        exact heq this
      have hrep : (List.replicate counts[cIdx]! (minVal + (cIdx : Int))).count w = 0 := by
        rw [List.count_replicate]
        split_ifs with h
        · exfalso; apply hne; rw [beq_iff_eq] at h; exact h
        · rfl
      have hw_next_le : minVal + (((cIdx + 1) : Nat) : Int) ≤ w := by
        have : cIdx < idxOf w := by
          unfold idxOf minVal maxVal at *
          omega
        unfold minVal maxVal at *
        omega
      have hrest : (emitList counts (cIdx + 1)).count w = counts[idxOf w]! :=
        ih hw_next_le
      rw [hrep, hrest, Nat.zero_add]

lemma emitList_mem_range (counts : Array Nat) (cIdx : Nat) (x : Int)
    (hx : x ∈ emitList counts cIdx) :
    minVal ≤ x ∧ x ≤ maxVal := by
  induction cIdx using emitList_ind with
  | h_base cIdx hscan =>
    rw [emitList.eq_def] at hx
    simp [hscan] at hx
  | h_step cIdx hscan ih =>
    rw [emitList.eq_def] at hx
    simp only [hscan, ↓reduceIte, List.mem_append] at hx
    rcases hx with hrep | hrest
    · have hx_eq := List.eq_of_mem_replicate hrep
      subst hx_eq
      unfold minVal maxVal rangeSize at *
      omega
    · exact ih hrest

lemma emitList_pairwise_and_ge (counts : Array Nat) (cIdx : Nat) :
    (emitList counts cIdx).Pairwise (· ≤ ·) ∧
    (∀ x ∈ emitList counts cIdx, minVal + (cIdx : Int) ≤ x) := by
  induction cIdx using emitList_ind with
  | h_base cIdx hscan =>
    rw [emitList.eq_def]
    simp only [hscan, ↓reduceIte]
    refine ⟨List.Pairwise.nil, by simp⟩
  | h_step cIdx hscan ih =>
    rw [emitList.eq_def]
    simp only [hscan, ↓reduceIte]
    have hrep_pw : (List.replicate counts[cIdx]! (minVal + (cIdx : Int))).Pairwise (· ≤ ·) := by
      apply List.pairwise_replicate.mpr
      omega
    have hcross : ∀ a ∈ List.replicate counts[cIdx]! (minVal + (cIdx : Int)),
                  ∀ b ∈ emitList counts (cIdx + 1), a ≤ b := by
      intro a ha b hb
      have ha_eq := List.eq_of_mem_replicate ha
      have hb_ge := ih.2 b hb
      rw [ha_eq]
      unfold minVal at *
      omega
    have hpw : ((List.replicate counts[cIdx]! (minVal + (cIdx : Int))) ++ emitList counts (cIdx + 1)).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      exact ⟨hrep_pw, ih.1, hcross⟩
    refine ⟨hpw, ?_⟩
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with h1 | h2
    · have := List.eq_of_mem_replicate h1
      subst this
      omega
    · have := ih.2 x h2
      unfold minVal at *
      omega

lemma list_foldr_count (l : List Int) (v : Int) :
    List.foldr (fun a acc => if a = v then acc + 1 else acc) 0 l = List.count v l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [List.count_cons]
    by_cases hav : a = v <;> simp [hav, ih]

lemma toArray_count (l : List Int) (v : Int) : l.toArray.count v = l.count v := by
  simp only [Array.count, Array.countP]
  have h_foldr : Array.foldr (fun a acc => bif a == v then acc + 1 else acc) 0 l.toArray =
      List.foldr (fun a acc => if a = v then acc + 1 else acc) 0 l := by
    simp [Array.foldr]
  rw [h_foldr, list_foldr_count]

lemma array_count (a : Array Int) (v : Int) : a.count v = a.toList.count v := by
  have h : a = a.toList.toArray := by simp
  rw [h, toArray_count]

lemma emitGo_zero_toList (counts : Array Nat) :
    (emitGo counts 0 #[]).toList = emitList counts 0 := by
  rw [emitGo_toList]
  exact List.nil_append _

lemma emitGo_zero_size (counts : Array Nat) :
    (emitGo counts 0 #[]).size = (emitList counts 0).length := by
  rw [Array.size_eq_length_toList, emitGo_zero_toList]

lemma emitGo_zero_getElem! (counts : Array Nat) (k : Nat)
    (hk : k < (emitGo counts 0 #[]).size) :
    (emitGo counts 0 #[])[k]! = (emitList counts 0)[k]'(by
      have hsz := emitGo_zero_size counts
      rw [← hsz]
      exact hk) := by
  have hk_len1 : k < (emitGo counts 0 #[]).toList.length := by
    rw [← Array.size_eq_length_toList]
    exact hk
  have hk_len2 : k < (emitList counts 0).length := by
    have hsz := emitGo_zero_size counts
    rw [← hsz]
    exact hk
  have h1 : (emitGo counts 0 #[])[k]! = (emitGo counts 0 #[]).toList[k]! := by
    rw [getElem!_pos (emitGo counts 0 #[]) k hk]
    rw [getElem!_pos (emitGo counts 0 #[]).toList k hk_len1]
    rfl
  have h2 : (emitGo counts 0 #[]).toList[k]! = (emitList counts 0)[k]! :=
    congrArg (·[k]!) (emitGo_zero_toList counts)
  have h3 : (emitList counts 0)[k]! = (emitList counts 0)[k]'hk_len2 :=
    getElem!_pos (emitList counts 0) k hk_len2
  rw [h1, h2, h3]

lemma emitGo_zero_isSortedNondecreasing (counts : Array Nat) :
    isSortedNondecreasing (emitGo counts 0 #[]) := by
  unfold isSortedNondecreasing
  intro i j hij hj
  have hi : i < (emitGo counts 0 #[]).size := by omega
  rw [emitGo_zero_getElem! counts i hi, emitGo_zero_getElem! counts j hj]
  have hpw := (emitList_pairwise_and_ge counts 0).1
  rw [List.pairwise_iff_getElem] at hpw
  exact hpw i j _ _ hij

lemma emitGo_zero_allInRange (counts : Array Nat) :
    allInRange (emitGo counts 0 #[]) := by
  unfold allInRange
  intro i hi
  rw [emitGo_zero_getElem! counts i hi]
  have hlen : i < (emitList counts 0).length := by
    have hsz := emitGo_zero_size counts
    rw [← hsz]
    exact hi
  have hmem : (emitList counts 0)[i]'hlen ∈ emitList counts 0 := List.getElem_mem hlen
  exact emitList_mem_range counts 0 _ hmem

lemma countSort_count (nums : Array Int) (hpre : precondition nums) (v : Int) :
    (countSort nums).count v = nums.count v := by
  unfold countSort
  set counts := countGo nums 0 (Array.replicate rangeSize 0) with hcounts_def
  rw [array_count, emitGo_zero_toList counts]
  by_cases hv : minVal ≤ v ∧ v ≤ maxVal
  · have hmin0 : minVal + ((0 : Nat) : Int) ≤ v := by
      unfold minVal at *
      omega
    rw [emitList_count_inside counts v hv.2 0 hmin0]
    have hcg := countGo_getElem! nums 0 (Array.replicate rangeSize 0)
      Array.size_replicate hpre v hv.1 hv.2
    have hlt := idxOf_lt v hv.1 hv.2
    have hlt_rep : idxOf v < (Array.replicate rangeSize 0).size := by
      rw [Array.size_replicate]; exact hlt
    have hinit : (Array.replicate rangeSize 0)[idxOf v]! = 0 := by
      rw [getElem!_pos (Array.replicate rangeSize 0) (idxOf v) hlt_rep]
      exact Array.getElem_replicate hlt_rep
    rw [hcounts_def, hcg, hinit, Nat.zero_add, List.drop_zero, array_count]
  · have hv_out : v < minVal ∨ maxVal < v := by omega
    have h1 : (emitList counts 0).count v = 0 := by
      rcases hv_out with hlt | hgt
      · have : v < minVal + ((0 : Nat) : Int) := by
          unfold minVal at *
          omega
        exact emitList_count_outside_lt counts v 0 this
      · exact emitList_count_outside_gt counts v hgt 0
    have h2 : nums.count v = 0 :=
      count_eq_zero_of_not_in_range nums hpre v hv_out
    rw [h1, h2]

lemma countSort_size (nums : Array Int) (hpre : precondition nums) :
    (countSort nums).size = nums.size := by
  have h_perm : (countSort nums).toList.Perm nums.toList := by
    rw [List.perm_iff_count]
    intro a
    have h := countSort_count nums hpre a
    rw [array_count, array_count] at h
    exact h
  have hlen := h_perm.length_eq
  rw [Array.size_eq_length_toList, Array.size_eq_length_toList]
  exact hlen

lemma countSort_isSortedNondecreasing (nums : Array Int) :
    isSortedNondecreasing (countSort nums) := by
  unfold countSort
  exact emitGo_zero_isSortedNondecreasing (countGo nums 0 (Array.replicate rangeSize 0))

lemma countSort_allInRange (nums : Array Int) :
    allInRange (countSort nums) := by
  unfold countSort
  exact emitGo_zero_allInRange (countGo nums 0 (Array.replicate rangeSize 0))

theorem countSort_correct (nums : Array Int) (hpre : precondition nums) :
    postcondition nums (countSort nums) := by
  unfold postcondition
  exact ⟨countSort_size nums hpre, countSort_isSortedNondecreasing nums,
         countSort_allInRange nums, countSort_count nums hpre⟩

prove_correct sortArray by
  velvet_vcgen [sortArray, postcondition] with try finish
  case count_continuation =>
    rw [countGo.eq_def (i := i)] at count_continuation
    simp only [counting, ↓reduceIte] at count_continuation
    exact count_continuation
  case push_continuation =>
    have hrem : remaining = (remaining - 1) + 1 := by omega
    conv at push_continuation =>
      lhs
      rw [hrem, pushMany_succ]
    exact push_continuation
  case emit_continuation =>
    rw [pushed, pushMany_zero] at push_continuation
    rw [push_continuation]
    rw [emitGo.eq_def (cIdx := cIdx)] at emit_continuation
    simp only [emitting, ↓reduceIte] at emit_continuation
    exact emit_continuation
  case sorted =>
    rename_i nums
    rw [countGo.eq_def (i := i)] at count_continuation
    have hnot_cnt : ¬ i < nums.size := by omega
    simp only [hnot_cnt, ↓reduceIte] at count_continuation
    rw [emitGo.eq_def (cIdx := cIdx)] at emit_continuation
    have hnot_emit : ¬ cIdx < rangeSize := by omega
    simp only [hnot_emit, ↓reduceIte] at emit_continuation
    have h_res : out = countSort nums := by
      unfold countSort
      rw [← count_continuation]
      exact emit_continuation
    rw [h_res]
    exact countSort_correct nums valid

end Proof

end SortAnArray
