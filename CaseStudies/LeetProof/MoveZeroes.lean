module

public import Velvet
public meta import Velvet
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Linarith

/-!
## Program description

Given an integer array `nums`, move all `0`'s to the end of it while maintaining
the relative order of the non-zero elements.

Note that you must do this in-place without making a copy of the array.

The program is expected to run in O(n) time and O(1) extra space, excluding the
returned array.
-/

namespace MoveZeroes

section Specs

public def countVal (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if x = v then acc + 1 else acc) 0

public def zerosFormSuffix (output : Array Int) : Prop :=
  ∀ (k : Nat),
    k < output.size →
    output[k]! = 0 →
    ∀ (j : Nat), k < j → j < output.size → output[j]! = 0

public def isNonZeroIndex (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ a[i]! ≠ 0

public def preservesNonZeroOrder (input : Array Int) (output : Array Int) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), isNonZeroIndex input i → f i < output.size ∧ output[(f i)]! = input[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → isNonZeroIndex input i → isNonZeroIndex input j → f i < f j) ∧
    (∀ (p : Nat), p < output.size → output[p]! ≠ 0 → ∃ (i : Nat), isNonZeroIndex input i ∧ f i = p)

public def precondition (_ : Array Int) : Prop :=
  True

public def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  (∀ (v : Int), countVal nums v = countVal result v) ∧
  zerosFormSuffix result ∧
  preservesNonZeroOrder nums result

end Specs

section Implementation

public def copyGo (nums : Array Int) (i : Nat) (st : Nat × Array Int) : Nat × Array Int :=
  if h : i < nums.size then
    let x := nums[i]!
    let st' := if x ≠ 0 then (st.1 + 1, st.2.set! st.1 x) else st
    copyGo nums (i + 1) st'
  else st
termination_by nums.size - i

public def fillZeros (n : Nat) (j : Nat) (a : Array Int) : Array Int :=
  if h : j < n then
    fillZeros n (j + 1) (a.set! j 0)
  else a
termination_by n - j

public def moveZeroesPure (nums : Array Int) : Array Int :=
  let (w, a1) := copyGo nums 0 (0, nums)
  fillZeros nums.size w a1

method moveZeroes (nums : Array Int)
  returns (result : Array Int)
  requires valid: precondition nums
  ensures moved: postcondition nums result
do
  let n := nums.size
  let mut res := nums
  let mut write : Nat := 0
  let mut i : Nat := 0
  while' copying: i < n
    invariant bounds: write ≤ i ∧ i ≤ n
    invariant copy_continuation:
      copyGo nums i (write, res) = copyGo nums 0 (0, nums)
    decreasing remaining_copy: n - i
    done_with copied: i = n
  do
    let x := nums[i]!
    if non_zero: x ≠ 0 then
      res := res.set! write x
      write := write + 1
    i := i + 1
  let mut j : Nat := write
  while' filling: j < n
    invariant bounds: write ≤ j ∧ j ≤ n
    invariant fill_continuation:
      fillZeros n j res = moveZeroesPure nums
    decreasing remaining_fill: n - j
    done_with filled: j = n
  do
    res := res.set! j 0
    j := j + 1
  return res

end Implementation

section Proof

public def step (st : Nat × Array Int) (x : Int) : Nat × Array Int :=
  let (w, a) := st
  if x ≠ 0 then (w + 1, a.set! w x) else (w, a)

lemma foldl_step_w (l : List Int) (w : Nat) (a : Array Int) :
    (l.foldl step (w, a)).1 = w + (l.filter (· ≠ 0)).length := by
  induction l generalizing w a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.filter_cons]
    by_cases hx : x ≠ 0
    · simp [step, hx, ih]
      omega
    · simp [step, hx, ih]

lemma foldl_step_size (l : List Int) (w : Nat) (a : Array Int) :
    (l.foldl step (w, a)).2.size = a.size := by
  induction l generalizing w a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hx : x ≠ 0
    · simpa [step, hx, Array.size_set!] using ih (w + 1) (a.set! w x)
    · simpa [step, hx] using ih w a

lemma getElem!_set!_self (a : Array Int) (i : Nat) (v : Int) (hi : i < a.size) :
    (a.set! i v)[i]! = v := by
  simp [Array.set!, Array.setIfInBounds, hi, getElem!_pos]

lemma getElem!_set!_ne (a : Array Int) (i j : Nat) (v : Int)
    (hi : i < a.size) (hj : j < a.size) (hne : j ≠ i) :
    (a.set! i v)[j]! = a[j]! := by
  rw [getElem!_pos (a.set! i v) j (by simpa [Array.size_set!])]
  rw [getElem!_pos a j hj]
  simp only [Array.set!, Array.setIfInBounds, dite_eq_left hi]
  exact Array.getElem_set_ne hi hj (fun h => hne h.symm)

lemma foldl_step_get_lt (l : List Int) (w : Nat) (a : Array Int) (i : Nat)
    (hi : i < w) (hcap : w + (l.filter (· ≠ 0)).length ≤ a.size) :
    (l.foldl step (w, a)).2[i]! = a[i]! := by
  induction l generalizing w a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hx : x ≠ 0
    · have h_step : step (w, a) x = (w + 1, a.set! w x) := by simp [step, hx]
      rw [h_step]
      have hcap' : w + 1 + (xs.filter (· ≠ 0)).length ≤ (a.set! w x).size := by
        rw [Array.size_set!]
        have h_flt : (x :: xs).filter (· ≠ 0) = x :: xs.filter (· ≠ 0) := by simp [hx]
        rw [h_flt] at hcap
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
      have hi_w1 : i < w + 1 := by omega
      rw [ih (w + 1) (a.set! w x) hi_w1 hcap']
      have hi_bounds : i < a.size := by omega
      exact Array.getElem!_set!_ne a w i x (by omega)
    · have h_step : step (w, a) x = (w, a) := by simp [step, hx]
      rw [h_step]
      have hcap' : w + (xs.filter (· ≠ 0)).length ≤ a.size := by simpa [hx] using hcap
      exact ih w a hi hcap'

lemma foldl_step_content (l : List Int) (w : Nat) (a : Array Int)
    (h_sz : w + (l.filter (· ≠ 0)).length ≤ a.size) :
    ∀ k (_hk : k < (l.filter (· ≠ 0)).length),
      (l.foldl step (w, a)).2[w + k]! = (l.filter (· ≠ 0))[k]! := by
  induction l generalizing w a with
  | nil =>
    intro k hk
    contradiction
  | cons x xs ih =>
    intro k hk
    simp only [List.foldl_cons]
    by_cases hx : x = 0
    · have h_flt : (x :: xs).filter (· ≠ 0) = xs.filter (· ≠ 0) := by simp [hx]
      have h_step : step (w, a) x = (w, a) := by unfold step; simp [hx]
      rw [h_flt] at h_sz hk ⊢
      rw [h_step]
      have h_sz' : w + (xs.filter (· ≠ 0)).length ≤ a.size := by
        exact h_sz
      exact ih w a h_sz' k hk
    · have h_flt : (x :: xs).filter (· ≠ 0) = x :: xs.filter (· ≠ 0) := by simp [hx]
      have h_step : step (w, a) x = (w + 1, a.set! w x) := by unfold step; simp [hx]
      rw [h_flt] at h_sz hk ⊢
      rw [h_step]
      have h_sz_xs : w + 1 + (xs.filter (· ≠ 0)).length ≤ (a.set! w x).size := by
        rw [Array.size_set!]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_sz
      cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem!_cons_zero]
        have hw_sz : w < a.size := by
          have h_sz' : w + (1 + (xs.filter (· ≠ 0)).length) ≤ a.size := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_sz
          have : w < w + (1 + (xs.filter (· ≠ 0)).length) := by omega
          exact lt_of_lt_of_le this h_sz'
        have h_lt : w < w + 1 := by omega
        have ha_w1 : w + 1 ≤ (a.set! w x).size := by rw [Array.size_set!]; omega
        rw [foldl_step_get_lt xs (w + 1) (a.set! w x) w h_lt h_sz_xs]
        exact getElem!_set!_self a w x hw_sz
      | succ k =>
        simp only [List.getElem!_cons_succ]
        have hk' : k < (xs.filter (· ≠ 0)).length := by
          simp only [List.length_cons] at hk
          omega
        have h_add : w + (k + 1) = (w + 1) + k := by omega
        rw [h_add]
        exact ih (w + 1) (a.set! w x) h_sz_xs k hk'

lemma fillZeros_spec (n : Nat) (j : Nat) (a : Array Int)
    (hj : j ≤ n) (h_sz : n ≤ a.size) :
    (fillZeros n j a).size = a.size ∧
    (∀ k, k < j → (fillZeros n j a)[k]! = a[k]!) ∧
    (∀ k, j ≤ k → k < n → (fillZeros n j a)[k]! = 0) ∧
    (∀ k, n ≤ k → k < a.size → (fillZeros n j a)[k]! = a[k]!) := by
  induction h_d : n - j generalizing j a with
  | zero =>
    have hj_eq : j = n := by omega
    simp [fillZeros.eq_def, hj_eq]
    omega
  | succ d ih =>
    have hj_lt : j < n := by omega
    rw [fillZeros.eq_def]
    simp only [hj_lt, ↓reduceDIte]
    have hj1_le : j + 1 ≤ n := by omega
    have ha_set_sz : n ≤ (a.set! j 0).size := by rw [Array.size_set!]; omega
    have hd_eq : n - (j + 1) = d := by omega
    have ih_app := ih (j + 1) (a.set! j 0) hj1_le ha_set_sz hd_eq
    have hj_bound : j < a.size := by omega
    refine ⟨by rw [ih_app.1, Array.size_set!], ?_, ?_, ?_⟩
    · intro k hk
      have hk_lt : k < j + 1 := by omega
      rw [ih_app.2.1 k hk_lt]
      have hk_bound : k < a.size := by omega
      exact getElem!_set!_ne a j k 0 hj_bound hk_bound (by omega)
    · intro k hk_ge hk_lt
      by_cases hkj : k = j
      · have hj_lt_j1 : j < j + 1 := by omega
        rw [hkj, ih_app.2.1 j hj_lt_j1]
        exact getElem!_set!_self a j 0 hj_bound
      · have hk_ge' : j + 1 ≤ k := by omega
        exact ih_app.2.2.1 k hk_ge' hk_lt
    · intro k hk_ge hk_lt
      have hk_bound : k < (a.set! j 0).size := by rw [Array.size_set!]; exact hk_lt
      rw [ih_app.2.2.2 k hk_ge hk_bound]
      have hk_a : k < a.size := hk_lt
      exact getElem!_set!_ne a j k 0 hj_bound hk_a (by omega)

theorem copyGo_eq_foldl (nums : Array Int) :
    ∀ (i : Nat) (st : Nat × Array Int),
      copyGo nums i st = (nums.toList.drop i).foldl step st
  | i, st => by
      rw [copyGo.eq_def]
      by_cases hi : i < nums.size
      · simp only [hi, ↓reduceDIte]
        have hdrop : nums.toList.drop i = nums[i]! :: nums.toList.drop (i + 1) := by
          have hi_len : i < nums.toList.length := by
            have := nums.length_toList
            omega
          rw [List.drop_eq_getElem_cons hi_len]
          simp [getElem!_pos nums i hi]
        rw [hdrop, List.foldl_cons]
        by_cases h_ne : nums[i]! ≠ 0
        · simpa [h_ne, step] using
            copyGo_eq_foldl nums (i + 1) (st.1 + 1, st.2.set! st.1 nums[i]!)
        · simpa [h_ne, step] using copyGo_eq_foldl nums (i + 1) st
      · simp only [hi, ↓reduceDIte]
        have : nums.toList.drop i = [] := by
          apply List.drop_eq_nil_of_le
          have := nums.length_toList
          omega
        rw [this, List.foldl_nil]
termination_by i => nums.size - i

theorem moveZeroesPure_eq (nums : Array Int) :
    moveZeroesPure nums = fillZeros nums.size (nums.toList.foldl step (0, nums)).1 (nums.toList.foldl step (0, nums)).2 := by
  unfold moveZeroesPure
  have h := copyGo_eq_foldl nums 0 (0, nums)
  rw [List.drop_zero] at h
  rw [h]

lemma list_foldl_count (l : List Int) (v : Int) (acc : Nat) :
    l.foldl (fun acc x => if x = v then acc + 1 else acc) acc = acc + l.count v := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.count_cons]
    by_cases h : x = v
    · simp [h]
      omega
    · simp [h]

lemma countVal_eq_count (a : Array Int) (v : Int) :
    countVal a v = a.toList.count v := by
  unfold countVal
  rw [← Array.foldl_toList]
  have := list_foldl_count a.toList v 0
  omega

lemma list_filter_get_countP (l : List Int) (i : Nat) (hi : i < l.length) (hnz : l[i]! ≠ 0) :
    (l.filter (· ≠ 0))[List.countP (· ≠ 0) (l.take i)]! = l[i]! := by
  induction l generalizing i with
  | nil => contradiction
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.countP_nil, List.getElem!_cons_zero]
      have : hd ≠ 0 := by simpa using hnz
      have h_flt : (hd :: tl).filter (· ≠ 0) = hd :: tl.filter (· ≠ 0) := by simp [this]
      rw [h_flt, List.getElem!_cons_zero]
    | succ i =>
      simp only [List.take_succ_cons, List.countP_cons, List.getElem!_cons_succ] at hnz ⊢
      have hi' : i < tl.length := by simpa using hi
      by_cases hhd : hd = 0
      · have h_flt : (hd :: tl).filter (· ≠ 0) = tl.filter (· ≠ 0) := by simp [hhd]
        have h_dec : decide (hd ≠ 0) = false := decide_eq_false (by intro h; exact h hhd)
        rw [h_flt, h_dec]
        exact ih i hi' hnz
      · have h_flt : (hd :: tl).filter (· ≠ 0) = hd :: tl.filter (· ≠ 0) := by simp [hhd]
        have h_dec : decide (hd ≠ 0) = true := decide_eq_true hhd
        rw [h_flt, h_dec]
        simp only [ite_true, List.getElem!_cons_succ]
        exact ih i hi' hnz

lemma list_countP_take_lt (l : List Int) (i j : Nat) (hij : i < j) (_hj : j ≤ l.length) (hnz : l[i]! ≠ 0) (hi : i < l.length) :
    List.countP (· ≠ 0) (l.take i) < List.countP (· ≠ 0) (l.take j) := by
  have h_take : l.take (i + 1) = l.take i ++ [l[i]!] := by
    rw [List.take_add_one]
    have : l[i]? = some l[i]! := by
      rw [getElem!_pos l i hi]
      exact List.getElem?_eq_getElem hi
    rw [this]
    rfl
  have h1 : List.countP (· ≠ 0) (l.take (i + 1)) = List.countP (· ≠ 0) (l.take i) + 1 := by
    rw [h_take, List.countP_append, List.countP_singleton]
    have : decide (l[i]! ≠ 0) = true := decide_eq_true hnz
    rw [this]
    rfl
  have h2 : List.countP (· ≠ 0) (l.take (i + 1)) ≤ List.countP (· ≠ 0) (l.take j) := by
    have h_sub : l.take j = l.take (i + 1) ++ (l.take j).drop (i + 1) := by
      have : (l.take j).take (i + 1) = l.take (i + 1) := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [← this, List.take_append_drop]
    rw [h_sub, List.countP_append]
    omega
  omega

lemma list_filter_exists_index (l : List Int) (p : Nat) (hp : p < (l.filter (· ≠ 0)).length) :
    ∃ i, i < l.length ∧ l[i]! ≠ 0 ∧ List.countP (· ≠ 0) (l.take i) = p := by
  induction l generalizing p with
  | nil => contradiction
  | cons hd tl ih =>
    by_cases hhd : hd = 0
    · have h_flt : (hd :: tl).filter (· ≠ 0) = tl.filter (· ≠ 0) := by simp [hhd]
      rw [h_flt] at hp
      obtain ⟨i, hi, hnz, hcnt⟩ := ih p hp
      refine ⟨i + 1, by simp; omega, ?_, ?_⟩
      · simp only [List.getElem!_cons_succ]
        exact hnz
      · simp only [List.take_succ_cons, List.countP_cons]
        have h_dec : decide (hd ≠ 0) = false := decide_eq_false (by intro h; exact h hhd)
        rw [h_dec]
        simpa [decide_not] using hcnt
    · have h_flt : (hd :: tl).filter (· ≠ 0) = hd :: tl.filter (· ≠ 0) := by simp [hhd]
      rw [h_flt] at hp
      simp only [List.length_cons] at hp
      cases p with
      | zero =>
        refine ⟨0, by simp, ?_, ?_⟩
        · simp only [List.getElem!_cons_zero]
          exact hhd
        · simp only [List.take_zero, List.countP_nil]
      | succ p =>
        have hp' : p < (tl.filter (· ≠ 0)).length := by omega
        obtain ⟨i, hi, hnz, hcnt⟩ := ih p hp'
        refine ⟨i + 1, by simp; omega, ?_, ?_⟩
        · simp only [List.getElem!_cons_succ]
          exact hnz
        · simp only [List.take_succ_cons, List.countP_cons]
          have h_dec : decide (hd ≠ 0) = true := decide_eq_true hhd
          rw [h_dec]
          simp only [ite_true, hcnt]

lemma list_count_zero_add_filter_nonzero (l : List Int) :
    l.count 0 + (l.filter (· ≠ 0)).length = l.length := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h : hd = 0
    · subst hd
      simp at *
      omega
    · simp [h] at *
      omega

theorem correctness_goal (nums : Array Int) (_h_precond : precondition nums) :
    postcondition nums (moveZeroesPure nums) := by
  have h_w : (nums.toList.foldl step (0, nums)).1 = (nums.toList.filter (· ≠ 0)).length := by
    have := foldl_step_w nums.toList 0 nums
    omega
  have h_sz : (nums.toList.foldl step (0, nums)).2.size = nums.size := by
    exact foldl_step_size nums.toList 0 nums
  have h_w_le : (nums.toList.filter (· ≠ 0)).length ≤ nums.size := by
    have h_le := List.length_filter_le (· ≠ 0) nums.toList
    have h_len := nums.length_toList
    omega
  have h_fill := fillZeros_spec nums.size (nums.toList.foldl step (0, nums)).1
    (nums.toList.foldl step (0, nums)).2 (by omega) (by omega)
  have h_pure_sz : (moveZeroesPure nums).size = nums.size := by
    rw [moveZeroesPure_eq, h_fill.1, h_sz]
  have h_pure_get_lt : ∀ k, k < (nums.toList.filter (· ≠ 0)).length →
      (moveZeroesPure nums)[k]! = (nums.toList.filter (· ≠ 0))[k]! := by
    intro k hk
    rw [moveZeroesPure_eq]
    have hk_w : k < (nums.toList.foldl step (0, nums)).1 := by omega
    rw [h_fill.2.1 k hk_w]
    have h_content := foldl_step_content nums.toList 0 nums (by omega) k hk
    simp only [Nat.zero_add] at h_content
    exact h_content
  have h_pure_get_ge : ∀ k, (nums.toList.filter (· ≠ 0)).length ≤ k → k < nums.size →
      (moveZeroesPure nums)[k]! = 0 := by
    intro k hk_ge hk_lt
    rw [moveZeroesPure_eq]
    have hk_w : (nums.toList.foldl step (0, nums)).1 ≤ k := by omega
    exact h_fill.2.2.1 k hk_w hk_lt
  have h_rearrange : (moveZeroesPure nums).toList =
      (nums.toList.filter (· ≠ 0)) ++ List.replicate (nums.size - (nums.toList.filter (· ≠ 0)).length) 0 := by
    apply List.ext_getElem
    · simp only [Array.length_toList, h_pure_sz, List.length_append, List.length_replicate]
      omega
    · intro k h1 h2
      simp only [Array.length_toList, h_pure_sz] at h1
      have h1_pure : k < (moveZeroesPure nums).size := by rw [h_pure_sz]; exact h1
      rw [Array.getElem_toList]
      rw [← getElem!_pos (moveZeroesPure nums) k h1_pure]
      by_cases hk : k < (nums.toList.filter (· ≠ 0)).length
      · rw [h_pure_get_lt k hk]
        rw [List.getElem_append_left hk]
        rw [getElem!_pos (nums.toList.filter (· ≠ 0)) k hk]
      · have hk_ge : (nums.toList.filter (· ≠ 0)).length ≤ k := by omega
        rw [h_pure_get_ge k hk_ge h1]
        rw [List.getElem_append_right hk_ge]
        simp only [List.getElem_replicate]
  refine ⟨h_pure_sz, ?_, ?_, ?_⟩
  · intro v
    rw [countVal_eq_count, countVal_eq_count, h_rearrange, List.count_append]
    by_cases hv : v = 0
    · subst hv
      have h_flt_0 : (nums.toList.filter (· ≠ 0)).count 0 = 0 := by
        rw [List.count_eq_zero]
        intro h_mem
        have := (List.mem_filter.mp h_mem).2
        revert this
        decide
      rw [h_flt_0, Nat.zero_add, List.count_replicate_self]
      have h_cz := list_count_zero_add_filter_nonzero nums.toList
      have h_len := nums.length_toList
      omega
    · rw [List.count_filter]
      · have hbeq : ((0 : Int) == v) = false := beq_false_of_ne (Ne.symm hv)
        rw [List.count_replicate, hbeq]
        rfl
      · exact decide_eq_true hv
  · unfold zerosFormSuffix
    intro k hk hk0 j hkj hj
    rw [h_pure_sz] at hk hj
    have hk_ge_w : (nums.toList.filter (· ≠ 0)).length ≤ k := by
      by_contra h_lt
      have hk_lt : k < (nums.toList.filter (· ≠ 0)).length := by omega
      have h_get := h_pure_get_lt k hk_lt
      rw [hk0] at h_get
      have h_mem : (nums.toList.filter (· ≠ 0))[k]! ≠ 0 := by
        rw [getElem!_pos (nums.toList.filter (· ≠ 0)) k hk_lt]
        have h_get_mem := List.getElem_mem hk_lt
        have := (List.mem_filter.mp h_get_mem).2
        exact of_decide_eq_true this
      exact h_mem h_get.symm
    have hj_ge_w : (nums.toList.filter (· ≠ 0)).length ≤ j := by omega
    exact h_pure_get_ge j hj_ge_w hj
  · unfold preservesNonZeroOrder
    refine ⟨fun i => List.countP (· ≠ 0) (nums.toList.take i), ?_, ?_, ?_⟩
    · intro i hi
      unfold isNonZeroIndex at hi
      have hi_len : i < nums.toList.length := by
        have := nums.length_toList; omega
      have h_nz : nums.toList[i]! ≠ 0 := by
        rw [getElem!_pos nums i hi.1] at hi
        rw [getElem!_pos nums.toList i hi_len, Array.getElem_toList]
        exact hi.2
      have h_take_succ := list_countP_take_lt nums.toList i (i + 1) (by omega) (by have := nums.length_toList; omega) h_nz hi_len
      have h_take_le : List.countP (· ≠ 0) (nums.toList.take (i + 1)) ≤ (nums.toList.filter (· ≠ 0)).length := by
        have h_app : nums.toList = nums.toList.take (i + 1) ++ nums.toList.drop (i + 1) := by rw [List.take_append_drop]
        nth_rw 2 [h_app]
        rw [List.countP_eq_length_filter, List.filter_append]
        simp only [List.length_append]
        omega
      have h_cnt_lt : List.countP (· ≠ 0) (nums.toList.take i) < (nums.toList.filter (· ≠ 0)).length := by
        omega
      have h_cnt_lt_pure : List.countP (· ≠ 0) (nums.toList.take i) < (moveZeroesPure nums).size := by
        rw [h_pure_sz]
        omega
      refine ⟨h_cnt_lt_pure, ?_⟩
      dsimp
      rw [h_pure_get_lt (List.countP (· ≠ 0) (nums.toList.take i)) h_cnt_lt]
      have h_filt_get := list_filter_get_countP nums.toList i hi_len h_nz
      rw [h_filt_get, getElem!_pos nums.toList i hi_len, getElem!_pos nums i hi.1, Array.getElem_toList]
    · intro i j hij hi hj
      unfold isNonZeroIndex at hi hj
      have hi_len : i < nums.toList.length := by have := nums.length_toList; omega
      have hj_len : j < nums.toList.length := by have := nums.length_toList; omega
      have h_nz : nums.toList[i]! ≠ 0 := by
        rw [getElem!_pos nums i hi.1] at hi
        rw [getElem!_pos nums.toList i hi_len, Array.getElem_toList]
        exact hi.2
      exact list_countP_take_lt nums.toList i j hij (by have := nums.length_toList; omega) h_nz hi_len
    · intro p hp hp_nz
      rw [h_pure_sz] at hp
      have hp_lt_w : p < (nums.toList.filter (· ≠ 0)).length := by
        by_contra h_ge
        have hp_ge : (nums.toList.filter (· ≠ 0)).length ≤ p := by omega
        have hp_zero := h_pure_get_ge p hp_ge hp
        exact hp_nz hp_zero
      obtain ⟨i, hi_len, hnz, hcnt⟩ := list_filter_exists_index nums.toList p hp_lt_w
      have hi_sz : i < nums.size := by have := nums.length_toList; omega
      have h_nz' : nums[i]! ≠ 0 := by
        have : nums.toList[i]! = nums[i]! := by
          rw [getElem!_pos nums.toList i hi_len, getElem!_pos nums i hi_sz, Array.getElem_toList]
        rw [this] at hnz
        exact hnz
      refine ⟨i, ⟨⟨hi_sz, h_nz'⟩, hcnt⟩⟩

prove_correct moveZeroes by
  velvet_vcgen [moveZeroes, postcondition] with try finish
  all_goals try {
    rw [fillZeros.eq_def] at fill_continuation
    simp only [filled, lt_self_iff_false, ↓reduceDIte] at fill_continuation
    rw [fill_continuation]
    exact correctness_goal _ valid
  }
  all_goals try {
    unfold moveZeroesPure
    rw [← copy_continuation, copied, copyGo.eq_def]
    simp only [lt_self_iff_false, ↓reduceDIte]
  }
  all_goals try {
    rw [← copy_continuation]
    conv_rhs => rw [copyGo.eq_def]
    simp only [copying, ↓reduceDIte]
    split_ifs with h_if
    · rfl
    · exfalso; exact h_if non_zero
  }
  all_goals try {
    rw [← copy_continuation]
    conv_rhs => rw [copyGo.eq_def]
    simp only [copying, ↓reduceDIte]
    split_ifs with h_if
    · exfalso; exact non_zero h_if
    · rfl
  }
  case fill_continuation =>
    calc
      fillZeros _ (j + 1) (res.set! j 0) = fillZeros _ j res := by
        nth_rewrite 2 [fillZeros.eq_def]
        simp [filling]
      _ = moveZeroesPure _ := fill_continuation

end Proof

end MoveZeroes
