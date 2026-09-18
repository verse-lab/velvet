module

public import Velvet
public meta import Velvet
public import Mathlib.Tactic.IntervalCases

/-!
## Program description

Reorder an array containing only `0`, `1`, and `2` so all zeroes precede all
ones, which precede all twos. The program is expected to run in O(n) time and
O(1) extra space, excluding the returned array.
-/

namespace SortColors

section Specs

public def ColorsOnly (nums : Array Nat) : Prop :=
  ∀ i, i < nums.size → nums[i]! ≤ 2

public def Is012Sorted (nums : Array Nat) : Prop :=
  ∃ a b,
    a ≤ b ∧ b ≤ nums.size ∧
    (∀ i, i < a → nums[i]! = 0) ∧
    (∀ i, a ≤ i ∧ i < b → nums[i]! = 1) ∧
    (∀ i, b ≤ i ∧ i < nums.size → nums[i]! = 2)

public def countVal (nums : Array Nat) (v : Nat) : Nat := nums.count v

public def precondition (nums : Array Nat) : Prop := ColorsOnly nums

public def postcondition (nums result : Array Nat) : Prop :=
  result.size = nums.size ∧
  Is012Sorted result ∧
  countVal result 0 = countVal nums 0 ∧
  countVal result 1 = countVal nums 1 ∧
  countVal result 2 = countVal nums 2

end Specs

section Implementation

public def countStep (c : Nat × Nat × Nat) (x : Nat) : Nat × Nat × Nat :=
  if x = 0 then (c.1 + 1, c.2.1, c.2.2)
  else if x = 1 then (c.1, c.2.1 + 1, c.2.2)
  else (c.1, c.2.1, c.2.2 + 1)

public def countGo (nums : Array Nat) (i : Nat)
    (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  if i < nums.size then countGo nums (i + 1) (countStep c nums[i]!) else c
termination_by nums.size - i

public def fillGo (nums : Array Nat) (counts : Nat × Nat × Nat)
    (i : Nat) (out : Array Nat) : Array Nat :=
  if i < nums.size then
    let value := if i < counts.1 then 0
      else if i < counts.1 + counts.2.1 then 1 else 2
    fillGo nums counts (i + 1) (out.set! i value)
  else out
termination_by nums.size - i

public def sort012 (nums : Array Nat) : Array Nat :=
  let counts := countGo nums 0 (0, 0, 0)
  fillGo nums counts 0 nums

method sortColors (nums : Array Nat)
  returns (result : Array Nat)
  requires colors_only: precondition nums
  ensures sorted: postcondition nums result
do
  let mut i : Nat := 0
  let mut c0 : Nat := 0
  let mut c1 : Nat := 0
  let mut c2 : Nat := 0
  while counting: i < nums.size
    invariant count_index: i ≤ nums.size
    invariant count_continuation:
      countGo nums i (c0, c1, c2) = countGo nums 0 (0, 0, 0)
    decreasing count_remaining: nums.size - i
    done_with counted: i = nums.size
  do
    if zero: nums[i]! = 0 then
      c0 := c0 + 1
    else if one: nums[i]! = 1 then
      c1 := c1 + 1
    else
      c2 := c2 + 1
    i := i + 1
  let mut out := nums
  i := 0
  while filling: i < nums.size
    invariant fill_index: i ≤ nums.size
    invariant fill_continuation:
      fillGo nums (c0, c1, c2) i out = sort012 nums
    decreasing fill_remaining: nums.size - i
    done_with filled: i = nums.size
  do
    if in_zeroes: i < c0 then
      out := out.set! i 0
    else if in_ones: i < c0 + c1 then
      out := out.set! i 1
    else
      out := out.set! i 2
    i := i + 1
  return out

end Implementation

section Proof

public def suffixCount (nums : Array Nat) (i v : Nat) : Nat :=
  (nums.toList.drop i).count v

theorem countGo_eq_suffix (nums : Array Nat) (i : Nat)
    (c : Nat × Nat × Nat) (colors : ColorsOnly nums) :
    countGo nums i c =
      (c.1 + suffixCount nums i 0,
       c.2.1 + suffixCount nums i 1,
       c.2.2 + suffixCount nums i 2) := by
  fun_induction countGo nums i c
  case case1 i c h ih =>
    have hdrop : nums.toList.drop i = nums[i]! :: nums.toList.drop (i + 1) := by
      have hd := List.drop_eq_getElem_cons (l := nums.toList) (i := i) (by simpa using h)
      rw [getElem!_pos nums i h]
      exact hd
    have hx := colors i h
    by_cases h0 : nums[i]! = 0
    · rw [ih]
      simp [suffixCount, hdrop, countStep, h0, Nat.add_assoc, Nat.add_comm]
    · by_cases h1 : nums[i]! = 1
      · rw [ih]
        simp [suffixCount, hdrop, countStep, h1, Nat.add_assoc, Nat.add_comm]
      · have h2 : nums[i]! = 2 := by omega
        rw [ih]
        simp [suffixCount, hdrop, countStep, h2, Nat.add_assoc, Nat.add_comm]
  case case2 i c h =>
    have hlen : nums.toList.length ≤ i := by simpa using (Nat.le_of_not_gt h)
    simp [suffixCount, List.drop_eq_nil_iff.mpr hlen]

theorem countGo_zero (nums : Array Nat) (colors : ColorsOnly nums) :
    countGo nums 0 (0, 0, 0) =
      (countVal nums 0, countVal nums 1, countVal nums 2) := by
  have h := countGo_eq_suffix nums 0 (0, 0, 0) colors
  simpa [suffixCount, countVal, ← Array.count_toList] using h

public def colorAt (counts : Nat × Nat × Nat) (i : Nat) : Nat :=
  if i < counts.1 then 0 else if i < counts.1 + counts.2.1 then 1 else 2

public def colorBlocks (counts : Nat × Nat × Nat) : Array Nat :=
  Array.replicate counts.1 0 ++
  Array.replicate counts.2.1 1 ++
  Array.replicate counts.2.2 2

public def FilledPrefix (counts : Nat × Nat × Nat) (i : Nat) (out : Array Nat) : Prop :=
  ∀ j, j < i → out[j]! = colorAt counts j

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

theorem colorBlocks_size (counts : Nat × Nat × Nat) :
    (colorBlocks counts).size = counts.1 + counts.2.1 + counts.2.2 := by
  simp [colorBlocks, Nat.add_assoc]

theorem colorBlocks_get (counts : Nat × Nat × Nat) (i : Nat)
    (hi : i < counts.1 + counts.2.1 + counts.2.2) :
    (colorBlocks counts)[i]! = colorAt counts i := by
  by_cases h0 : i < counts.1
  · simp [colorBlocks, colorAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_append, h0]
  · by_cases h1 : i < counts.1 + counts.2.1
    · have hs : i - counts.1 < counts.2.1 := by omega
      simp [colorBlocks, colorAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_append, h0, h1, hs]
    · have hs1 : ¬i - counts.1 < counts.2.1 := by omega
      have hs2 : i - counts.1 - counts.2.1 < counts.2.2 := by omega
      simp [colorBlocks, colorAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_append, h0, h1, hs1, hs2]

theorem fillGo_eq_blocks (nums out : Array Nat) (counts : Nat × Nat × Nat)
    (i : Nat) (hi : i ≤ nums.size) (hout : out.size = nums.size)
    (hsum : counts.1 + counts.2.1 + counts.2.2 = nums.size)
    (hprefix : FilledPrefix counts i out) :
    fillGo nums counts i out = colorBlocks counts := by
  fun_induction fillGo nums counts i out
  case case1 idx arr hscan value ih =>
    apply ih
    · omega
    · simp [hout]
    · intro j hj
      have hjbound : j < arr.size := by rw [hout]; omega
      have hibound : idx < arr.size := by rw [hout]; exact hscan
      by_cases hji : j = idx
      · subst j
        rw [getElem!_set! arr idx idx value hibound hibound]
        simp [value, colorAt]
      · rw [getElem!_set! arr idx j value hibound hjbound, ite_eq_right hji]
        exact hprefix j (by omega)
  case case2 idx arr hscan =>
    apply Array.ext
    · rw [hout, colorBlocks_size, hsum]
    · intro j hj₁ hj₂
      have hj : j < idx := by omega
      have hp := hprefix j hj
      have hb := colorBlocks_get counts j (by simpa [colorBlocks_size] using hj₂)
      rw [getElem!_pos arr j hj₁] at hp
      rw [getElem!_pos (colorBlocks counts) j hj₂] at hb
      exact hp.trans hb.symm

theorem list_count012_eq_length (l : List Nat)
    (h : ∀ x ∈ l, x ≤ 2) :
    l.count 0 + l.count 1 + l.count 2 = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ 2 := by
        intro y hy
        exact h y (by simp [hy])
      specialize ih hxs
      interval_cases x <;> simp_all <;> omega

theorem color_count_sum (nums : Array Nat) (colors : ColorsOnly nums) :
    countVal nums 0 + countVal nums 1 + countVal nums 2 = nums.size := by
  have hlist : ∀ x ∈ nums.toList, x ≤ 2 := by
    intro x hx
    have ha : x ∈ nums := by simpa using hx
    obtain ⟨i, hi, rfl⟩ := (Array.mem_iff_getElem).mp ha
    simpa [getElem!_pos nums i hi] using colors i hi
  have h := list_count012_eq_length nums.toList hlist
  simpa [countVal, ← Array.count_toList] using h

theorem colorBlocks_sorted (counts : Nat × Nat × Nat) :
    Is012Sorted (colorBlocks counts) := by
  refine ⟨counts.1, counts.1 + counts.2.1, by omega,
    by simp [colorBlocks_size], ?_, ?_, ?_⟩
  · intro i hi
    rw [colorBlocks_get counts i]
    · simp [colorAt, hi]
    · omega
  · intro i hi
    rw [colorBlocks_get counts i]
    · simp [colorAt, hi.1, hi.2]
    · omega
  · intro i hi
    rw [colorBlocks_get counts i]
    · have h0 : ¬i < counts.1 := by omega
      have h1 : ¬i < counts.1 + counts.2.1 := by omega
      simp [colorAt, h0, h1]
    · simpa [colorBlocks_size] using hi.2

theorem colorBlocks_counts (counts : Nat × Nat × Nat) :
    countVal (colorBlocks counts) 0 = counts.1 ∧
    countVal (colorBlocks counts) 1 = counts.2.1 ∧
    countVal (colorBlocks counts) 2 = counts.2.2 := by
  simp [countVal, colorBlocks, Array.count_replicate]

theorem sort012_eq_blocks (nums : Array Nat) (colors : ColorsOnly nums) :
    sort012 nums =
      colorBlocks (countVal nums 0, countVal nums 1, countVal nums 2) := by
  rw [sort012, countGo_zero nums colors]
  apply fillGo_eq_blocks
  · omega
  · rfl
  · exact color_count_sum nums colors
  · intro j hj
    omega

theorem sort012_correct (nums : Array Nat) (colors : ColorsOnly nums) :
    postcondition nums (sort012 nums) := by
  rw [sort012_eq_blocks nums colors]
  have hs := colorBlocks_sorted (countVal nums 0, countVal nums 1, countVal nums 2)
  have hc := colorBlocks_counts (countVal nums 0, countVal nums 1, countVal nums 2)
  refine ⟨?_, hs, hc.1, hc.2.1, hc.2.2⟩
  simp [colorBlocks_size, color_count_sum nums colors]

prove_correct sortColors by
  velvet_vcgen [sortColors, postcondition] with try finish
  case count_continuation =>
    rename_i nums
    rw [getElem!_pos nums i counting] at zero
    rw [countGo.eq_def] at count_continuation
    simp [counting, zero] at count_continuation
    exact count_continuation
  case count_continuation =>
    rename_i nums
    rw [getElem!_pos nums i counting] at zero one
    rw [countGo.eq_def] at count_continuation
    simp [counting, countStep, one] at count_continuation
    exact count_continuation
  case count_continuation =>
    rename_i nums
    rw [getElem!_pos nums i counting] at zero one
    rw [countGo.eq_def] at count_continuation
    simp [counting, countStep, zero, one] at count_continuation
    exact count_continuation
  case fill_continuation =>
    rw [countGo.eq_def] at count_continuation
    simp [counted] at count_continuation
    simp [sort012, ← count_continuation]
  case fill_continuation =>
    rw [fillGo.eq_def] at fill_continuation
    simpa [filling, in_zeroes] using fill_continuation
  case fill_continuation =>
    rw [fillGo.eq_def] at fill_continuation
    simpa [filling, in_zeroes, in_ones] using fill_continuation
  case fill_continuation =>
    rw [fillGo.eq_def] at fill_continuation
    simpa [filling, in_zeroes, in_ones] using fill_continuation
  case sorted =>
    rw [fillGo.eq_def] at fill_continuation
    simp [filled] at fill_continuation
    rw [fill_continuation]
    exact sort012_correct _ colors_only

end Proof

end SortColors
