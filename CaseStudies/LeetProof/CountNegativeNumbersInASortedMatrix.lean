module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
## Program description

1351. Count Negative Numbers in a Sorted Matrix: count how many entries in a matrix are negative.

Natural language breakdown:
1. The input is a 2D matrix `grid` represented as an array of rows, where each row is an array of integers.
2. The matrix is rectangular: all rows have the same number of columns.
3. Each row is sorted in non-increasing order (left to right values never increase).
4. Each column is sorted in non-increasing order (top to bottom values never increase).
5. The output is the number of positions (i,j) within the matrix bounds such that `grid[i][j] < 0`.
6. The output is a natural number.

The program is expected to run in O(m + n) time and O(1) extra space.
-/

namespace CountNegativeNumbersInASortedMatrix

section Specs

-- Helper: number of columns, defined total (0 for empty grid)
public def numCols (grid : Array (Array Int)) : Nat :=
  if grid.size = 0 then 0 else (grid[0]!).size

-- Helper: rectangular matrix (nonempty and all rows have same size)
public def Rectangular (grid : Array (Array Int)) : Prop :=
  grid.size > 0 ∧
  numCols grid > 0 ∧
  (∀ (i : Nat), i < grid.size → (grid[i]!).size = numCols grid)

-- Helper: row-wise non-increasing order
-- For each row i and adjacent columns j and j+1: grid[i][j] ≥ grid[i][j+1]
public def RowWiseNonIncreasing (grid : Array (Array Int)) : Prop :=
  let m := grid.size
  let n := numCols grid
  ∀ (i : Nat), i < m →
    ∀ (j : Nat), j + 1 < n →
      (grid[i]!)[j]! ≥ (grid[i]!)[j + 1]!

-- Helper: column-wise non-increasing order
-- For each column j and adjacent rows i and i+1: grid[i][j] ≥ grid[i+1][j]
public def ColWiseNonIncreasing (grid : Array (Array Int)) : Prop :=
  let m := grid.size
  let n := numCols grid
  ∀ (i : Nat), i + 1 < m →
    ∀ (j : Nat), j < n →
      (grid[i]!)[j]! ≥ (grid[i + 1]!)[j]!

-- Helper: mathematical count of negative entries (as a sum over bounded indices)
public def negCount (grid : Array (Array Int)) : Nat :=
  let m := grid.size
  let n := numCols grid
  (Finset.range m).sum (fun i =>
    (Finset.range n).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0))

-- Preconditions
-- 1) grid is a nonempty rectangular matrix
-- 2) grid is sorted non-increasing in each row and each column
public def precondition (grid : Array (Array Int)) : Prop :=
  Rectangular grid ∧
  RowWiseNonIncreasing grid ∧
  ColWiseNonIncreasing grid

-- Postcondition
-- The result equals the number of matrix entries that are negative.
public def postcondition (grid : Array (Array Int)) (result : Nat) : Prop :=
  result = negCount grid

end Specs

section Implementation

method countNegatives (grid : Array (Array Int))
  returns (result : Nat)
  requires valid: precondition grid
  ensures count_correct: postcondition grid result
do
  let m := grid.size
  let n := numCols grid

  let mut i : Nat := m
  let mut j : Nat := 0
  let mut cnt : Nat := 0

  while' scanning: i > 0 ∧ j < n
    invariant bounds: i ≤ m ∧ j ≤ n
    invariant inv_accounting:
      cnt +
        (Finset.range i).sum (fun r =>
          (Finset.range (n - j)).sum (fun t =>
            if (grid[r]!)[j + t]! < 0 then 1 else 0))
      = negCount grid
    decreasing remaining: i + (n - j)
  do
    let ii : Nat := i - 1
    let v : Int := (grid[ii]!)[j]!
    if is_neg: v < 0 then
      cnt := cnt + (n - j)
      i := ii
    else
      j := j + 1

  return cnt

end Implementation

section Proof

theorem col_le_of_le
    (grid : Array (Array Int))
    (hcol : ColWiseNonIncreasing grid)
    (j : Nat) (hj : j < numCols grid) :
    ∀ (d : Nat) (r : Nat), r + d < grid.size → grid[r + d]![j]! ≤ grid[r]![j]! := by
  intro d
  induction d with
  | zero =>
    intro r _
    exact le_refl _
  | succ d ih =>
    intro r hr
    have hr_step : r + d + 1 < grid.size := hr
    have hr_prev : r + d < grid.size := by omega
    have hstep : grid[r + d + 1]![j]! ≤ grid[r + d]![j]! :=
      hcol (r + d) hr_step j hj
    have hprev : grid[r + d]![j]! ≤ grid[r]![j]! :=
      ih r hr_prev
    exact le_trans hstep hprev

theorem row_le_of_le
    (grid : Array (Array Int))
    (hrow : RowWiseNonIncreasing grid)
    (r : Nat) (hr : r < grid.size) :
    ∀ (d : Nat) (c : Nat), c + d < numCols grid → grid[r]![c + d]! ≤ grid[r]![c]! := by
  intro d
  induction d with
  | zero =>
    intro c _
    exact le_refl _
  | succ d ih =>
    intro c hc
    have hc_step : c + d + 1 < numCols grid := hc
    have hc_prev : c + d < numCols grid := by omega
    have hstep : grid[r]![c + d + 1]! ≤ grid[r]![c + d]! :=
      hrow r hr (c + d) hc_step
    have hprev : grid[r]![c + d]! ≤ grid[r]![c]! :=
      ih c hc_prev
    exact le_trans hstep hprev

theorem exit_correct
    (grid : Array (Array Int))
    (cnt i j : Nat)
    (hinv : (cnt + ∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) = negCount grid)
    (hdone : ¬(0 < i ∧ j < numCols grid)) :
    postcondition grid cnt := by
  unfold postcondition
  have hrem : (∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) = 0 := by
    by_cases hi : i = 0
    · subst hi
      simp
    · have hj : numCols grid ≤ j := by
        omega
      have hsub : numCols grid - j = 0 := by omega
      simp [hsub]
  simpa [hrem] using hinv

theorem step_neg_correct
    (grid : Array (Array Int))
    (hrow : RowWiseNonIncreasing grid)
    (cnt i j : Nat)
    (hi_le : i ≤ grid.size)
    (hi_pos : 0 < i)
    (hj : j < numCols grid)
    (is_neg : grid[i - 1]![j]! < 0)
    (hinv : (cnt + ∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) = negCount grid) :
    (cnt + (numCols grid - j) +
      ∑ r ∈ Finset.range (i - 1), ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) =
    negCount grid := by
  let f : Nat → Nat := fun r =>
    ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0
  have hrow_all_neg : ∀ t ∈ Finset.range (numCols grid - j), grid[i - 1]![j + t]! < 0 := by
    intro t ht
    have ht_lt : t < numCols grid - j := Finset.mem_range.mp ht
    have hle : grid[i - 1]![j + t]! ≤ grid[i - 1]![j]! :=
      row_le_of_le grid hrow (i - 1) (by omega) t j (by omega)
    exact lt_of_le_of_lt hle is_neg
  have hrow_term : ∀ t ∈ Finset.range (numCols grid - j), (if grid[i - 1]![j + t]! < 0 then 1 else 0) = 1 := by
    intro t ht
    simp [hrow_all_neg t ht]
  have hf_pred : f (i - 1) = numCols grid - j := by
    dsimp [f]
    rw [Finset.sum_congr rfl hrow_term]
    simp
  have hi_eq : i = (i - 1) + 1 := by omega
  have hsum_split : (∑ r ∈ Finset.range i, f r) = (∑ r ∈ Finset.range (i - 1), f r) + (numCols grid - j) := by
    conv_lhs => rw [hi_eq]
    rw [Finset.sum_range_succ f (i - 1), hf_pred]
  have hinv' : cnt + (∑ r ∈ Finset.range i, f r) = negCount grid := hinv
  rw [hsum_split] at hinv'
  dsimp [f] at hinv'
  omega

theorem step_nonneg_correct
    (grid : Array (Array Int))
    (hcol : ColWiseNonIncreasing grid)
    (cnt i j : Nat)
    (hi_le : i ≤ grid.size)
    (hi_pos : 0 < i)
    (hj : j < numCols grid)
    (is_nonneg : ¬grid[i - 1]![j]! < 0)
    (hinv : (cnt + ∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) = negCount grid) :
    (cnt +
      ∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - (j + 1)), if grid[r]![j + 1 + t]! < 0 then 1 else 0) =
    negCount grid := by
  have hj_sub : numCols grid - j = (numCols grid - (j + 1)) + 1 := by omega
  have hrow_eq : ∀ r ∈ Finset.range i,
      (∑ t ∈ Finset.range (numCols grid - (j + 1)), if grid[r]![j + 1 + t]! < 0 then 1 else 0) =
      (∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) := by
    intro r hr
    have hr_lt : r < i := Finset.mem_range.mp hr
    have hd : r + ((i - 1) - r) = i - 1 := by omega
    have hle_col : grid[i - 1]![j]! ≤ grid[r]![j]! := by
      have h := col_le_of_le grid hcol j hj ((i - 1) - r) r (by omega)
      rwa [hd] at h
    have hr_nonneg : ¬grid[r]![j]! < 0 := by
      intro hlt
      have : grid[i - 1]![j]! < 0 := lt_of_le_of_lt hle_col hlt
      exact is_nonneg this
    let g : Nat → Nat := fun t => if grid[r]![j + t]! < 0 then 1 else 0
    have hg0 : g 0 = 0 := by
      dsimp [g]
      simp [hr_nonneg]
    have hsplit : (∑ t ∈ Finset.range ((numCols grid - (j + 1)) + 1), g t) =
        (∑ t ∈ Finset.range (numCols grid - (j + 1)), g (t + 1)) + g 0 :=
      Finset.sum_range_succ' g (numCols grid - (j + 1))
    have hg_succ : (∑ t ∈ Finset.range (numCols grid - (j + 1)), g (t + 1)) =
        ∑ t ∈ Finset.range (numCols grid - (j + 1)), if grid[r]![j + 1 + t]! < 0 then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro t _
      dsimp [g]
      have : j + (t + 1) = j + 1 + t := by omega
      rw [this]
    have hsum_g : (∑ t ∈ Finset.range (numCols grid - j), g t) =
        ∑ t ∈ Finset.range (numCols grid - (j + 1)), if grid[r]![j + 1 + t]! < 0 then 1 else 0 := by
      conv_lhs => rw [hj_sub]
      rw [hsplit, hg0, Nat.add_zero, hg_succ]
    exact hsum_g.symm
  have hsum_all :
      (∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - (j + 1)), if grid[r]![j + 1 + t]! < 0 then 1 else 0) =
      (∑ r ∈ Finset.range i, ∑ t ∈ Finset.range (numCols grid - j), if grid[r]![j + t]! < 0 then 1 else 0) :=
    Finset.sum_congr rfl hrow_eq
  rw [hsum_all]
  exact hinv

prove_correct countNegatives by
  velvet_vcgen [countNegatives, postcondition] with try finish
  case inv_accounting =>
    simp [negCount]
  case count_correct =>
    rename_i grid
    exact exit_correct grid cnt i j inv_accounting h_done_with
  case inv_accounting =>
    rename_i grid
    exact step_neg_correct grid valid.2.1 cnt i j bounds.1 scanning.1 scanning.2 is_neg inv_accounting
  case inv_accounting =>
    rename_i grid
    exact step_nonneg_correct grid valid.2.2 cnt i j bounds.1 scanning.1 scanning.2 is_neg inv_accounting

end Proof

end CountNegativeNumbersInASortedMatrix
