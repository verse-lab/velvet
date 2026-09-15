module

public import Velvet
public meta import Velvet

open Std.Internal.Do

@[grind →]
public theorem adjacent_to_global_sorted {a : Array Int}
    (h_adjacent : ∀ k, k < a.size - 1 → a[k]! ≤ a[k + 1]!) :
    ∀ i j, i < j → j < a.size → a[i]! ≤ a[j]! := by
  intro i j
  induction j with
  | zero => intro h _; omega
  | succ j ih =>
    intro hij hjlt
    by_cases h : i = j
    · subst h
      exact h_adjacent _ (by omega)
    · have h1 := ih (by omega) (by omega)
      have h2 := h_adjacent j (by omega)
      omega

@[grind →]
public theorem not_sorted_of_inversion {a : Array Int} {k : Nat}
    (hk : k < a.size - 1) (hinv : a[k + 1]! < a[k]!) :
    ¬ (∀ i j, i < j → j < a.size → a[i]! ≤ a[j]!) := by
  intro h
  have := h k (k + 1) (by omega) (by omega)
  omega

method isSorted (a : Array Int)
  returns (sorted : Bool)
  requires size_gt_0: a.size > 0
  ensures sorted_iff: sorted = true ↔
    (∀ i j, i < j → j < a.size → a[i]! ≤ a[j]!)
do
  let mut sorted := true
  let mut i : Nat := 0
  while' loop_cond: i < a.size - 1 ∧ sorted = true
    invariant idx_bounded: i ≤ a.size - 1
    invariant ok_prefix: sorted = true → (∀ k, k < i → a[k]! ≤ a[k + 1]!)
    invariant found_inversion: sorted = false → ∃ k, k < a.size - 1 ∧ a[k]! > a[k + 1]!
    decreasing by_remaining: a.size - 1 - i
    done_with done: i = a.size - 1 ∨ sorted = false
  do
    if a[i]! > a[i + 1]! then
      sorted := false
    else
      sorted := sorted
    i := i + 1
  return sorted

prove_correct isSorted by
  velvet_vcgen [isSorted] with finish
