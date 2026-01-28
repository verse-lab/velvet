import CaseStudies.Velvet.Std
-- import CaseStudies.Velvet.Utils
-- import CaseStudies.Velvet.UtilsLemmas
-- import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findEvenNumbers: Extract even numbers from an array of integers, preserving order.
-/

@[grind]
def isEvenInt (x : Int) : Bool :=
  x % 2 = 0

@[grind]
def Array.Sublist (arr : Array Int) (sub : Array Int) : Prop :=
  ∃ indices : Array Nat,
    indices.size = sub.size ∧
    (∀ i, i < indices.size → indices[i]! < arr.size) ∧
    (∀ i, i < indices.size → sub[i]! = arr[indices[i]!]!) ∧
    (∀ i j, i < j → j < indices.size → indices[i]! < indices[j]!)
-- section Impl
method findEvenNumbers (arr : Array Int)
  return (result : Array Int)
  ensures arr.Sublist result
  ensures ∀ x, x ∈ result → isEvenInt x = true
  ensures ∀ x, isEvenInt x = true → result.count x = arr.count x
  ensures ∀ x, isEvenInt x = false → result.count x = 0
  do
  let mut result : Array Int := #[]
  let mut indices : Array Nat := #[]
  let mut i : Nat := 0
  while i < arr.size
    invariant "inv_i_bounds" (i ≤ arr.size)
    invariant "inv_all_even" (∀ x, x ∈ result → isEvenInt x = true)
    invariant "inv_count_odds_zero" (∀ x, isEvenInt x = false → result.count x = 0)
    invariant "inv_count_evens_prefix" (∀ x, isEvenInt x = true → result.count x = (arr.take i).count x)
    invariant "inv_indices_size" (indices.size = result.size)
    invariant "inv_indices_index" (∀ k, k < indices.size → indices[k]! < i)
    invariant "inv_indices_arr_bounds" (∀ k, k < indices.size → indices[k]! < arr.size)
    invariant "inv_indices_result_bounds" (∀ k, k < indices.size → result[k]! = arr[indices[k]!]!)
    invariant "inv_indices_order" (∀ k j, k < j → j < indices.size → indices[k]! < indices[j]!)
    done_with i = arr.size
  do
    let x := arr[i]!
    if isEvenInt x = true then
      result := result.push x
      indices := indices.push i
    i := i + 1
  return result
-- end Impl

section Proof
set_option maxHeartbeats 10000000

@[grind]
theorem count_take [DecidableEq α] [Inhabited α] {a : α} {xs : Array α} :
  n < xs.size →
  (xs.take (n + 1)).count a = if xs[n]! = a then (xs.take n).count a + 1 else (xs.take n).count a := by
  intro; grind [Array.extract_succ_right]

set_option trace.profiler true

attribute [grind] Array.take_size

prove_correct findEvenNumbers by
  loom_solve


end Proof
