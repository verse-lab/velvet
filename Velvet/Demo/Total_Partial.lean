-------------------------------------------------------
-- Example 3: Combining Total and Partial Correctness
-------------------------------------------------------

-- This file illustrates that total correctness can be established by proving its
-- two constituents *separately* and then gluing them together:
--
--   total correctness  =  partial correctness  +  termination
--
-- We verify insertion sort three times:
--   • `insertionSort_part`        — WHAT it computes, *if* it terminates (partial).
--   • `insertionSort_termination` — THAT it terminates, ignoring the result.
--   • `insertionSort_result`      — the full total-correctness claim, obtained by
--                                   composing the two proofs above (no re-proving).
--
-- The payoff: each half uses only the machinery it needs — invariants for the
-- functional spec, ranking functions for termination — so neither proof is
-- burdened by the other's obligations.

import Velvet.Std

attribute [grind] Array.multiset_swap

section

-- Part A — PARTIAL correctness.
-- Under "partial" termination semantics the loops carry no ranking function: we
-- promise the postcondition only *conditionally on* termination. The invariants
-- capture the full functional spec (sortedness of the prefix + permutation of the
-- input), which is exactly what carries over once termination is known.
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method insertionSort_part
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let arr₀ := arr
    let arr_size := arr.size
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arr₀.toMultiset
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1 -- try commenting this out for termination
    return

set_option maxHeartbeats 1000000 in
prove_correct insertionSort_part by
  loom_solve!

end

section

-- Part B — TERMINATION only.
-- Under "total" semantics every loop must exhibit a `decreasing` ranking function.
-- The postcondition is the trivial `True`: we deliberately say *nothing* about the
-- result here, so the proof is only about the ranking measures shrinking. The
-- functional invariants are dropped — they are Part A's job.
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

method insertionSort_termination
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures True
  do
    let mut n := 1
    let arr_size := arr.size
    while n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    decreasing arr.size - n
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      decreasing mind
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1 -- try commenting this out for termination
    return

prove_correct insertionSort_termination by
  loom_solve!
end

-- Part C — TOTAL correctness, by composition.
-- Same program, now with both the full functional spec *and* "total" semantics.
-- Crucially, we do not re-verify the loops: the proof below assembles the total
-- result purely from Part A (partial correctness) and Part B (termination).
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

set_option loom.linter.errors false
set_option loom.linter.warnings false


method insertionSort_result
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size do
      let mut mind := n
      while mind ≠ 0 do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1 -- try commenting this out for termination
    return

prove_correct insertionSort_result by
  -- Pull in the two proofs established separately above...
  have triple_termination := insertionSort_termination_correct arrOld -- Part B: it terminates
  have triple_res := insertionSort_part_correct arrOld                -- Part A: what it computes
  -- ...and glue them: `total_decompose_triple` is the lemma stating that a
  -- termination proof plus a partial-correctness proof yield total correctness.
  exact VelvetM.total_decompose_triple
    (insertionSort_termination arrOld) (insertionSort_part arrOld) (insertionSort_result arrOld)
    (eqx := by rfl) (eqy := by rfl)
    triple_termination
    triple_res
