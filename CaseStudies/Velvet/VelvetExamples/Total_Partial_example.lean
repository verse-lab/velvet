import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import CaseStudies.Velvet.Std

attribute [grind] Array.multiset_swap

section

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

method insertionSort_part
  (mut arr: Array Int) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let arr₀ := arr
    let arr_size := arr.size
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant n ≤ arr.size
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
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 1000000 in
prove_correct insertionSort_part by
  loom_solve!

end

section

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

method insertionSort_termination
  (mut arr: Array Int) return (u: Unit)
  ensures True
  do
    let arr₀ := arr
    let arr_size := arr.size
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant n ≤ arr.size
      decreasing arr.size - n
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        decreasing mind
        do
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

prove_correct insertionSort_termination by
  loom_solve!
end

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

set_option loom.linter.errors false
set_option loom.linter.warnings false


method insertionSort_result
  (mut arr: Array Int) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let arr₀ := arr
    let arr_size := arr.size
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size do
        let mut mind := n
        while mind ≠ 0 do
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

prove_correct insertionSort_result by
  have triple_termination := insertionSort_termination_correct arrOld
  have triple_res := insertionSort_part_correct arrOld
  -- applying lemma about separation of termination proof and correctness proof
  exact VelvetM.total_decompose_triple
    (insertionSort_termination arrOld) (insertionSort_part arrOld) (insertionSort_result arrOld)
    (eqx := by rfl) (eqy := by rfl)
    triple_termination
    triple_res
