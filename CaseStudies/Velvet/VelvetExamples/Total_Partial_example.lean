import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Basic
import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std

open Lean.Elab.Term.DoNames

attribute [grind] Array.multiset_swap

macro_rules
  | `(tactic|loom_solver) =>
    `(tactic|try grind (splits := 40))

--we prove invariants in partial correctness
open PartialCorrectness DemonicChoice in
method insertionSort_part
  (mut arr: Array Int) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arrNew[i]! ≤ arrNew[j]!
  ensures arr.toMultiset = arrNew.toMultiset
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
open PartialCorrectness DemonicChoice in
prove_correct insertionSort_part by
  loom_solve!

--we prove termination in total correctness
open TotalCorrectness DemonicChoice in
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
open TotalCorrectness DemonicChoice in
prove_correct insertionSort_termination by
  loom_solve!

--we prove the postcondition just by combination of the two triples above
open TotalCorrectness DemonicChoice in
method insertionSort_result
  (mut arr: Array Int) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arrNew[i]! ≤ arrNew[j]!
  ensures arr.toMultiset = arrNew.toMultiset
  do
    let arr₀ := arr
    let arr_size := arr.size
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant True
      do
        let mut mind := n
        while mind ≠ 0
        invariant True
        do
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return
open TotalCorrectness DemonicChoice in
prove_correct insertionSort_result by
  have triple_termination := insertionSort_termination_correct arr
  have triple_res := insertionSort_part_correct arr
  -- applying lemma about separation of termination proof and correctness proof
  exact VelvetM.total_decompose_triple
    (insertionSort_termination arr) (insertionSort_part arr) (insertionSort_result arr)
    (eqx := by rfl) (eqy := by rfl)
    triple_termination
    triple_res
