import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

attribute [solverHint] TArray.get_set TArray.size_set

section insertionSort

/-

Dafny code below for reference

method insertionSort(arr: array<int>)
  modifies arr
  ensures forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures multiset(arr[..]) == old(multiset(arr[..]))
{
  if arr.Length <= 1 {
    return;
  }
  var n := 1;
  while n != arr.Length
  invariant 0 <= n <= arr.Length
  invariant forall i, j :: 0 <= i < j <= n - 1 ==> arr[i] <= arr[j]
  invariant multiset(arr[..]) == old(multiset(arr[..]))
  {
    var mind := n;
    while mind != 0
    invariant 0 <= mind <= n
    invariant multiset(arr[..]) == old(multiset(arr[..]))
    invariant forall i, j :: 0 <= i < j <= n && (j != mind)==> arr[i] <= arr[j]
    {
      if arr[mind] <= arr[mind - 1] {
        arr[mind], arr[mind - 1] := arr[mind - 1], arr[mind];
      }
      mind := mind - 1;
    }
    n := n + 1;
  }
}
-/

-- set_option trace.profiler true
attribute [local solverHint] Array.multiset_swap
attribute [solverHint] Array.size_set_c Array.get_set_c

--partial correctness version of insertionSort
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i]! ≤ arrNew[j]!
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := arr.size
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant toMultiset arr = toMultiset arr₀
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant toMultiset arr = toMultiset arr₀
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return

extract_program_for insertionSort
prove_precondition_decidable_for insertionSort
prove_postcondition_decidable_for insertionSort by
  (exact (decidable_by_nat_upperbound [(size arr), (size arr)]))
derive_tester_for insertionSort

-- doing simple testing
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

set_option maxHeartbeats 1000000

prove_correct insertionSort by
  dsimp [insertionSort]
  loom_solve

end insertionSort

section squareRoot

--partial correctness version of square root
method sqrt (x: ℕ) return (res: ℕ)
  require x > 8
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      done_with x < i * i
      do
        i := i + 1
      return i - 1
prove_correct sqrt by
  dsimp [sqrt]
  loom_solve!

end squareRoot
