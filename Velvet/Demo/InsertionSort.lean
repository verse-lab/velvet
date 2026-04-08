----------------------------------------------------
-- Example 1: Velvet basics
----------------------------------------------------

import Velvet.Std
import CaseStudies.TestingUtil

-- (2) Insertion sort
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

attribute [grind] Array.multiset_swap


set_option loom.semantics.termination "partial"
-- set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

--partial correctness version of insertionSort
-- uncomment termination measures for total correctness
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures ∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arrOld.size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arrOld.toMultiset
    -- decreasing arr.size - n
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arrOld.size
      invariant mind ≤ n
      invariant ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arrOld.toMultiset
      -- decreasing mind
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1 -- try commenting this out for termination
    return

-- Let's test this stuff
extract_program_for insertionSort

-- Determinising the execution
-- #print insertionSortExec

-- Prove decidability as we need to check them
prove_precondition_decidable_for insertionSort
-- #print insertionSortPreDecidable
prove_postcondition_decidable_for insertionSort
derive_tester_for insertionSort

-- (2.1) Doing simple testing
-- See here where the postcondition is violated

run_elab do
  -- Generate random arrays
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

-- (2.2) This just works

set_option maxHeartbeats 1000000

prove_correct insertionSort by
  loom_solve_async!

end insertionSort
