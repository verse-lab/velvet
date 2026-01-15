/-
Velvet Utils
============

Helper functions and definitions for Velvet programs.
Extracted from various example files in VelvetExamples/.

Contents:
- Array multiset operations
- Array element swapping operations
-/

import Mathlib.Data.Multiset.Basic

/-! ## Multiset Operations for Arrays -/

/-- Convert an array to a multiset representation -/
def arrayToMultiset (a: Array Int) :=
  (Multiset.ofList a.toList)

/-! ## Array Element Swapping -/

/-- Swap two elements in an array at given indices -/
@[reducible]
def elemSwap! (arr: Array Int) (idx1 idx2 : Nat) :=
  let arr' := Array.set! arr idx1 (arr[idx2]!)
  let arr'' := Array.set! arr' idx2 (arr[idx1]!)
  arr''
