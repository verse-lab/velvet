module

public import Velvet
public meta import Velvet

open Std.Internal.Do

@[grind]
public def isMax (mx : Int) (arr : Array Int) : Prop :=
  ∀ i, (h : i < arr.size) → mx ≥ arr[i]'h

method maxElem (arr : Array Int)
  returns (res : Int)
  requires size_gt_0: arr.size > 0
  ensures max_is: isMax res arr
do
  let mut i : Nat := 0
  let mut mx := arr[0]!
  i := i + 1
  while' loop_cond: i < arr.size
    invariant idx_bounded: i ≤ arr.size
    invariant prefix_max: ∀ j, j < i → mx ≥ arr[j]!
    decreasing loop_var_size : arr.size - i
    done_with scanned_all: i = arr.size
  do
    if arr[i]! > mx then
      mx := arr[i]!
    else
      mx := mx
    i := i + 1
  return mx

prove_correct maxElem by
  velvet_vcgen [maxElem] with finish

