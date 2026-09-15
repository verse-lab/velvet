module

public import Velvet
public meta import Velvet

open Std.Internal.Do

namespace SimplestSort

/-!
# "I Can't Believe It Can Sort" (https://arxiv.org/pdf/2110.01111)

Verified implementation of Stanley P. Y. Fung's algorithm:
```lean
for i in 0..n do
  for j in 0..n do
    if a[i] < a[j] then
      swap(a[i], a[j])
```
-/

@[grind, simp]
public def cnt (arr : Array Int) (x : Int) : Nat := arr.toList.count x

@[grind, simp]
public def sameElems (a b : Array Int) : Prop := ∀ x, cnt a x = cnt b x

@[grind, simp]
public def SortedUpTo (arr : Array Int) (n : Nat) : Prop :=
  ∀ i j, i ≤ j → j < n → arr[i]! ≤ arr[j]!

@[grind =, simp]
public theorem getElem!_swap (a : Array Int) (i j k : Nat) (hi : i < a.size) (hj : j < a.size) :
  ((a.set! i a[j]!).set! j a[i]!)[k]! =
    if k = j then a[i]! else if k = i then a[j]! else a[k]! := by
  grind

set_option maxHeartbeats 10000000

set_option velvet.semantics.termination "total" in
method simplestSort (arr : Array Int)
  returns (res : Array Int)
  requires size_pos: arr.size > 0
  ensures sorted: SortedUpTo res res.size
  ensures elems_same: sameElems res arr
do
  let mut res := arr
  let mut i : Nat := 0
  while' outer_loop: i < res.size
    invariant sz_inv: res.size = arr.size
    invariant i_le: i ≤ res.size
    invariant sorted_prefix: SortedUpTo res i
    invariant max_prefix: ∀ m, m < res.size → (i = 0 ∨ res[m]! ≤ res[i - 1]!)
    invariant elems_inv: sameElems res arr
    decreasing by_i: res.size - i
  do
    let mut j : Nat := 0
    while' inner_loop: j < res.size
      invariant inner_sz: res.size = arr.size
      invariant j_le: j ≤ res.size
      invariant inv_i0: i = 0 → ∀ m, m < j → res[m]! ≤ res[0]!
      invariant inv_left_sorted: ∀ u v, u ≤ v → v < min i j → res[u]! ≤ res[v]!
      invariant inv_right_sorted: j < i → ∀ u v, j ≤ u → u ≤ v → v < i → res[u]! ≤ res[v]!
      invariant inv_left_le_i: j < i → ∀ u, u < j → res[u]! ≤ res[i]!
      invariant inv_left_le_j: j < i → ∀ u, u < j → res[u]! ≤ res[j]!
      invariant inv_max_prev: (i > 0 ∧ j < i) → ∀ m, m < res.size → res[m]! ≤ res[i - 1]!
      invariant inv_sorted_done: (i > 0 ∧ j ≥ i) → SortedUpTo res (i + 1)
      invariant inv_max_done: (i > 0 ∧ j ≥ i) → ∀ m, m < res.size → res[m]! ≤ res[i]!
      invariant inner_elems: sameElems res arr
      decreasing by_j: res.size - j
    do
      if res[i]! < res[j]! then
        let tmp := res[i]!
        res := res.set! i res[j]!
        res := res.set! j tmp
      j := j + 1
    i := i + 1
  return res

#eval (simplestSort #[11,21,12,15, 10])

prove_correct simplestSort by
  velvet_vcgen [simplestSort] with try finish
  intro hj1 u hu
  have hj_step := inv_right_sorted (by grind) j (j + 1) (by grind) (by grind) hj1
  grind
  intro hj1 u hk
  have hj_step := inv_right_sorted (by grind) j (j + 1) (by grind) (by grind) hj1
  grind

end SimplestSort
