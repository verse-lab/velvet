module

public import Velvet
public meta import Velvet

open Std.Internal.Do

@[grind]
public def cnt (arr : Array Int) (x : Int) : Nat := arr.toList.count x

@[grind]
public def sameElems (a b : Array Int) : Prop := ∀ x, cnt a x = cnt b x

@[grind]
public def SortedUpTo (arr : Array Int) (n : Nat) : Prop :=
  ∀ i j, i ≤ j → j < n → arr[i]! ≤ arr[j]!


set_option maxHeartbeats 10000000 in
set_option velvet.semantics.termination "total" in
method insertionSort (arr : Array Int)
  returns (res : Array Int)
  requires size_pos: arr.size > 0
  ensures sorted: SortedUpTo res res.size
  ensures elems_same: sameElems res arr
do
  let mut res := arr
  let mut n : Nat := 1
  while' loop_cond: n ≠ res.size
    invariant sz_inv: res.size = arr.size
    invariant n_le: n ≤ res.size
    invariant sorted_prefix: SortedUpTo res n
    invariant elems_inv: sameElems res arr
    decreasing by_size: res.size - n
  do
    let mut mind := n
    while' inner_cond: mind ≠ 0
      invariant inner_sz: res.size = arr.size
      invariant mind_le: mind ≤ n
      invariant inner_sorted: ∀ i j, i ≤ j → j < n + 1 → j ≠ mind → res[i]! ≤ res[j]!
      invariant inner_elems: sameElems res arr
      decreasing by_mind: mind
    do
      if res[mind]! < res[mind - 1]! then
        let tmp := res[mind]!
        res := res.set! mind res[mind - 1]!
        res := res.set! (mind - 1) tmp
      else
        res := res
      mind := mind - 1
    n := n + 1
  return res

prove_correct insertionSort by
  velvet_vcgen [insertionSort] with try finish
  case inner_sorted =>
    intro i j hij hj_bound hj
    by_cases hj_m : j = mind
    · subst hj_m
      rcases Nat.lt_or_eq_of_le hij with hi | rfl
      · exact Int.le_trans (inner_sorted i (j - 1) (by omega) (by omega) (by omega)) (by omega)
      · grind
    · exact inner_sorted i j hij hj_bound hj_m
