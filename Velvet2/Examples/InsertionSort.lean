import Velvet2.Syntax
import Velvet2.VCGen.Frontend


open Std.Internal.Do

def cnt (arr : Array Int) (x : Int) : Nat := arr.toList.count x

def sameElems (a b : Array Int) : Prop := ∀ x, cnt a x = cnt b x

def SortedUpTo (arr : Array Int) (n : Nat) : Prop :=
  ∀ i j, i ≤ j → j < n → arr[i]! ≤ arr[j]!

theorem count_set_swap {l : List Int} {k : Nat} (h : k + 2 ≤ l.length) :
    ∀ y, List.count y ((l.set (k + 1) l[k]!).set k l[k + 1]!) = List.count y l := by
  induction k generalizing l with
  | zero =>
      cases l with
      | nil => simp at h
      | cons u t =>
          cases t with
          | nil => simp at h
          | cons v t =>
              intro y
              simp only [List.getElem!_cons_zero, List.getElem!_cons_succ,
                List.set_cons_zero, List.set_cons_succ]
              have hpair : ∀ a b : Int,
                  List.count y [a, b] = List.count y [b, a] := by
                intro a b
                by_cases ha : a = y <;> by_cases hb : b = y <;>
                  simp only [ha, hb, List.count_cons, List.count_singleton] <;> omega
              have hL : List.count y (v :: u :: t)
                  = List.count y [v, u] + List.count y t := by
                rw [show (v :: u :: t) = [v, u] ++ t from rfl, List.count_append]
              have hR : List.count y (u :: v :: t)
                  = List.count y [u, v] + List.count y t := by
                rw [show (u :: v :: t) = [u, v] ++ t from rfl, List.count_append]
              rw [hL, hR, hpair v u]
  | succ m ih =>
      cases l with
      | nil => simp at h
      | cons a t =>
          have h2 : m + 2 ≤ t.length := by simpa using h
          intro y
          have hred :
              List.count y
                (((a :: t).set (m + 1 + 1) (a :: t)[m + 1]!).set (m + 1)
                  (a :: t)[m + 1 + 1]!) =
              List.count y (a :: ((t.set (m + 1) t[m]!).set m t[m + 1]!)) := by
            simp only [List.getElem!_cons_succ, List.set_cons_succ]
          rw [hred, List.count_cons, List.count_cons]
          have hic := ih (l := t) h2 y
          split <;> omega

theorem cnt_swap {arr : Array Int} {k : Nat} (h : k + 2 ≤ arr.size) :
    ∀ y, cnt ((arr.set! (k + 1) arr[k]!).set! k arr[k + 1]!) y = cnt arr y := by
  intro y
  show List.count y ((arr.set! (k + 1) arr[k]!).set! k arr[k + 1]!).toList =
    List.count y arr.toList
  rw [Array.toList_set!, Array.toList_set!]
  have h := count_set_swap h y
  rw [Array.getElem!_toList, Array.getElem!_toList] at h
  exact h


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
  vcgen_ [insertionSort] simplifying_assumptions with try finish
  case sorted_prefix =>
    rename_i arr
    intro i j _ hj
    have hii : i = j := by omega
    subst hii
    omega
  case elems_inv =>
    rename_i arr
    exact fun _ => rfl
  case inner_sorted =>
    rename_i arr res n
    intro i j hij hj hn
    exact sorted_prefix i j hij (by omega)
  case sorted_prefix =>
    rename_i arr res n ain mind
    have hm0 : mind = 0 := by
      by_cases hm : mind = 0
      · exact hm
      · exact absurd hm h_done_with
    intro i j hij hjlt
    by_cases hj0 : j = 0
    · have hi0 : i = 0 := by omega
      subst hi0
      subst hj0
      omega
    · exact inner_sorted i j hij (by omega) (by omega)
  case inner_elems =>
    rename_i arr res n ain mind
    intro x
    have hidx : mind - 1 + 1 = mind := by omega
    have h := cnt_swap (arr := ain) (k := mind - 1) (by omega) x
    rw [hidx] at h
    exact h.trans (inner_elems x)
  case inner_sorted =>
    rename_i arr res n ain mind
    intro i j hij hjlt hne
    by_cases hjm : j = mind - 1
    · subst hjm
      exact inner_sorted i (mind - 1) (by omega) (by omega) (by omega)
    · by_cases hjm2 : j = mind
      · subst hjm2
        by_cases him : i = j
        · subst him
          omega
        · have hchain := inner_sorted i (j - 1) (by omega) (by omega) (by omega)
          have hg := if_cond
          omega
      · exact inner_sorted i j hij hjlt (by omega)
