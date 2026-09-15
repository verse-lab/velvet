module

public import Velvet
public meta import Velvet

open Std.Internal.Do

set_option velvet.semantics.termination "partial" in
method rec lengthMatch (n : Nat) (l : List Nat)
  returns (res : Nat)
  ensures res_eq: res = l.length
do
  match l, n with
  | [], _ => pure 0
  | _ :: k, _ =>
    let b ← lengthMatch n k
    pure b.succ

prove_correct lengthMatch by
  intro n l
  induction l with
  | nil => rw [lengthMatch.eq_1]; velvet_vcgen with finish
  | cons head tail ih => rw [lengthMatch.eq_2]; velvet_vcgen [ih] with finish

set_option velvet.semantics.termination "partial" in
method matchTriple (a : Nat) (b : Nat) (c : Nat)
  returns (res : Nat)
  ensures res_gt: res > 9
do
  match a, b, c with
  | 2, 3, 4 => pure 10
  | _, _, _ => pure (a + b + c + 10)

prove_correct matchTriple by
  velvet_vcgen [matchTriple] with try finish
