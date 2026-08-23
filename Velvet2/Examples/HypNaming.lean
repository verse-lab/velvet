import Velvet2.Syntax
import Velvet2.VCGen.Frontend

namespace Velvet2.Examples.HypNaming

open Std.Internal.Do

/- Keep SymM's maximal-sharing assertions enabled for these regression examples. -/
set_option sym.debug true

/- `if` naming -/
method maxOf (a : Nat) (b : Nat) returns (res : Nat)
  ensures a ≤ res ∧ b ≤ res ∧ (a = res ∨ b = res)
do
  if a < b then
    return b
  return a

prove_correct maxOf by
  vcgen_ [maxOf]
  · grind
  · grind
/- dependent `if` naming -/
method depMaxOf (a : Nat) (b : Nat) returns (res : Nat)
  ensures a ≤ res ∧ b ≤ res ∧ (a = res ∨ b = res)
do
  if hab : a < b then
    return b
  return a

prove_correct depMaxOf by
  vcgen_ [depMaxOf]
  · grind
  · grind

/- nested `if`s -/
method nestedIfs (x : Nat) returns (res : Nat)
  ensures res ≤ 10
do
  if x < 10 then
    if x < 5 then
      return x
    return x
  return 10

prove_correct nestedIfs by
  vcgen_ [nestedIfs]
  · grind
  · grind

/- `match` on a List -/
method headOr (xs : List Nat) returns (res : Nat)
  ensures res = xs.headD 0
do
  match xs with
  | [] => return 0
  | y :: rest => return y

prove_correct headOr by
  vcgen_ [headOr]
  · grind
  · grind

/- `match` with named equation -/
method headOrH (xs : List Nat) returns (res : Nat)
  requires precond: True
  ensures postcond: res = xs.headD 0
do
  match hx : xs with
  | [] => return 0
  | y :: _ => return y

prove_correct headOrH by
  vcgen_ [headOrH]
  · grind
  · grind

end Velvet2.Examples.HypNaming
