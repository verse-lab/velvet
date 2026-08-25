import Velvet

namespace Velvet.Examples.HypNaming

open Std.WP

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
  velvet_vcgen [maxOf]
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
  velvet_vcgen [depMaxOf]
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
  velvet_vcgen [nestedIfs]
  · grind
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
  velvet_vcgen [headOr]
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
  velvet_vcgen [headOrH]
  · grind
  · grind

/- `bif` (bool `if`) naming -/
method bifExample (b : Bool) (x : Nat) returns (res : Nat)
  ensures (b = true → res = x + 1) ∧ (b = false → res = x)
do
  bif b then
    return x + 1
  else
    return x

prove_correct bifExample by
  velvet_vcgen [bifExample]
  · grind
  · grind

end Velvet.Examples.HypNaming
