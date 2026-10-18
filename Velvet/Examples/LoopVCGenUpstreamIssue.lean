module

public import Std.Tactic.Do
public import Std.WP

open Std.WP

/-!
# Early exits from loops with Lean's `vcgen`

Lean's own `do` loops and `vcgen`, without Velvet: `break` works, but an early `return` from a
loop loses what held at the `return`, or needs an invariant over the loop's internal state. Each
section pins the goals `vcgen` leaves. Velvet's `velvet_vcgen` proves the same programs (see
`LoopControl.lean`).

`sym.debug` is off where the loop state is a tuple: Lean's own `splitProdBinder` fails its sharing
checks on it (see `SplitProdBinder.lean`).
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace Velvet.Examples.LoopVCGenUpstreamIssue

/-! ## `while` with `break`: works

The exit invariant (`inv true s`) is asked for at the `break`, where it holds. -/

def breakAtFive (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n
    invariant _ => i ≤ n
    decreasing n - i
  do
    if i = 5 then break
    i := i + 1
  return i

theorem breakAtFive_spec (n : Nat) :
    Triple (breakAtFive n) True (fun r => r ≤ n) estack⟨⟩ := by
  vcgen [breakAtFive] with finish

/-! ## `while` with `return`: what held at the `return` is lost

A `return` stores the value in the loop state's return slot and leaves the loop like a `break`, so
it only has to establish the exit invariant. The inline invariant cannot mention the return slot,
so after the loop only `(a✝², i).fst = some a✝` is known about the returned value: `xs[i]! = 0`,
which held at the `return`, is gone. -/

def findZero (xs : Array Nat) : Except String Nat := do
  let mut i := 0
  while i < xs.size
    invariant _ => i ≤ xs.size
    decreasing xs.size - i
  do
    if xs[i]! = 0 then return i
    i := i + 1
  throw "no zero"

/--
error: unsolved goals
case vc2
xs : Array Nat
a✝² : Option Nat
i : Nat
a✝¹ : i ≤ xs.size
a✝ : Nat
x✝ : (a✝², i).fst = some a✝
⊢ a✝ < xs.size ∧ xs[a✝]! = 0
-/
#guard_msgs in
set_option sym.debug false in
theorem findZero_spec (xs : Array Nat) :
    Triple (findZero xs) True (fun r => r < xs.size ∧ xs[r]! = 0) (fun e => e = "no zero") := by
  vcgen [findZero] with try finish

/-! ## `while` with `return`, invariant over the whole loop state

Without the inline clauses, `vcgen` asks for a `WhileInvariant` and a `Variant` over the whole loop
state, return slot included. Such an invariant can say what a returned value satisfies, but the
step ranges over every state, returned or not (`a✝¹ : Option Nat`), and the goals keep
`WhileInvariant.mk`, `Variant.EvalsTo` and `Lean.Order.meet` unreduced. Here the normal exit
cannot be proved: nothing says the slot is empty while the loop runs. -/

def findZeroState (xs : Array Nat) : Except String Nat := do
  let mut i := 0
  while i < xs.size do
    if xs[i]! = 0 then return i
    i := i + 1
  throw "no zero"

/--
error: unsolved goals
case vc5
xs : Array Nat
a✝¹ : Option Nat
b✝ : Nat
mb✝ : (Variant.ofMeasure fun s => xs.size - s.snd).γ
a✝ :
  Lean.Order.meet ((Variant.ofMeasure fun s => xs.size - s.snd).EvalsTo (a✝¹, b✝) mb✝)
    (WhileInvariant.mk
      (fun x s =>
        match s with
        | (none, i) => i ≤ xs.size
        | (some r, snd) => r < xs.size ∧ xs[r]! = 0)
      false (a✝¹, b✝))
h✝ : ¬(a✝¹, b✝).snd < xs.size
⊢ WhileInvariant.mk
    (fun x s =>
      match s with
      | (none, i) => i ≤ xs.size
      | (some r, snd) => r < xs.size ∧ xs[r]! = 0)
    true (none, (a✝¹, b✝).snd)
-/
#guard_msgs in
set_option sym.debug false in
theorem findZeroState_spec (xs : Array Nat) :
    Triple (findZeroState xs) True (fun r => r < xs.size ∧ xs[r]! = 0)
      (fun e => e = "no zero") := by
  vcgen [findZeroState]
    invariants
    · WhileInvariant.mk fun _ s => match s with
        | (none, i) => i ≤ xs.size
        | (some r, _) => r < xs.size ∧ xs[r]! = 0
    · Variant.ofMeasure (Pred := Prop) (fun s : Option Nat × Nat => xs.size - s.2)
    with try finish

/-! ## `for` with `return`: an invariant over the whole loop state

A `for` loop has no inline invariant, so `vcgen` asks for one over the whole loop state,
`Option Nat × PUnit`: the return slot and an empty state. `Invariant.withEarlyReturnNewDo` builds
one from an invariant while iterating and a condition on a returned value, but the goals keep its
`Lean.Order.join`, `meet`, `iSup` and `ofProp` unreduced, and `finish` proves neither the
`return` nor the code after the loop. -/

def findZeroFor (xs : List Nat) : Except String Nat := do
  for x in xs do
    if x = 0 then return x
  throw "no zero"

/--
error: unsolved goals
case vc2
xs : List Nat
a✝² : Option Nat
b✝ : PUnit
a✝¹ :
  match (a✝², b✝) with
  | (x, b) =>
    Lean.Order.join (Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (x = none)) ((fun x x_1 x_2 => True) xs [] b))
      (Lean.Order.iSup fun r =>
        Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (x = some r ∧ [] = [])) ((fun r x => r = 0) r b))
a✝ : Nat
x✝ : (a✝², b✝).fst = some a✝
⊢ a✝ = 0

case vc3
xs pref✝ : List Nat
cur✝ : Nat
suff✝ : List Nat
_h✝ : xs = pref✝ ++ cur✝ :: suff✝
a✝¹ : Option Nat
b✝ : PUnit
a✝ :
  match (a✝¹, b✝) with
  | (x, b) =>
    Lean.Order.join
      (Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (x = none)) ((fun x x_1 x_2 => True) pref✝ (cur✝ :: suff✝) b))
      (Lean.Order.iSup fun r =>
        Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (x = some r ∧ cur✝ :: suff✝ = [])) ((fun r x => r = 0) r b))
h✝ : cur✝ = 0
⊢ Lean.Order.join
    (Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (some cur✝ = none)) ((fun x x_1 x_2 => True) xs [] PUnit.unit))
    (Lean.Order.iSup fun r =>
      Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (some cur✝ = some r ∧ [] = []))
        ((fun r x => r = 0) r PUnit.unit))
-/
#guard_msgs in
set_option sym.debug false in
theorem findZeroFor_spec (xs : List Nat) :
    Triple (findZeroFor xs) True (fun r => r = 0) (fun e => e = "no zero") := by
  vcgen [findZeroFor]
    invariants
    · Invariant.withEarlyReturnNewDo Prop (fun _ _ _ => True) (fun r _ => r = 0)
    with try finish

end Velvet.Examples.LoopVCGenUpstreamIssue
