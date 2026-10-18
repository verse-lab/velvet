module

public import Velvet
public meta import Velvet
public import Std.Tactic.Do

open Std.WP

/-!
# Early exits from `while` loops

Two problems with leaving a `while` loop through `break` or `return`, each shown for
`velvet_vcgen` and for Lean's `vcgen`. The `#guard_msgs` blocks pin the goals that cannot be
proved today.

1. Without `done_with`, a Velvet `while` loop's exit condition is its invariants together with
   `¬cond`, and the loop specification requires it on every exit. `while c do body` runs as
   `if c then body else break`, so the specification cannot tell the loop's own exit from a
   `break` or `return` in the body, where `cond` still holds. The goal `¬cond` is then
   unprovable. Lean's `while` asks for its invariant at `exit = true` instead, and proves the
   same loop.

2. `return e` inside a loop stores `some e` in the loop state's return slot, and `ensures` is
   checked against it after the loop. Invariants and `done_with` cannot name the return slot, so
   what held at the `return` is lost, and the `ensures` goal has no facts about the returned
   value. Lean's `vcgen` has the same problem.
-/

namespace Velvet.Examples.LoopEarlyExit

set_option experimental.vcgen true
set_option experimental.intrinsic true

/-! ## 1. `¬cond` is required on a `break` -/

method breakAtFive (n : Nat) returns (res : Nat)
  ensures True
do
  let mut i := 0
  while i < n
    invariant bound : i ≤ n
    decreasing n - i
  do
    if i = 5 then break
    i := i + 1
  return i

/- On the `break`, `i < n` still holds, so `¬i < n` cannot be proved. -/
/--
error: unsolved goals
case h_done_with
n✝ i : Nat
bound : i ≤ n✝
h_loop : i < n✝
if_cond : i = 5
⊢ ¬i < n✝
-/
#guard_msgs in
prove_correct breakAtFive by
  velvet_vcgen [breakAtFive] with try finish

/-- Lean's `while` asks for the invariant at `exit = true`, which holds on the `break`. -/
def breakAtFiveLean (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n
    invariant _ => i ≤ n
    decreasing n - i
  do
    if i = 5 then break
    i := i + 1
  return i

theorem breakAtFiveLean_spec (n : Nat) :
    Triple (breakAtFiveLean n) True (fun _ => True) estack⟨⟩ := by
  vcgen [breakAtFiveLean] <;> grind

/-! ## 2. Facts at a `return` do not reach `ensures` -/

method findZero (xs : Array Nat) returns (res : Nat)
  signals notFound : (e : String) => e = "no zero"
  ensures res < xs.size ∧ xs[res]! = 0
do
  let mut i := 0
  while i < xs.size
    invariant bound : i ≤ xs.size
    decreasing xs.size - i
    done_with fin : i ≤ xs.size
  do
    if xs[i]! = 0 then return i
    i := i + 1
  throw "no zero"

/- Only `h_some` is known about the returned `a`; `xs[a]! = 0`, which held at the `return`, is lost. -/
/--
error: unsolved goals
case ensures1
xs✝ : Array Nat
a✝ : Option Nat
i : Nat
bound fin : i ≤ xs✝.size
a : Nat
h_some : a✝ = some a
⊢ a < xs✝.size ∧ xs✝[a]! = 0
-/
#guard_msgs in
prove_correct findZero by
  velvet_vcgen [findZero] with try finish

def findZeroLean (xs : Array Nat) : Except String Nat := do
  let mut i := 0
  while i < xs.size
    invariant _ => i ≤ xs.size
    decreasing xs.size - i
  do
    if xs[i]! = 0 then return i
    i := i + 1
  throw "no zero"

-- `sym.debug` is off here: Lean's own `splitProdBinder` fails its sharing checks on the loop state
-- `Option Nat × Nat` (see `SplitProdBinder.lean`).
/- Lean's `vcgen` loses the same fact: only the return slot `(a✝², i).fst = some a✝` is known. -/
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
theorem findZeroLean_spec (xs : Array Nat) :
    Triple (findZeroLean xs) True (fun r => r < xs.size ∧ xs[r]! = 0)
      (fun e => e = "no zero") := by
  vcgen [findZeroLean] with try finish

end Velvet.Examples.LoopEarlyExit
