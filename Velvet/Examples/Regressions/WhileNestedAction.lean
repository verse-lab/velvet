module

public import Velvet
public meta import Velvet

open Std.WP

/-!
# Nested actions in a `while` condition

`(← e)` in a `while` condition runs before every iteration, as in Lean's own `while`, both when the
loop has no Velvet clauses and when Velvet verifies it.
-/

namespace Velvet.Examples.Regressions.WhileNestedAction

def readCounted (r checks : IO.Ref Nat) : IO Nat := do
  checks.modify (· + 1)
  r.get

def countReads : IO (Nat × Nat) := do
  let r ← IO.mkRef 0
  let checks ← IO.mkRef 0
  while (← readCounted r checks) < 3 do
    r.modify (· + 1)
    if (← r.get) ≥ 10 then break
  return (← r.get, ← checks.get)

/-- info: (3, 4) -/
#guard_msgs in
#eval countReads

method countToThree (fuel₀ : Nat) returns (res : PUnit) in StateM Nat
  requires (s : Nat) => fuel₀ = 10
  ensures (s : Nat) => s = 3
do
  set 0
  let mut fuel := fuel₀
  while (← get) < 3 ∧ fuel > 0
    invariant tracks : (fun s : Nat => s + fuel = 10 ∧ s ≤ 3)
    decreasing remaining : fuel
    done_with finished : (fun s : Nat => s = 3)
  do
    let s ← get
    set (s + 1)
    fuel := fuel - 1

prove_correct countToThree by
  velvet_vcgen [countToThree] with finish

/-- info: ((), 3) -/
#guard_msgs in
#eval (countToThree 10).run 0

end Velvet.Examples.Regressions.WhileNestedAction
