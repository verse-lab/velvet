import Velvet

open Std.WP

namespace Velvet.Examples.VelvetAndIntrinsic

def safeInc (n : Nat) : Option Nat
  requires n ≠ 0
  ensures r => r = n + 1 :=
  pure (n + 1)

/-- info: safeInc.spec : ∀ (n : Nat), ⦃ n ≠ 0 ⦄ safeInc n ⦃ fun r => r = n + 1 ⦄ -/
#guard_msgs in
#check @safeInc.spec

method velvetCallsIntrinsic (n : Nat) returns (res : Nat) in StateT Nat Option
  requires (s : Nat) => n ≠ 0
  signals (_ : Unit) => False
  ensures (s : Nat) => res = n + 1 ∧ s = res
do
  let x ← safeInc n
  set x
  return x

prove_correct velvetCallsIntrinsic by
  vcgen_ [velvetCallsIntrinsic] with finish

method velvetDouble (k : Nat) returns (res : Nat) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = 2 * k
do
  return 2 * k

prove_correct velvetDouble by
  vcgen_ [velvetDouble] with finish

def intrinsicCallsVelvet (k : Nat) : StateT Nat Id Nat
  requires _s => True
  ensures r s => r = 2 * k + s :=
  do
    let d ← velvetDouble k
    let s ← get
    return d + s

/-- info: intrinsicCallsVelvet.spec : ∀ (k : Nat), ⦃ fun _s => True ⦄ intrinsicCallsVelvet k ⦃ fun r s => r = 2 * k + s ⦄ -/
#guard_msgs in
#check @intrinsicCallsVelvet.spec

example : (intrinsicCallsVelvet 5).run 100 = ((110, 100) : Nat × Nat) := by rfl

end Velvet.Examples.VelvetAndIntrinsic
