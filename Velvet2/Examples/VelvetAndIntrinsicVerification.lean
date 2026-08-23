import Velvet2.Syntax
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

open Std.Internal.Do

namespace Velvet2.Examples.VelvetAndIntrinsic

/-! ## Direction A: intrinsic function called from a Velvet method

Program B is a plain `def` with an intrinsic contract in `Option`. Program A is
a Velvet method over `StateT Nat Option`; the call site lifts B exactly as in
`LiftingExamples.lean` scenario 1, and B's intrinsic `safeInc.spec` applies
through the lift like any other registered spec.
-/

/-- Program B, intrinsically verified: total-correctness contract discharged by
the toolchain `vcgen` during elaboration of the `def`. -/
def safeInc (n : Nat) : Option Nat
  requires n ≠ 0
  ensures r => r = n + 1 :=
  pure (n + 1)

/-- info: safeInc.spec : ∀ (n : Nat), ⦃ n ≠ 0 ⦄ safeInc n ⦃ fun r => r = n + 1 ⦄ -/
#guard_msgs in
#check @safeInc.spec

-- Program A: Velvet method calling the intrinsic helper across the lift.
method velvetCallsIntrinsic (n : Nat) returns (res : Nat) in StateT Nat Option
  requires (s : Nat), n ≠ 0
  signals False
  ensures (s : Nat), res = n + 1 ∧ s = res
do
  let x ← safeInc n
  set x
  return x

prove_correct velvetCallsIntrinsic by
  vcgen_ [velvetCallsIntrinsic] with finish

/-! ## Direction B: Velvet method called from an intrinsic definition

The roles reverse: `intrinsicCallsVelvet` is verified by the toolchain `vcgen`
when the `def` elaborates, and at the call node it picks up
`velvetDouble.spec` — the contract `prove_correct` registered for the
Velvet method. Both calls live in `StateT Nat Id`, so no lifting happens here;
the interop is purely contract-level.
-/

method velvetDouble (k : Nat) returns (res : Nat) in StateT Nat Id
  requires (s : Nat), True
  ensures (s : Nat), res = 2 * k
do
  return 2 * k

prove_correct velvetDouble by
  vcgen_ [velvetDouble] with finish

/-- Program C, intrinsically verified, composing the Velvet method with reads of
the ambient state. Its contract is proven automatically at elaboration. -/
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

-- The two worlds are also interoperable at runtime — everything stays
-- ordinary, compilable Lean code.
example : (intrinsicCallsVelvet 5).run 100 = ((110, 100) : Nat × Nat) := by rfl

end Velvet2.Examples.VelvetAndIntrinsic
