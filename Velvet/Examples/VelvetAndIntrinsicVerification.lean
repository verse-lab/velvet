module

public import Velvet
public meta import Velvet

open Std.WP

namespace Velvet.Examples.VelvetAndIntrinsic

public def safeInc (n : Nat) : Option Nat
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
  velvet_vcgen [velvetCallsIntrinsic] with finish

method velvetDouble (k : Nat) returns (res : Nat) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = 2 * k
do
  return 2 * k

prove_correct velvetDouble by
  velvet_vcgen [velvetDouble] with finish

public def intrinsicCallsVelvet (k : Nat) : StateT Nat Id Nat
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

method mkFreshNat returns (r : Nat) in StateT Nat Id
  given (n : Nat)
  requires (s : Nat) => s = n
  ensures (s : Nat) => r = n ∧ s = n + 1
do
  let m ← get
  set (m + 1)
  return m

prove_correct mkFreshNat by
  velvet_vcgen [mkFreshNat] with finish

#check @mkFreshNat.spec

method widen (k : Nat) returns (res : Unit) in StateT Nat Id
  given (lo hi : Nat) {d : Nat}
  requires (s : Nat) => lo ≤ s ∧ s ≤ hi ∧ d = k
  ensures (s : Nat) => lo ≤ s + k ∧ s ≤ hi + d
do
  modify (· + k)

prove_correct widen by
  velvet_vcgen [widen] with finish

#check @widen.spec

end Velvet.Examples.VelvetAndIntrinsic
