module

public import Velvet
public meta import Velvet

open scoped GhostSyntax
open Std.WP Lean.Order

namespace Velvet.Examples.BindersTest

set_option velvet.verifyDuringElab true

/-! ## 1. Multi-variable Explicit Binders `(x y : Nat)` -/

/-- Adds two natural numbers and returns their sum. -/
method addTwo (x y : Nat) returns (res : Nat) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = x + y
do
  return x + y

#check @addTwo.spec

/-! ## 2. Implicit Parameters `{α : Type}` -/

method identity {α : Type} (x : α) returns (res : α) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = x
do
  return x

#check @identity.spec

/-! ## 3. Multi-variable Implicit Parameters `{α β : Type}` -/

method makePair {α β : Type} (x : α) (y : β) returns (res : α × β) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = (x, y)
do
  return (x, y)

#check @makePair.spec

/-! ## 4. Typeclass Instance Binders `[Inhabited α]` -/

method getDefault (α : Type) [Inhabited α] returns (res : α) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = default
do
  return default

#check @getDefault.spec

/-! ## 5. Strict Implicit Binders `⦃α : Type⦄` -/

method strictId ⦃α : Type⦄ (x : α) returns (res : α) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = x
do
  return x

#check @strictId.spec

/-! ## 6. Dependent and Single-variable Binders `(n : Nat) (xs : List (Fin n))` -/

method headOf (n : Nat) (xs : List (Fin (n + 1))) returns (res : Nat) in StateT Nat Id
  requires (s : Nat) => xs ≠ []
  ensures (s : Nat) => True
do
  return 0

#check @headOf.spec

/-! ## 7. Combined Program Binders with `given` Clause -/

method combinedMethod (x y : Nat) {α : Type} [Inhabited α] (val : α)
    returns (res : Nat × α) in StateT Nat Id
  given (lo hi : Nat) {d : Nat}
  requires (s : Nat) => lo ≤ s ∧ s ≤ hi ∧ d = 1
  ensures (s : Nat) => res = (x + y, val) ∧ lo ≤ s ∧ s ≤ hi
do
  return (x + y, val)

#check @combinedMethod.spec

end Velvet.Examples.BindersTest
