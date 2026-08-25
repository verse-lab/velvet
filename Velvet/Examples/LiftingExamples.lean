import Velvet

open Std.WP
open Lean.Order

namespace Velvet.Examples.Lifting

/-! ## Scenario 1: `Option` → `StateT Nat Option`

B is a plain `Option` method (the default method monad). A adds a state layer on
top and calls B; do-notation inserts `liftM (bump n)` because `bind` expects a
`StateT Nat Option` computation.
-/

-- Program B: total-correctness method in `Option`; fails iff `n = 0`.
method bump (n : Nat) returns (res : Nat)
  requires n ≠ 0
  ensures res = n + 1
do
  return n + 1

prove_correct bump by
  velvet_vcgen [bump] with finish

-- Program A: stateful wrapper around B.
--
-- Note that A's `requires` must be strong enough for the call: dropping
-- `n ≠ 0` here leaves B's precondition `¬n = 0` as an unsolved call-site VC.
method outerBump (n : Nat) returns (res : Nat) in StateT Nat Option
  requires (s : Nat) => n ≠ 0
  signals (_ : Unit) => False
  ensures (s : Nat) => res = n + 1 ∧ s = res
do
  let x ← bump n
  set x
  return x

prove_correct outerBump by
  velvet_vcgen [outerBump] with finish

/-- Explicit discharge: `'requires1'` is B's precondition surfacing at the lifted
call site (its proof reuses the hypothesis recorded from B's contract), while
`'signals1'` and `'ensures1'` are A's own obligations. -/
theorem outerBump_explicit : outerBump.spec_triple := by
  unfold outerBump.spec_triple
  velvet_vcgen [outerBump]
  case requires1 => grind
  case signals1 => grind
  case ensures1 => grind

/-! ## Scenario 2: `ExceptT String Option` → `StateT Nat (ExceptT String Option)`

B is an auto-stacked exception method throwing `"n is odd"`; A adds a state
dimension. Under the lift, B's error channel flows into A's error channel, so
A's `signals err_odd` clause constrains exactly which errors may escape, and
B's termination channel composes with A's `signals (_ : Unit) => False`.
-/

method checkedHalf (n : Nat) returns (res : Nat)
  requires True
  signals err_odd : (e : String) => e = "n is odd"
  ensures res * 2 = n
do
  if n % 2 = 1 then
    throw "n is odd"
  assert parity : ¬(n % 2 = 1)
  return n / 2

prove_correct checkedHalf by
  velvet_vcgen [checkedHalf] with finish

method outerHalf (n : Nat) returns (res : Nat) in StateT Nat (ExceptT String Option)
  requires (s : Nat) => True
  signals err_odd : (e : String) => e = "n is odd"
  signals (_ : Unit) => False
  ensures (s : Nat) => res * 2 = n ∧ s = res
do
  let h ← checkedHalf n
  set h
  return h

prove_correct outerHalf by
  velvet_vcgen [outerHalf] with finish

/-- Explicit discharge: `'err_odd'` ties the error raised by the lifted call to
A's `signals` clause (the hypothesis records B's own signal postcondition), and
`'signals2'` composes the innermost `Option` failure channels. -/
theorem outerHalf_explicit : outerHalf.spec_triple := by
  unfold outerHalf.spec_triple
  velvet_vcgen [outerHalf]
  case err_odd => grind
  case signals2 => grind
  case ensures1 => grind

/-! ## Scenario 3: `Id` → `StateT Nat Id`

Pure methods lift into any `Pure` monad (`MonadLiftT Id m` holds unconditionally).
Here the lifted call leaves no residual VCs at all: B's trivial contract composes
with A's state updates entirely during generation.
-/

method triple' (k : Nat) returns (res : Nat) in Id
  requires True
  ensures res = 3 * k
do
  return 3 * k

prove_correct triple' by
  velvet_vcgen [triple'] with finish

method addTriple (k : Nat) returns (res : Nat) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = s
do
  let t ← triple' k
  let initial ← get
  set (initial + t)
  let cur ← get
  return cur

prove_correct addTriple by
  velvet_vcgen [addTriple] with finish

/-- Explicit discharge: no VCs remain after generation; the lifted pure call,
the state reads/writes and the postconditions cancel definitionally. -/
theorem addTriple_explicit : addTriple.spec_triple := by
  unfold addTriple.spec_triple
  velvet_vcgen [addTriple]

/-! ## Scenario 4: a lift stdlib does not provide — `Option` → `ExceptT String _`

Two definitions are needed:

1. The `MonadLift` instance itself .
2. A `@[spec]` theorem of the same shape as stdlib's `Spec.monadLift_*`
   family, encoding those semantics as a weakest-precondition transformation.
-/

-- The error message raised when a lifted `Option` computation fails.
def optionLiftError : String := "Lifted from Option"

-- Piece 1: the lift itself: `none ↦ throw "Lifted from Option"` 
instance instMonadLiftOptionExceptTString {m : Type → Type} [Monad m] :
    MonadLift Option (ExceptT String m) where
  monadLift x :=
    ExceptT.mk (
      match x with
      | some a => pure (Except.ok a)
      | none => pure (Except.error optionLiftError))

@[spec]
theorem triple_monadLift_option_exceptTString
    {α : Type} (x : Option α) (post : α → Prop) (epost : (String → Prop) × (Unit → Prop)) :
    Triple (MonadLift.monadLift x : ExceptT String Option α)
      (wp x post (fun (_ : Unit) => epost.fst optionLiftError))
      post
      epost := by
  apply Triple.intro
  cases x <;> exact PartialOrder.rel_refl

-- Program A: stateful wrapper around B across the custom lift. Same shape as
-- `outerBump`, now over `StateT Nat (ExceptT String Option)`; the `signals`
-- clause admits exactly the one error our lift can produce.
method outerSafe (n : Nat) returns (res : Nat) in StateT Nat (ExceptT String Option)
  requires (s : Nat) => n ≠ 0
  signals boom : (e : String) => e = optionLiftError
  signals (_ : Unit) => False
  ensures (s : Nat) => res = n + 1 ∧ s = res
do
  let x ← bump n
  set x
  return x

prove_correct outerSafe by
  velvet_vcgen [outerSafe] with finish

theorem outerSafe_explicit : outerSafe.spec_triple := by
  unfold outerSafe.spec_triple
  velvet_vcgen [outerSafe]
  case requires1 => grind
  case ensures1 => grind

end Velvet.Examples.Lifting
