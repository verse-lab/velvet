import Velvet2.Syntax
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

open Std.Internal.Do
open Lean.Order

namespace Velvet2.Examples.Lifting

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
  vcgen_ [bump] with finish

-- Program A: stateful wrapper around B.
--
-- Note that A's `requires` must be strong enough for the call: dropping
-- `n ≠ 0` here leaves B's precondition `¬n = 0` as an unsolved call-site VC.
method outerBump (n : Nat) returns (res : Nat) in StateT Nat Option
  requires (s : Nat), n ≠ 0
  signals False
  ensures (s : Nat), res = n + 1 ∧ s = res
do
  let x ← bump n
  set x
  return x

prove_correct outerBump by
  vcgen_ [outerBump] with finish

/-- Explicit discharge: `'requires1'` is B's precondition surfacing at the lifted
call site (its proof reuses the hypothesis recorded from B's contract), while
`'signals1'` and `'ensures1'` are A's own obligations. -/
theorem outerBump_explicit : outerBump.spec_triple := by
  unfold outerBump.spec_triple
  vcgen_ [outerBump]
  case requires1 => grind
  case signals1 => simp_all
  case ensures1 => grind

/-! ## Scenario 2: `ExceptT String Option` → `StateT Nat (ExceptT String Option)`

B is an auto-stacked exception method throwing `"n is odd"`; A adds a state
dimension. Under the lift, B's error channel flows into A's error channel, so
A's `signals err_odd` clause constrains exactly which errors may escape, and
B's termination channel composes with A's `signals False`.
-/

method checkedHalf (n : Nat) returns (res : Nat)
  requires True
  signals err_odd : (e : String), e = "n is odd"
  ensures res * 2 = n
do
  if n % 2 = 1 then
    throw "n is odd"
  assert parity : ¬(n % 2 = 1)
  return n / 2

prove_correct checkedHalf by
  vcgen_ [checkedHalf] with finish

method outerHalf (n : Nat) returns (res : Nat) in StateT Nat (ExceptT String Option)
  requires (s : Nat), True
  signals err_odd : (e : String), e = "n is odd"
  signals False
  ensures (s : Nat), res * 2 = n ∧ s = res
do
  let h ← checkedHalf n
  set h
  return h

prove_correct outerHalf by
  vcgen_ [outerHalf] with finish

/-- Explicit discharge: `'err_odd'` ties the error raised by the lifted call to
A's `signals` clause (the hypothesis records B's own signal postcondition), and
`'vc2'` composes the innermost `Option` failure channels. -/
theorem outerHalf_explicit : outerHalf.spec_triple := by
  unfold outerHalf.spec_triple
  vcgen_ [outerHalf]
  case err_odd => grind
  case vc2 => simp_all
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
  vcgen_ [triple'] with finish

method addTriple (k : Nat) returns (res : Nat) in StateT Nat Id
  requires (s : Nat), True
  ensures (s : Nat), res = s
do
  let t ← triple' k
  let initial ← get
  set (initial + t)
  let cur ← get
  return cur

prove_correct addTriple by
  vcgen_ [addTriple] with finish

/-- Explicit discharge: no VCs remain after generation; the lifted pure call,
the state reads/writes and the postconditions cancel definitionally. -/
theorem addTriple_explicit : addTriple.spec_triple := by
  unfold addTriple.spec_triple
  vcgen_ [addTriple]

/-! ## Scenario 4: a lift stdlib does not provide — `Option` → `ExceptT String _`

There is no `MonadLift Option (ExceptT ε m)` instance anywhere in core/Std:
stdlib cannot decide what `none` should become (which error message?). Defining
that mapping is precisely the freedom a custom lift affords — here we turn a
failed `Option` into the exception `"Lifted from Option"` — but it also means
the *user* owns the vcgen-facing contract for lifted calls. Two definitions are
needed:

1. The `MonadLift` instance itself (a semantic decision).
2. A `@[spec]` theorem of the same shape as stdlib's `Spec.monadLift_*`
   family, encoding those semantics as a weakest-precondition transformation.

Piece 2 is not optional. Without it, vcgen refuses to decompose the lifted call:

```text
No spec applicable to program MonadLift.monadLift (monadLift (bump n✝)) in monad
ExceptT String Option. Candidates were [Std.Internal.Do.Spec.monadLift_ExceptT].
```

stdlib's spec is listed as a candidate but its backward rule fails to apply,
because its statement pins the canonical `MonadLift m (ExceptT ε m)` instance —
a deliberately safe mismatch rather than a silent reuse of the wrong semantics.

(For a monad that is not built from transformers at all, there is a piece 0: a
`WPMonad m Pred EPred` instance interpreting programs into predicate
transformers, plus `Assertion` instances for the lattice. See
`Std/Internal/Do/WP/Basic.lean` for the `Id`/`Option`/transformer instances to
model after.)
-/

-- The error message raised when a lifted `Option` computation fails.
def optionLiftError : String := "Lifted from Option"

-- Piece 1: the lift itself: `none ↦ throw "Lifted from Option"` — a genuine
-- exception carrying the diagnostic message, not an inner failure.
instance instMonadLiftOptionExceptTString {m : Type → Type} [Monad m] :
    MonadLift Option (ExceptT String m) where
  monadLift x :=
    ExceptT.mk (
      match x with
      | some a => pure (Except.ok a)
      | none => pure (Except.error optionLiftError))

/-- Piece 2: the vcgen-facing contract for lifted-call nodes, mirroring
`Std.Internal.Do.Spec.monadLift_ExceptT` but for our instance.

`Option`'s WP is pinned to the `Prop` lattice (`Option.instWPMonad : WPMonad
Option Prop Prop`), so the source failure postcondition is interpreted *at* the
chosen error payload: the premise says the lifted call behaves as if a source
failure raises `optionLiftError` satisfying `eh optionLiftError` — exactly the
semantics of piece 1. The Triple is proved from the instance's actual `match`, so
instance and spec cannot drift apart. With the inner monad fixed to `Option`,
both sides compute and the proof is two `rfl`-entailments. -/
@[spec]
theorem triple_monadLift_option_exceptTString
    {α : Type} (x : Option α) (post : α → Prop) (eh : String → Prop) (etail : Prop) :
    Triple (MonadLift.monadLift x : ExceptT String Option α)
      (wp x post (eh optionLiftError))
      post
      (EPost.Cons.mk eh etail) := by
  apply Triple.intro
  cases x <;> exact PartialOrder.rel_refl

-- Program A: stateful wrapper around B across the custom lift. Same shape as
-- `outerBump`, now over `StateT Nat (ExceptT String Option)`; the `signals`
-- clause admits exactly the one error our lift can produce.
method outerSafe (n : Nat) returns (res : Nat) in StateT Nat (ExceptT String Option)
  requires (s : Nat), n ≠ 0
  signals boom : (e : String), e = optionLiftError
  signals False
  ensures (s : Nat), res = n + 1 ∧ s = res
do
  let x ← bump n
  set x
  return x

prove_correct outerSafe by
  vcgen_ [outerSafe] with finish

/-- Explicit discharge: `'requires1'` surfaces from B's precondition through the
custom lift exactly as in scenario 1; `'vc2'` is A's total-correctness signal. -/
theorem outerSafe_explicit : outerSafe.spec_triple := by
  unfold outerSafe.spec_triple
  vcgen_ [outerSafe]
  case requires1 => grind
  case vc2 => simp_all
  case ensures1 => grind

end Velvet2.Examples.Lifting
