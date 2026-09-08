module

public import Velvet
public meta import Velvet

open Std.WP Named Loop Specs WPPartial Lean.Order

/-
# Error message examples

These commands intentionally fail and use `#guard_msgs` to pin the exact error message. If an
error message regresses (text, location, or when it fires), this file fails to build.
-/

/- In total correctness, `while'` must carry a `decreasing` clause. -/
/-- error: `while'` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness -/
#guard_msgs in
method badWhilePrime (n : Nat) returns (res : Nat)
  requires True
  ensures res = 0
do
  let mut i := 0
  while' i < n
    invariant True
  do
    i := i + 1
  return 0

/- Invariant referencing loop cursor variable without `done_with`. -/
/--
error: Loop invariant 'bad_inv' references loop cursor variable 'i'.
Cursor-dependent invariants require an explicit 'done_with' clause because 'i' is not in scope after the loop terminates.
Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes.
-/
#guard_msgs in
method badForPrimeCursor (n : Nat) returns (res : Nat)
  requires True
  ensures res = n
do
  let mut x := 0
  for' i in 0...n
    invariant bad_inv: x = i
  do
    x := x + 1
  return x

/- Multiple invariants where one references loop cursor variable without `done_with`. -/
/--
error: Loop invariant 'cursor_dep' references loop cursor variable 'i'.
Cursor-dependent invariants require an explicit 'done_with' clause because 'i' is not in scope after the loop terminates.
Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes.
-/
#guard_msgs in
method badForPrimeMultiInv (n : Nat) returns (res : Nat)
  requires True
  ensures res = n
do
  let mut x := 0
  for' i in 0...n
    invariant state_ok: x ≥ 0
    invariant cursor_dep: x = i
  do
    x := x + 1
  return x

/- Invariant referencing `__rest` without `done_with`. -/
/--
error: Loop invariant 'rest_check' references '__rest'.
Suffix-dependent invariants require an explicit 'done_with' clause because there are no remaining elements after the loop terminates.
Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes.
-/
#guard_msgs in
method badForPrimeRest (xs : List Nat) returns (res : Nat)
  requires True
  ensures res = 0
do
  let mut x := 0
  for' elem in xs
    invariant rest_check: __rest.length ≥ 0
  do
    x := x + elem
  return x

/- Invariant referencing `__pref` without `done_with`. -/
/--
error: Loop invariant 'pref_check' references '__pref'.
Prefix-dependent invariants require an explicit 'done_with' clause specifying what holds when the loop finishes.
Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes.
-/
#guard_msgs in
method badForPrimePref (xs : List Nat) returns (res : Nat)
  requires True
  ensures res = 0
do
  let mut x := 0
  for' elem in xs
    invariant pref_check: __pref.length ≥ 0
  do
    x := x + elem
  return x

/- Explicit `set_option velvet.semantics.termination "total"` without `decreasing`. -/
/-- error: `while'` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness -/
#guard_msgs in
set_option velvet.semantics.termination "total" in
method badWhileExplicitTotal (n : Nat) returns (res : Nat)
  requires True
  ensures res = 0
do
  let mut i := 0
  while' i < n
    invariant True
  do
    i := i + 1
  return 0

/- Partial correctness while loop in a monad stack lacking a partial-loop instance. -/
@[expose] public def NoCCPOMonad (α : Type) : Type := Option α
public instance : Monad NoCCPOMonad := inferInstanceAs (Monad Option)
public instance : WPMonad NoCCPOMonad Prop (Unit → Prop) := inferInstanceAs (WPMonad Option Prop (Unit → Prop))

/--
error: failed to synthesize instance of type class
  ForIn NoCCPOMonad PartialLoop Unit

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option velvet.semantics.termination "partial" in
method badWhileNoCCPO (n : Nat) returns (res : Nat) in NoCCPOMonad
  requires True
  signals (fun (_ : Unit) => True)
  ensures res = 0
do
  let mut i := 0
  while' i < n
    invariant True
  do
    i := i + 1
  return 0

/- Partial correctness while loop in a monad with CCPO & MonoBind but lacking WPPartial instance. -/
@[expose] public def NoWPPartialMonad (α : Type) : Type := Option α
public instance : Monad NoWPPartialMonad := inferInstanceAs (Monad Option)
public instance : WPMonad NoWPPartialMonad Prop (Unit → Prop) := inferInstanceAs (WPMonad Option Prop (Unit → Prop))
public instance (α : Type) : CCPO (NoWPPartialMonad α) := inferInstanceAs (CCPO (Option α))
public instance : MonoBind NoWPPartialMonad where
  bind_mono_left := MonoBind.bind_mono_left (m := Option)
  bind_mono_right := MonoBind.bind_mono_right (m := Option)

set_option velvet.semantics.termination "partial" in
method badWhileNoWPPartial (n : Nat) returns (res : Nat) in NoWPPartialMonad
  requires True
  signals (fun (_ : Unit) => True)
  ensures res = 0
do
  let mut i := 0
  while' i < n
    invariant True
  do
    i := i + 1
  return 0

/--
error: No spec applicable to program Gadget.whileLoopPartial 0
  (fun __u __s => if h_loop : __s < n✝ then pure (ForInStep.yield (__s + 1)) else pure (ForInStep.done __s))
  (fun i => ⌜⟪invariant1 : True⟫⌝) fun i =>
  ⌜⟪invariant1 : True⟫⌝ ⊓
    ⌜⟪h_done_with : ¬i < n✝⟫⌝ in monad NoWPPartialMonad. Candidates were [SpecProof.global Loop.Spec.whileLoop_partial].
-/
#guard_msgs in
prove_correct badWhileNoWPPartial by
  velvet_vcgen [badWhileNoWPPartial] with finish

/- Signals with multiple binders when no `in` monad stack is provided. -/
/-- error: expected exactly one explicit binder in `signals` when no `in` monad stack is given, got 2 -/
#guard_msgs in
method badSignalsTwoBinders returns (res : Nat)
  requires True
  signals (e1 : String) (e2 : Nat) => e1 = "boom"
  ensures res = 0
do
  return 0

/- Signals with untyped binder when no `in` monad stack is provided. -/
/-- error: expected a typed binder `(x : T)` in `signals` when no `in` monad stack is given -/
#guard_msgs in
method badSignalsUntyped returns (res : Nat)
  requires True
  signals (e) => e = "boom"
  ensures res = 0
do
  return 0

/- Partial correctness loop in `Option` with `signals (e : Unit) => False` fails intrinsic verification.
   The while loop without a decreasing measure allows divergence (`divergence_post Option` is `True`),
   which contradicts the contract's promise that failure/divergence never happens (`signals False`). -/
/--
error: `finish` failed
case signals1
n✝ : Nat
requires1 : True
b✝ : Nat
i_le : b✝ ≤ n✝
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] b✝ ≤ n✝
  [eqc] True propositions
    [prop] b✝ ≤ n✝
  [cutsat] Assignment satisfying linear constraints
    [assign] n✝ := 0
    [assign] b✝ := 0
-/
#guard_msgs in
set_option velvet.semantics.termination "partial" in
set_option velvet.verifyDuringElab true in
method badSignalsPartialOption (n : Nat) returns (res : Nat) in Option
  requires True
  signals (e : Unit) => False
  ensures res = n
do
  let mut i := 0
  while' (i < n)
    invariant i_le : i ≤ n
  do
    i := i + 1
  return i




