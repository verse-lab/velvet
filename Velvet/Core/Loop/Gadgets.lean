module

public import Velvet.Core.Specs
public import Velvet.Core.Partial
public import Std.WP
public import Std.WP.Gadget.ForIn
public import Std.WP.Triple.SpecLemmas
public import Std.Internal.ForIn

open Std.Internal
open Std.WP
open Std.WP.Assertion
open Lean.Order
open WPPartial

universe u u₁ u₂ v w

namespace Loop

/-- Our own least-fixed-point loop: `partial_fixpoint` over the loop body. -/
@[expose, specialize] public def forIn.loop {β : Type u} {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => forIn.loop f b
  partial_fixpoint

public structure PartialLoop where
  mk ::

public instance instForInPartialLoopOfCCPO {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] :
    ForIn m PartialLoop Unit where
  forIn _ init f := forIn.loop f init

/-!
## Gadgets

A Velvet loop becomes a gadget: Lean's `forIn'` or `forIn` over the loop body, with the loop's
clauses as extra arguments that do not change what runs. The loop state holds the mutable
variables the body assigns; when the body can `return`, it starts with the return slot
`Option γ`.

| Loop | Gadget |
|---|---|
| `for` | `forLoopWithInvariant` |
| `for`, with a `return` | `forLoopWithInvariantReturning` |
| `for … done_with` | `forLoopWithInvariantAndDone` |
| `for … done_with`, with a `return` | `forLoopWithInvariantAndDoneReturning` |
| `while` (partial correctness) | `whileLoopPartial` |
| `while`, with a `return` | `whileLoopPartialReturning` |
| `while … decreasing` | `whileLoopTotal` |
| `while … decreasing`, with a `return` | `whileLoopTotalReturning` |

A `while` loop's `done_with` is the `done?` argument, `none` without it.
-/

namespace Gadget

set_option linter.unusedVariables false in
/-- A `for` loop whose invariants mention the mutable variables. The body takes the membership
proof `h_mem : x ∈ xs`, which `for h : x in xs` names `h`.

    for x in xs
      invariant s_ok: s ≥ 0
    do
      s := s + x

becomes

    forLoopWithInvariant xs s
      (fun x h_mem s => … pure (ForInStep.yield (s + x)))
      (fun s => ⌜⟪s_ok : s ≥ 0⟫⌝) -/
@[expose, inline] public def forLoopWithInvariant {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : β → Pred) : m β :=
  forIn' xs init f

set_option linter.unusedVariables false in
/-- `forLoopWithInvariant` for a body that can `return`.

    for x in xs
      invariant s_ok: s ≥ 0
    do
      if x = 0 then return 0
      s := s + x

becomes

    forLoopWithInvariantReturning xs (none, s)
      (fun x h_mem (r?, s) =>
        if x = 0 then pure (ForInStep.done (some 0, s)) else pure (ForInStep.yield (none, s + x)))
      (fun s => ⌜⟪s_ok : s ≥ 0⟫⌝) -/
@[expose, inline] public def forLoopWithInvariantReturning {γ τ : Type u} {m : Type u → Type v}
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : Option γ × τ) (f : (a : α) → a ∈ xs → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) : m (Option γ × τ) :=
  forIn' xs init f

set_option linter.unusedVariables false in
/-- A `for` loop with `done_with`. Its invariants can also mention the elements already visited
(`__pref`), the current one and the rest (`__rest`); `done` holds when the loop exits.

    for x in xs
      invariant s_ok: s = __pref.length
      done_with fin: s = xs.length
    do
      s := s + 1

becomes

    forLoopWithInvariantAndDone xs s
      (fun x h_mem s => … pure (ForInStep.yield (s + 1)))
      (fun __pref x __rest s => ⌜⟪s_ok : s = __pref.length⟫⌝)
      (fun __pref s => ⌜⟪fin : s = xs.length⟫⌝) -/
@[expose, inline] public def forLoopWithInvariantAndDone {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred) : m β :=
  forIn' xs init f

set_option linter.unusedVariables false in
/-- `forLoopWithInvariantAndDone` for a body that can `return`.

    for x in xs
      invariant s_ok: s = __pref.length
      done_with fin: s = xs.length
    do
      if x = 0 then return 0
      s := s + 1

becomes

    forLoopWithInvariantAndDoneReturning xs (none, s)
      (fun x h_mem (r?, s) =>
        if x = 0 then pure (ForInStep.done (some 0, s)) else pure (ForInStep.yield (none, s + 1)))
      (fun __pref x __rest s => ⌜⟪s_ok : s = __pref.length⟫⌝)
      (fun __pref s => ⌜⟪fin : s = xs.length⟫⌝) -/
@[expose, inline] public def forLoopWithInvariantAndDoneReturning {γ τ : Type u} {m : Type u → Type v}
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : Option γ × τ) (f : (a : α) → a ∈ xs → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : List α → α → List α → τ → Pred)
    (done : List α → τ → Pred) : m (Option γ × τ) :=
  forIn' xs init f

set_option linter.unusedVariables false in
/-- A `while` loop in partial correctness. The body exits with `ForInStep.done` once the condition
fails, and `done?` is the `done_with` clause, with the invariants.

    while i < n
      invariant bound: i ≤ n
    do
      i := i + 1

becomes

    whileLoopPartial i
      (fun () i => if h_loop : i < n then pure (ForInStep.yield (i + 1)) else pure (ForInStep.done i))
      (fun i => ⌜⟪bound : i ≤ n⟫⌝) none -/
@[expose, inline] public def whileLoopPartial {β : Type u} {Pred : Type u₁} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (done? : Option (β → Pred)) : m β :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
/-- `whileLoopPartial` for a body that can `return`.

    while i < n
      invariant bound: i ≤ n
      done_with fin: i = n
    do
      if i = 5 then return 5
      i := i + 1

becomes

    whileLoopPartialReturning (none, i)
      (fun () (r?, i) =>
        if h_loop : i < n then
          if i = 5 then pure (ForInStep.done (some 5, i)) else pure (ForInStep.yield (none, i + 1))
        else pure (ForInStep.done (none, i)))
      (fun i => ⌜⟪bound : i ≤ n⟫⌝) (some fun i => ⌜⟪bound : i ≤ n⟫⌝ ⊓ ⌜⟪fin : i = n⟫⌝) -/
@[expose, inline] public def whileLoopPartialReturning {γ τ : Type u} {Pred : Type u₁} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : Option γ × τ) (f : Unit → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) (done? : Option (τ → Pred)) : m (Option γ × τ) :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
/-- A `while` loop with a `decreasing` measure, in total correctness.

    while i < n
      invariant bound: i ≤ n
      decreasing n - i
      done_with fin: i = n
    do
      i := i + 1

becomes

    whileLoopTotal i
      (fun () i => if h_loop : i < n then pure (ForInStep.yield (i + 1)) else pure (ForInStep.done i))
      (fun i => ⌜⟪bound : i ≤ n⟫⌝) (some fun i => ⌜⟪bound : i ≤ n⟫⌝ ⊓ ⌜⟪fin : i = n⟫⌝)
      (fun i => ⟪termination : n - i⟫) -/
@[expose, inline] public def whileLoopTotal {β : Type u} {Pred : Type u₁} {m : Type u → Type v} [ForIn m Lean.Loop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (done? : Option (β → Pred)) (measure : β → Named.Measure) : m β :=
  forIn Lean.Loop.mk init f

set_option linter.unusedVariables false in
/-- `whileLoopTotal` for a body that can `return`.

    while i < n
      invariant bound: i ≤ n
      decreasing n - i
    do
      if i = 5 then return 5
      i := i + 1

becomes

    whileLoopTotalReturning (none, i)
      (fun () (r?, i) =>
        if h_loop : i < n then
          if i = 5 then pure (ForInStep.done (some 5, i)) else pure (ForInStep.yield (none, i + 1))
        else pure (ForInStep.done (none, i)))
      (fun i => ⌜⟪bound : i ≤ n⟫⌝) none (fun i => ⟪termination : n - i⟫) -/
@[expose, inline] public def whileLoopTotalReturning {γ τ : Type u} {Pred : Type u₁} {m : Type u → Type v}
    [ForIn m Lean.Loop Unit]
    (init : Option γ × τ) (f : Unit → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) (done? : Option (τ → Pred))
    (measure : τ → Named.Measure) : m (Option γ × τ) :=
  forIn Lean.Loop.mk init f

end Gadget

end Loop
