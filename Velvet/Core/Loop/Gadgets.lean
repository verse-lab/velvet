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

/-- Dedicated collection marker for partial `while` loops. Using a distinct
collection type lets `ForIn` dispatch to fixed-point execution without
replacing the ordinary `ForIn m Lean.Loop Unit` instance. -/
public structure PartialLoop where
  mk ::

public instance instForInPartialLoopOfCCPO {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] :
    ForIn m PartialLoop Unit where
  forIn _ init f := forIn.loop f init

namespace Gadget

set_option linter.unusedVariables false in
/-- A pure `forIn` loop annotated with a state invariant (independent of the cursor variable).
The invariant holds before entering the loop and is preserved at every step. -/
@[expose, inline] public def forLoopWithInvariant {ρ : Type w} [ForIn m ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β))
    (inv : β → Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
/-- A pure `forIn'` loop annotated with a state invariant and membership proofs in the loop body. -/
@[expose, inline] public def forLoopMemWithInvariant {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : β → Pred) : m β :=
  forIn' xs init f

set_option linter.unusedVariables false in
/-- A `for` loop with a state invariant whose body can `return`; the state starts with the return
slot. -/
@[expose, inline] public def forLoopWithInvariantReturning {γ τ : Type u} {m : Type u → Type v}
    {ρ : Type w} [ForIn m ρ α]
    (xs : ρ) (init : Option γ × τ) (f : α → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) : m (Option γ × τ) :=
  forIn xs init f

set_option linter.unusedVariables false in
@[expose, inline] public def forLoopMemWithInvariantReturning {γ τ : Type u} {m : Type u → Type v}
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : Option γ × τ) (f : (a : α) → a ∈ xs → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) : m (Option γ × τ) :=
  forIn' xs init f

set_option linter.unusedVariables false in
@[expose, inline] public def forLoopWithInvariantAndDone {ρ : Type w} [ForIn m ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β))
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
@[expose, inline] public def forLoopMemWithInvariantAndDone {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred) : m β :=
  forIn' xs init f

set_option linter.unusedVariables false in
/-- A `for` loop with `done_with` whose body can `return`; the state starts with the return slot. -/
@[expose, inline] public def forLoopWithInvariantAndDoneReturning {γ τ : Type u} {m : Type u → Type v}
    {ρ : Type w} [ForIn m ρ α]
    (xs : ρ) (init : Option γ × τ) (f : α → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : List α → α → List α → τ → Pred)
    (done : List α → τ → Pred) : m (Option γ × τ) :=
  forIn xs init f

set_option linter.unusedVariables false in
@[expose, inline] public def forLoopMemWithInvariantAndDoneReturning {γ τ : Type u} {m : Type u → Type v}
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : Option γ × τ) (f : (a : α) → a ∈ xs → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : List α → α → List α → τ → Pred)
    (done : List α → τ → Pred) : m (Option γ × τ) :=
  forIn' xs init f

set_option linter.unusedVariables false in
@[expose, inline] public def whileLoopPartial {β : Type u} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) : m β :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
/-- A partial-correctness `while` loop whose body can `return`; the state starts with the return
slot. -/
@[expose, inline] public def whileLoopPartialReturning {γ τ : Type u} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : Option γ × τ) (f : Unit → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) : m (Option γ × τ) :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
@[expose, inline] public def whileLoopPartialAndDone {β : Type u} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (done : β → Pred) : m β :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
/-- A partial-correctness `while` loop with `done_with` whose body can `return`; the state starts
with the return slot. -/
@[expose, inline] public def whileLoopPartialAndDoneReturning {γ τ : Type u} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : Option γ × τ) (f : Unit → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) (done : τ → Pred) : m (Option γ × τ) :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
@[expose, inline] public def whileLoopTotal {β : Type u} {m : Type u → Type v} [ForIn m Lean.Loop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (measure : β → Named.Measure) : m β :=
  forIn Lean.Loop.mk init f

set_option linter.unusedVariables false in
/-- A total-correctness `while` loop whose body can `return`; the state starts with the return
slot. -/
@[expose, inline] public def whileLoopTotalReturning {γ τ : Type u} {m : Type u → Type v}
    [ForIn m Lean.Loop Unit]
    (init : Option γ × τ) (f : Unit → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) (measure : τ → Named.Measure) : m (Option γ × τ) :=
  forIn Lean.Loop.mk init f

set_option linter.unusedVariables false in
@[expose, inline] public def whileLoopTotalAndDone {β : Type u} {m : Type u → Type v} [ForIn m Lean.Loop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (done : β → Pred) (measure : β → Named.Measure) : m β :=
  forIn Lean.Loop.mk init f

set_option linter.unusedVariables false in
/-- A total-correctness `while` loop with `done_with` whose body can `return`; the state starts
with the return slot. -/
@[expose, inline] public def whileLoopTotalAndDoneReturning {γ τ : Type u} {m : Type u → Type v}
    [ForIn m Lean.Loop Unit]
    (init : Option γ × τ) (f : Unit → Option γ × τ → m (ForInStep (Option γ × τ)))
    (inv : τ → Pred) (done : τ → Pred)
    (measure : τ → Named.Measure) : m (Option γ × τ) :=
  forIn Lean.Loop.mk init f

end Gadget

section StepPost
variable {β : Type u} {Pred : Type u₁} [Assertion Pred]

/-- The postcondition of one loop iteration: continuing (`.yield`) establishes `next`, and leaving
the loop (`.done`, from `break`, `return` or a `while` condition turning false) establishes
`exit`. -/
@[expose, reducible] public def stepPost (next exit : β → Pred) : ForInStep β → Pred
  | .yield b' => next b'
  | .done b' => exit b'

/-- `stepPost` for a loop with a termination measure: continuing from `b` re-establishes `inv`
and decreases `measure`. -/
@[expose, reducible] public noncomputable def stepPostDecreasing (inv : β → Pred)
    (measure : β → Named.Measure) (exit : β → Pred) (b : β) : ForInStep β → Pred :=
  stepPost (fun b' => match measure b, measure b' with
    | ⟨name, stx, current⟩, ⟨_, _, next⟩ => ⌜Named.mk name stx (next < current)⌝ ⊓ inv b') exit

/-- `inv` on the mutable variables of a state that has not returned. A loop only continues from
such states, since a `return` leaves it. -/
@[expose, reducible] public noncomputable def noReturn {γ τ : Type u} (inv : τ → Pred) :
    Option γ × τ → Pred
  | (none, s) => inv s
  | (some _, _) => ⊥

/-- Where leaving a loop whose body can `return` leads: a `return` (the slot holds a value) to the
code after the loop, which returns it, and any other exit to `done`. -/
@[expose, reducible] public def onExit {γ τ : Type u} (Q : Option γ × τ → Pred) (done : τ → Pred) :
    Option γ × τ → Pred
  | (some r, s) => Q (some r, s)
  | (none, s) => done s

end StepPost

end Loop
