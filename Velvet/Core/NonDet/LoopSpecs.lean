module

public import Velvet.Core.FreerMonad.NonDet
public import Velvet.Core.FreerMonad.Loop

/-!
# Loop specifications over `NonDetT`

The specifications `velvet_vcgen` applies to Velvet's `while` gadgets in `NonDetT`. Each is the
`FreerMonad` spec of the same name in `FreerMonad/Loop.lean`, carried across `NonDetT.toFreer`.
`for` loops need no specs of their own: the ones in `Loop/Specs.lean` apply to any monad with a WP.
-/

open Std.WP Lean.Order Loop Loop.Gadget WPPartial

universe u v w z

@[expose] public section

namespace NonDetT

section Specs
variable {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
  [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
  [Assertion EPred] [WPMonad m Pred EPred]
  [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]

/-- The spec for `Gadget.whileLoopPartial` without `done_with`: every exit goes straight to the code
after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopPartial
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv Q) einv) :
    Triple (Gadget.whileLoopPartial init f inv none) (inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartial (f := fun u b => (f u b).toFreer)
    inv hdiv fun b => triple_iff_toFreer.1 (step b)

/-- The spec for `Gadget.whileLoopPartial` with `done_with`: every exit establishes `done`, which the
code after the loop starts from. -/
@[spec 1250]
public theorem Spec.whileLoopPartialAndDone
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv done) einv) :
    Triple (Gadget.whileLoopPartial init f inv (some done)) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartialAndDone (f := fun u b => (f u b).toFreer)
    inv done hdiv fun b => triple_iff_toFreer.1 (step b)

/-- The spec for `Gadget.whileLoopPartialReturning` with `done_with`: a `return` goes straight to the
code after the loop, and every other exit establishes `done`. -/
@[spec 1250]
public theorem Spec.whileLoopPartialAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) (onExit Q done)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (Gadget.whileLoopPartialReturning init f inv (some done)) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartialAndDoneReturning (f := fun u b => (f u b).toFreer)
    inv done hdiv (fun s => triple_iff_toFreer.1 (step s)) hD

/-- The spec for `Gadget.whileLoopPartialReturning` without `done_with`: every exit goes straight to
the code after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopPartialReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) Q) einv) :
    Triple (Gadget.whileLoopPartialReturning init f inv none) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartialReturning (f := fun u b => (f u b).toFreer)
    inv hdiv fun s => triple_iff_toFreer.1 (step s)

/-- The spec for `Gadget.whileLoopTotal` without `done_with`: every exit goes straight to the code
after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopTotal
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure Q b) einv) :
    Triple (Gadget.whileLoopTotal init f inv none measure) (inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotal (f := fun u b => (f u b).toFreer)
    inv measure fun b => triple_iff_toFreer.1 (step b)

/-- The spec for `Gadget.whileLoopTotal` with `done_with`: every exit establishes `done`, which the
code after the loop starts from. -/
@[spec 1250]
public theorem Spec.whileLoopTotalAndDone
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure done b) einv) :
    Triple (Gadget.whileLoopTotal init f inv (some done) measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotalAndDone (f := fun u b => (f u b).toFreer)
    inv done measure fun b => triple_iff_toFreer.1 (step b)

/-- The spec for `Gadget.whileLoopTotalReturning` with `done_with`: a `return` goes straight to the
code after the loop, and every other exit establishes `done`. -/
@[spec 1250]
public theorem Spec.whileLoopTotalAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) (none, s)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (Gadget.whileLoopTotalReturning init f inv (some done) measure) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotalAndDoneReturning (f := fun u b => (f u b).toFreer)
    inv done measure (fun s => triple_iff_toFreer.1 (step s)) hD

/-- The spec for `Gadget.whileLoopTotalReturning` without `done_with`: every exit goes straight to
the code after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopTotalReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q (none, s)) einv) :
    Triple (Gadget.whileLoopTotalReturning init f inv none measure) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotalReturning (f := fun u b => (f u b).toFreer)
    inv measure fun s => triple_iff_toFreer.1 (step s)

end Specs

end NonDetT

end
