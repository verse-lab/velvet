module

public import Velvet.Core.FreerMonad.NonDet
public import Velvet.Core.FreerMonad.Loop

/-!
# Loop specifications for `NonDetT`

Each spec is the `FreerMonad` spec of the same name, carried across `NonDetT.toFreer`.
-/

@[expose] public section

open Std.WP Lean.Order WPPartial Loop Loop.Gadget

universe u v

namespace NonDetT

variable {mode : NondetMode} {m : Type u → Type v} {Pred EPred : Type u}
  {div_post : EPred} {div_pre : EPred → Pred}
  [Monad m] [Assertion Pred] [∀ P : Pred, PreservesSup (meet P)]
  [Assertion EPred] [WPMonad m Pred EPred]
  [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]

@[spec 1250]
theorem Spec.whileLoopPartial
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv Q) einv) :
    Triple (whileLoopPartial init f inv) (inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartial (f := fun u b => (f u b).toFreer)
    inv hdiv fun b => triple_iff_toFreer.1 (step b)

@[spec 1250]
theorem Spec.whileLoopPartialAndDone
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv done) einv) :
    Triple (whileLoopPartialAndDone init f inv done) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartialAndDone (f := fun u b => (f u b).toFreer)
    inv done hdiv fun b => triple_iff_toFreer.1 (step b)

@[spec 1250]
theorem Spec.whileLoopPartialAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) (onExit Q done)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (whileLoopPartialAndDoneReturning init f inv done) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartialAndDoneReturning
    (f := fun u b => (f u b).toFreer) inv done hdiv (fun s => triple_iff_toFreer.1 (step s)) hD

@[spec 1250]
theorem Spec.whileLoopPartialReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) Q) einv) :
    Triple (whileLoopPartialReturning init f inv) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopPartialReturning
    (f := fun u b => (f u b).toFreer) inv hdiv fun s => triple_iff_toFreer.1 (step s)

@[spec 1250]
theorem Spec.whileLoopTotal
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure Q b) einv) :
    Triple (whileLoopTotal init f inv measure) (inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotal (f := fun u b => (f u b).toFreer)
    inv measure fun b => triple_iff_toFreer.1 (step b)

@[spec 1250]
theorem Spec.whileLoopTotalAndDone
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure done b) einv) :
    Triple (whileLoopTotalAndDone init f inv done measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotalAndDone (f := fun u b => (f u b).toFreer)
    inv done measure fun b => triple_iff_toFreer.1 (step b)

@[spec 1250]
theorem Spec.whileLoopTotalAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) (none, s)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (whileLoopTotalAndDoneReturning init f inv done measure) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotalAndDoneReturning
    (f := fun u b => (f u b).toFreer) inv done measure (fun s => triple_iff_toFreer.1 (step s)) hD

@[spec 1250]
theorem Spec.whileLoopTotalReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q (none, s)) einv) :
    Triple (whileLoopTotalReturning init f inv measure) (noReturn inv init) Q einv :=
  triple_iff_toFreer.2 <| FreerMonad.Spec.whileLoopTotalReturning
    (f := fun u b => (f u b).toFreer) inv measure fun s => triple_iff_toFreer.1 (step s)

end NonDetT

end
