import Lean
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.SpecLemmas

open Std.Internal.Do

def invariantGadget {m : Type u → Type v} [Monad m] (_inv : Prop) : m PUnit := pure ⟨⟩
def decreasingGadget {m : Type u → Type v} [Monad m] (_measure : Nat) : m PUnit := pure ⟨⟩
def onDoneGadget {m : Type u → Type v} [Monad m] (_done : Prop) : m PUnit := pure ⟨⟩

namespace Velvet2.Spec

/-- A reducible boundary around an annotated loop's executable body. -/
@[spec]
def loopBody (f : Unit → β → Option (ForInStep β)) (b : β) : Option (ForInStep β) :=
  f () b

/--
A specialization of Lean's `forIn_loop` specification which reads Velvet's
inline invariant, variant, and exit condition markers from the loop body.
The markers are runtime no-ops; their arguments make the annotations visible
to `vcgen` while it selects this rule.
-/
@[spec 1100]
theorem forInLoopWithGadgets {β : Type}
    {l : Lean.Loop} {init : β}
    {inv done : β → Prop} {measure : β → Nat}
    {f : Unit → β → Option (ForInStep β)}
    (step : ∀ b,
      Std.Internal.Do.Triple (loopBody f b)
        (inv b)
        (fun r => match r with
          | .yield b' => measure b' < measure b ∧ inv b'
          | .done b' => inv b' ∧ done b')
        True) :
    Std.Internal.Do.Triple
      (forIn l init fun u b => do
        invariantGadget (inv b)
        decreasingGadget (measure b)
        onDoneGadget (done b)
        f u b)
      (inv init)
      (fun b => inv b ∧ done b)
      True := by
  let loopInv := Std.Internal.Do.RepeatInvariant.ofInvariantAndBreak inv done
  have step' : ∀ b,
      Std.Internal.Do.Triple (f () b)
        (loopInv (.inl b))
        (fun r => match r with
          | .yield b' => Lean.Order.meet
              (Lean.Order.CompleteLattice.ofProp (measure b' < measure b))
              (loopInv (.inl b'))
          | .done b' => loopInv (.inr b'))
        True := by
    intro b
    simpa [loopBody, loopInv] using step b
  simpa [invariantGadget, decreasingGadget, onDoneGadget, loopInv] using
    (Std.Internal.Do.Spec.forIn_loop
      (l := l)
      (init := init)
      (f := f)
      (measure := measure)
      (inv := loopInv)
      (einv := True)
      step')

open Std Std.PRange in
/--
A specialization of Lean's finite closed-open range specification which reads
Velvet's state invariant from the marker at the start of the loop body.
Termination and exhaustion are supplied by `Std.Rco`, so this rule needs no
variant or separate `done_with` annotation.
-/
@[spec 1100]
theorem forInRcoWithInvariantGadget {α β : Type}
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β}
    {inv : β → Prop}
    {f : α → β → Option (ForInStep β)}
    (step : ∀ i b, inv b →
      (f i b).elim True fun r => match r with
        | .yield b' => inv b'
        | .done b' => inv b') :
    Std.Internal.Do.Triple
      (forIn xs init fun i b => do
        invariantGadget (inv b)
        f i b)
      (inv init)
      (fun b => inv b)
      True := by
  let cursorInv : Std.Internal.Do.Invariant xs.toList β Prop := fun _ b => inv b
  have step' : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Std.Internal.Do.Triple (f cur b)
        (cursorInv ⟨pref, cur :: suff, h.symm⟩ b)
        (fun r => match r with
          | .yield b' => cursorInv ⟨pref ++ [cur], suff, by simp [h]⟩ b'
          | .done b' => cursorInv ⟨xs.toList, [], by simp⟩ b')
        True := by
    intro _ cur _ _ b
    apply Std.Internal.Do.Triple.intro
    intro hinv
    exact step cur b hinv
  simpa [invariantGadget, cursorInv] using
    (Std.Internal.Do.Spec.forIn_rco
      (xs := xs)
      (init := init)
      (f := f)
      (inv := cursorInv)
      (epost := True)
      step')

end Velvet2.Spec
