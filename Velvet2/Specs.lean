import Lean
import Velvet2.Named
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.SpecLemmas

open Std.Internal.Do

def invariantGadget {m : Type u → Type v} [Monad m] (_inv : Prop) : m PUnit := pure ⟨⟩
def decreasingGadget {m : Type u → Type v} [Monad m]
    (_measure : Named.Measure) : m PUnit := pure ⟨⟩
def onDoneGadget {m : Type u → Type v} [Monad m] (_done : Prop) : m PUnit := pure ⟨⟩

/-- A runtime no-op that introduces an assertion into verification conditions. -/
def assertGadget {m : Type u → Type v} [Monad m] {_Pred : Type w}
    (_assertion : _Pred) : m PUnit := pure ⟨⟩

namespace Velvet2.Spec

open Lean.Order

/--
Checking an assertion requires the assertion itself and makes it available when
proving the continuation.
-/
@[spec]
theorem assertGadgetSpec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [Frame Pred] (assertion : Pred) {post : PUnit → Pred} {epost : EPred} :
    Triple (_root_.assertGadget (m := m) assertion)
      (assertion ⊓ (assertion ⇨ post ⟨⟩)) post epost := by
  simpa [_root_.assertGadget] using
    (Triple.pure (m := m)
      (pre := assertion ⊓ (assertion ⇨ post ⟨⟩))
      (post := post) (epost := epost) (a := ⟨⟩)
      (h := himp_sound assertion (post ⟨⟩)))

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
    {inv done : β → Prop} {measure : β → Named.Measure}
    {f : Unit → β → Option (ForInStep β)}
    (step : ∀ b,
      Std.Internal.Do.Triple (loopBody f b)
        (inv b)
        (fun r => match r with
          | .yield b' =>
              match measure b, measure b' with
              | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
                  Named.mk name stx (next < current) ∧ inv b'
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
              (Lean.Order.CompleteLattice.ofProp
                ((measure b').value < (measure b).value))
              (loopInv (.inl b'))
          | .done b' => loopInv (.inr b'))
        True := by
    intro b
    simpa [Named.mk, loopBody, loopInv] using step b
  simpa [invariantGadget, decreasingGadget, onDoneGadget, loopInv] using
    (Std.Internal.Do.Spec.forIn_loop
      (l := l)
      (init := init)
      (f := f)
      (measure := fun b => (measure b).value)
      (inv := loopInv)
      (einv := True)
      step')

@[spec]
def rangeLoopBody (f : α → β → Option (ForInStep β)) (i : α) (b : β) :
    Option (ForInStep β) :=
  f i b

open Std Std.PRange in


/--
Stdlib rco spec:

@[spec]
theorem Spec.forIn_rco {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv ⟨pref, cur::suff, h.symm⟩ b)
        (fun r => match r with
          | ForInStep.yield b' => inv ⟨pref ++ [cur], suff, by simp [h]⟩ b'
          | ForInStep.done b' => inv ⟨xs.toList, [], by simp⟩ b')
        epost) :
    Triple
      (forIn xs init f)
      (inv ⟨[], xs.toList, rfl⟩ init)
      (fun b => inv ⟨xs.toList, [], by simp⟩ b)
      epost := by
Specification for a finite closed-open range carrying inline invariants.
The invariant is indexed by the current range element. At the terminal cursor,
where there is no current element, `done` is used instead.
-/
@[spec 1100]
theorem forInRcoWithGadgets {α β : Type}
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β}
    {inv : α → β → Prop} {done : β → Prop}
    {f : α → β → Option (ForInStep β)}
    (step : ∀ pref cur suff (_h : xs.toList = pref ++ cur :: suff) b,
      Std.Internal.Do.Triple (rangeLoopBody f cur b)
        (inv cur b)
        (fun r => match r with
          | .yield b' => match suff with
            | [] => done b'
            | cur :: _ => inv cur b'
          | .done b' => done b')
        True) :
    Std.Internal.Do.Triple
      (forIn xs init fun i b => do
        invariantGadget (inv i b)
        onDoneGadget (done b)
        f i b)
      (match xs.toList with
        | [] => done init
        | cur :: _ => inv cur init)
      (fun b => done b)
      True := by
  let cursorInv : Std.Internal.Do.Invariant xs.toList β Prop := fun cursor b =>
    match cursor.suffix with
    | [] => done b
    | cur :: _ => inv cur b
  have step' : ∀ (pref : List α) (cur : α) (suff : List α)
      (h : xs.toList = pref ++ cur :: suff) (b : β),
      Std.Internal.Do.Triple (f cur b)
        (cursorInv ⟨pref, cur :: suff, h.symm⟩ b)
        (fun r => match r with
          | .yield b' => cursorInv ⟨pref ++ [cur], suff, by simp [h]⟩ b'
          | .done b' => cursorInv ⟨xs.toList, [], by simp⟩ b')
        True := by
    intro pref cur suff h b
    cases suff <;> simpa [rangeLoopBody, cursorInv] using step pref cur _ h b
  change Std.Internal.Do.Triple (forIn xs init f)
    (match xs.toList with
      | [] => done init
      | cur :: _ => inv cur init)
    (fun b => done b) True
  exact Std.Internal.Do.Spec.forIn_rco
    (xs := xs)
    (init := init)
    (f := f)
    (inv := cursorInv)
    (epost := True)
    step'

end Velvet2.Spec
