import Lean
import Velvet2.Named
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.SpecLemmas

open Std.Internal.Do

variable {m : Type u → Type v} {Pred EPred : Type u}

/-- Runtime no-op exposing a loop invariant to verification tooling. -/
def invariantGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_inv : Pred) : m PUnit := pure ⟨⟩

/-- Runtime no-op exposing a decreasing measure to verification tooling. -/
def decreasingGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_measure : Named.Measure) : m PUnit := pure ⟨⟩

/-- Runtime no-op exposing a loop's terminal assertion to verification tooling. -/
def onDoneGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_done : Pred) : m PUnit := pure ⟨⟩

/-- A runtime no-op that introduces an assertion into verification conditions. -/
def assertGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_assertion : Pred) : m PUnit := pure ⟨⟩

namespace Velvet2.Spec

open Lean.Order

/-- Specification for `assertGadget`: the precondition requires both `assertion` and the
Heyting implication `assertion ⇨ post ⟨⟩`, so the assertion is available when proving the
continuation. -/
@[spec]
theorem assertGadgetSpec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (assertion : Pred) [∀ a : Pred, PreservesSup (meet a)]
    {post : PUnit → Pred} {epost : EPred} :
    Triple (_root_.assertGadget (m := m) assertion)
      (assertion ⊓ (assertion ⇨ post ⟨⟩)) post epost := by
  simpa [_root_.assertGadget] using
    (Triple.pure (m := m)
      (pre := assertion ⊓ (assertion ⇨ post ⟨⟩))
      (post := post) (epost := epost) (a := ⟨⟩)
      (h := meet_himp_le))

/-- A reducible boundary around an annotated loop's executable body. -/
@[spec]
def loopBody (f : Unit → β → m (ForInStep β)) (b : β) : m (ForInStep β) :=
  f () b

/--
A specialization of Lean's `forIn_loop` specification which reads Velvet's
inline invariant, variant, and exit condition markers from the loop body.
The markers are runtime no-ops; their arguments make the annotations visible
to `vcgen` while it selects this rule.
-/
@[spec 1100]
theorem forInLoopWithGadgets {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {l : Lean.Loop} {init : β}
    {inv done : β → Pred} {measure : β → Named.Measure}
    {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (step : ∀ b,
      Std.Internal.Do.Triple (loopBody f b)
        (inv b)
        (fun r => match r with
          | .yield b' =>
              match measure b, measure b' with
              | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
                  ⌜Named.mk name stx (next < current)⌝ ⊓ inv b'
          | .done b' => inv b' ⊓ done b')
        einv) :
    Std.Internal.Do.Triple
      (forIn l init fun u b => do
        invariantGadget (inv b)
        decreasingGadget (measure b)
        onDoneGadget (done b)
        f u b)
      (inv init)
      (fun b => inv b ⊓ done b)
      einv := by
  let loopInv := Std.Internal.Do.RepeatInvariant.ofInvariantAndBreak inv done
  have step' : ∀ b,
      Std.Internal.Do.Triple (f () b)
        (loopInv (.inl b))
        (fun r => match r with
          | .yield b' =>
              ⌜(measure b').value < (measure b).value⌝ ⊓ loopInv (.inl b')
          | .done b' => loopInv (.inr b'))
        einv := by
    intro b
    simpa [Named.mk, loopBody, loopInv] using step b
  simpa [invariantGadget, decreasingGadget, onDoneGadget, loopInv] using
    (Std.Internal.Do.Spec.forIn_loop
      (l := l)
      (init := init)
      (f := f)
      (measure := fun b => (measure b).value)
      (inv := loopInv)
      (einv := einv)
      step')

/-- Separate transparent wrappers for the last and successor range-step premises. Distinct spec
proof keys prevent VCGen's cached unfolding rule for one local cursor context from being reused in
the other. -/
@[spec]
def rangeLoopBodyLast (f : α → β → m (ForInStep β)) (i : α) (b : β) :
    m (ForInStep β) :=
  f i b

@[spec]
def rangeLoopBodyMore (f : α → β → m (ForInStep β)) (i : α) (b : β) :
    m (ForInStep β) :=
  f i b

open Std Std.PRange in
/-- Range-loop specification yielding separate, match-free initialization, last-element, and
successor VCs. The initial assertion is a meet of guarded empty/nonempty obligations; after lattice
normalization these become ordinary implications rather than a match on `xs.toList`.

The step premises use distinct transparent wrappers because reusing one wrapper spec in both local
cursor contexts can make VCGen's cached unfolding rule retain a free variable from the first
context. -/
@[spec 1100]
theorem forInRcoWithGadgets {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred]
    [∀ a : Pred, Lean.Order.PreservesSup (Lean.Order.meet a)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {α β : Type u}
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β}
    {inv : α → β → Pred} {done : β → Pred}
    {f : α → β → m (ForInStep β)} {einv : EPred}
    (last : ∀ pref cur (_h : xs.toList = pref ++ [cur]) b,
      Std.Internal.Do.Triple (rangeLoopBodyLast f cur b)
        (inv cur b)
        (fun r => match r with
          | .yield b' => done b'
          | .done b' => done b')
        einv)
    (more : ∀ pref cur next tail (_h : xs.toList = pref ++ cur :: next :: tail) b,
      Std.Internal.Do.Triple (rangeLoopBodyMore f cur b)
        (inv cur b)
        (fun r => match r with
          | .yield b' => inv next b'
          | .done b' => done b')
        einv) :
    Std.Internal.Do.Triple
      (forIn xs init fun i b => do
        invariantGadget (inv i b)
        onDoneGadget (done b)
        f i b)
      ((⌜xs.toList = []⌝ ⇨ done init) ⊓
        ⨅ cur, ⨅ tail, ⌜xs.toList = cur :: tail⌝ ⇨ inv cur init)
      (fun b => done b)
      einv := by
  let cursorInv : Std.Internal.Do.Invariant xs.toList β Pred := fun cursor b =>
    match cursor.suffix with
    | [] => done b
    | cur :: _ => inv cur b
  have step : ∀ (pref : List α) (cur : α) (suff : List α)
      (h : xs.toList = pref ++ cur :: suff) (b : β),
      Std.Internal.Do.Triple (f cur b)
        (cursorInv ⟨pref, cur :: suff, h.symm⟩ b)
        (fun r => match r with
          | .yield b' => cursorInv ⟨pref ++ [cur], suff, by simp [h]⟩ b'
          | .done b' => cursorInv ⟨xs.toList, [], by simp⟩ b')
        einv := by
    intro pref cur suff h b
    cases suff with
    | nil => simpa [rangeLoopBodyLast, cursorInv] using last pref cur h b
    | cons next tail => simpa [rangeLoopBodyMore, cursorInv] using more pref cur next tail h b
  have loop : Std.Internal.Do.Triple
      (forIn xs init fun i b => do
        invariantGadget (inv i b)
        onDoneGadget (done b)
        f i b)
      (match xs.toList with
        | [] => done init
        | cur :: _ => inv cur init)
      (fun b => done b)
      einv := by
    simpa [invariantGadget, onDoneGadget, cursorInv] using
      (Std.Internal.Do.Spec.forIn_rco
        (xs := xs)
        (init := init)
        (f := f)
        (inv := cursorInv)
        (epost := einv)
        step)
  apply Std.Internal.Do.Triple.intro
  apply Lean.Order.PartialOrder.rel_trans (y := match xs.toList with
    | [] => done init
    | cur :: _ => inv cur init)
  · have topHimpLe (x : Pred) : ((⊤ : Pred) ⇨ x) ⊑ x := by
      apply Lean.Order.PartialOrder.rel_trans
        (y := (⊤ : Pred) ⊓ ((⊤ : Pred) ⇨ x))
      · exact Lean.Order.le_meet _ _ _ (Lean.Order.le_top _) Lean.Order.PartialOrder.rel_refl
      · exact Lean.Order.meet_himp_le
    have himpOfTrueLe (p : Prop) (hp : p) (x : Pred) : (⌜p⌝ ⇨ x) ⊑ x := by
      simpa [Lean.Order.CompleteLattice.ofProp, hp] using topHimpLe x
    cases hxs : xs.toList with
    | nil =>
      apply Lean.Order.PartialOrder.rel_trans (Lean.Order.meet_le_left _ _)
      simpa [hxs] using himpOfTrueLe (xs.toList = []) hxs (done init)
    | cons cur tail =>
      change
        ((⌜cur :: tail = []⌝ ⇨ done init) ⊓
          ⨅ cur', ⨅ tail', ⌜cur :: tail = cur' :: tail'⌝ ⇨ inv cur' init) ⊑ inv cur init
      apply Lean.Order.PartialOrder.rel_trans (Lean.Order.meet_le_right _ _)
      apply Lean.Order.PartialOrder.rel_trans
        (Lean.Order.iInf_le
          (fun cur' : α => ⨅ tail', ⌜cur :: tail = cur' :: tail'⌝ ⇨ inv cur' init) cur)
      apply Lean.Order.PartialOrder.rel_trans
        (Lean.Order.iInf_le
          (fun tail' : List α => ⌜cur :: tail = cur :: tail'⌝ ⇨ inv cur init) tail)
      exact himpOfTrueLe _ rfl _
  · exact loop.le_wp

end Velvet2.Spec
