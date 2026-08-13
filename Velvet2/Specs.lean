import Velvet2.Named
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.SpecLemmas

open Std.Internal.Do

variable {m : Type u → Type v} {Pred EPred : Type u}

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

/--
Velvet's named specialization of Lean's native annotated-repeat-loop gadget. The program carries
its invariant and variant as explicit gadget arguments, while this wrapper specification converts
the `Named.Measure` payload to Lean's ordinary natural-number repeat variant and restores the name
on the generated strict-decrease proposition.
-/
@[spec 1200]
theorem forInLoopWithNamedInvariantAndVariant
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {l : Lean.Loop} {init : β}
    {inv : β ⊕ β → Pred} {measure : β → Named.Measure}
    {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (step : ∀ b,
      Std.Internal.Do.Triple (f () b)
        (inv (.inl b))
        (fun r => match r with
          | .yield b' =>
              match measure b, measure b' with
              | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
                  ⌜Named.mk name stx (next < current)⌝ ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Std.Internal.Do.Triple
      (Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant
        l init f (some (Std.Internal.Do.RepeatInvariant.mk inv)) (some measure))
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  let loopMeasure := Std.Internal.Do.RepeatVariant.ofMeasure (Pred := Pred)
    (fun b => (measure b).value)
  have step' : ∀ b (mb : loopMeasure.γ),
      Std.Internal.Do.Triple (f () b)
        (loopMeasure.EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' => loopMeasure.EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv := by
    intro b mb
    apply Std.Internal.Do.Triple.intro
    apply Std.Internal.Do.CompleteLattice.ofProp_meet_le_left
    intro h
    subst mb
    have natRel (a b : Nat) : WellFoundedRelation.rel a b = (a < b) := rfl
    simpa [Named.mk_eq, loopMeasure,
      Std.Internal.Do.RepeatVariant.evalsBelow_ofMeasure, natRel] using (step b).le_wp
  unfold Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant
  exact Std.Internal.Do.Spec.forIn_loop loopMeasure inv einv step'

/-- Select the current-element invariant or the final assertion from a native collection-loop
cursor. Keeping this selection behind a stable head symbol lets the range wrapper specification
recover Velvet's two named clauses without inspecting the executable loop body. -/
def rangeInvariantValue (inv : α → Pred) (done : Pred) (suff : List α) : Pred :=
  match suff with
  | [] => done
  | cur :: _ => inv cur

open Std Std.PRange in
/-- Named specialization of Lean's native collection-loop gadget for closed-open ranges, yielding
separate, match-free initialization, last-element, and successor VCs. The initial assertion is a
meet of guarded empty/nonempty obligations; after lattice normalization these become ordinary
implications rather than a match on `xs.toList`.

The step premises use distinct transparent wrappers because reusing one wrapper spec in both local
cursor contexts can make VCGen's cached unfolding rule retain a free variable from the first
context. -/
@[spec 1200]
theorem forInRcoWithNamedInvariant {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [LawfulMonad m] [Assertion Pred]
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
      Std.Internal.Do.Triple (f cur b)
        (inv cur b)
        (fun r => match r with
          | .yield b' => done b'
          | .done b' => done b')
        einv)
    (more : ∀ pref cur next tail (_h : xs.toList = pref ++ cur :: next :: tail) b,
      Std.Internal.Do.Triple (f cur b)
        (inv cur b)
        (fun r => match r with
          | .yield b' => inv next b'
          | .done b' => done b')
        einv) :
    Std.Internal.Do.Triple
      (Std.Internal.Do.Gadget.forInPureWithInvariant xs init f
        (fun _pref suff b => rangeInvariantValue (fun cur => inv cur b) (done b) suff))
      ((⌜xs.toList = []⌝ ⇨ done init) ⊓
        ⨅ cur, ⨅ tail, ⌜xs.toList = cur :: tail⌝ ⇨ inv cur init)
      (fun b => done b)
      einv := by
  let cursorInv : Std.Internal.Do.Invariant α β Pred := fun _pref suff b =>
    rangeInvariantValue (fun cur => inv cur b) (done b) suff
  have step : ∀ (pref : List α) (cur : α) (suff : List α)
      (h : xs.toList = pref ++ cur :: suff) (b : β),
      Std.Internal.Do.Triple (f cur b)
        (cursorInv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => cursorInv (pref ++ [cur]) suff b'
          | .done b' => cursorInv xs.toList [] b')
        einv := by
    intro pref cur suff h b
    cases suff with
    | nil => simpa [cursorInv, rangeInvariantValue] using last pref cur h b
    | cons next tail => simpa [cursorInv, rangeInvariantValue] using more pref cur next tail h b
  have rangeEq : (forIn xs init f : m β) = forIn xs.toList init f := by
    calc
      forIn xs init f = forIn' xs init (fun a _ b => f a b) :=
        (forIn'_eq_forIn xs init (fun a _ b => f a b) f (by intros; rfl)).symm
      _ = forIn' xs.toList init (fun a _ b => f a b) :=
        Std.Rco.forIn'_eq_forIn'_toList
      _ = forIn xs.toList init f :=
        forIn'_eq_forIn xs.toList init (fun a _ b => f a b) f (by intros; rfl)
  have loop : Std.Internal.Do.Triple
      (Std.Internal.Do.Gadget.forInPureWithInvariant xs init f cursorInv)
      (match xs.toList with
        | [] => done init
        | cur :: _ => inv cur init)
      (fun b => done b)
      einv := by
    unfold Std.Internal.Do.Gadget.forInPureWithInvariant
    simpa [cursorInv, rangeInvariantValue, rangeEq] using
      (Std.Internal.Do.Spec.forIn_list
        (xs := xs.toList)
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
