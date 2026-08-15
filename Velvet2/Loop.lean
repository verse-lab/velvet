import Velvet2.Specs

/-!
# Partial (no-measure) loops

`while'` loops may omit `decreasing` under partial correctness. The native Lean `while` lowers to
`Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant … noMeasure`, but Std has no sound
measure-free spec for it: `repeatM` is pinned to `Classical.choose` of an *arbitrary* fixed point,
so an invariant-only rule is unsound.

Instead we own the loop (like `loom-dev`): `Velvet2.Loop.forIn.loop` is defined with
`partial_fixpoint`, so it computes the *least* fixed point, and we prove a partial-correctness rule
for it directly.

Wiring: the do elaborator lowers `while'` (no `decreasing`) to
`Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant … noMeasure`. That gadget's body was
already elaborated to `Lean.Loop.forIn` (the arbitrary-fixed-point one), so a `ForIn` override does
not change it. Instead, the `macro_rules` at the bottom of this file intercepts the *syntax* of that
call before elaboration and redirects the `noMeasure` case to `Velvet2.Loop.forInLoopWithInvariantAndVariant`,
which is built on `forIn.loop`. The measure case is left on the Std gadget, so total loops keep
working unchanged.
-/

open Std.Internal.Do
open Std.Internal.Do.Assertion
open Lean.Order
open Std.Internal.Do.CompleteLattice

universe u v

namespace Velvet2.Loop

/-- Our own least-fixed-point loop: `partial_fixpoint` over the loop body. -/
def forIn.loop {β : Type u} {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => forIn.loop f b
  partial_fixpoint

/-- `forIn` wrapper matching `Lean.Loop.forIn`'s shape. -/
def forIn {β : Type u} {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  forIn.loop f init

/-- Partial-correctness rule for our loop over `Option`: the invariant holds on exit, with no
termination measure. `einv` is specialized to `True` (the partial `none` postcondition). -/
theorem Option.forInLoop_partial {β : Type u}
    (f : Unit → β → Option (ForInStep β)) (init : β)
    (inv : β ⊕ β → Prop)
    (step : ∀ b, Triple (f () b) (inv (.inl b))
      (fun r => match r with
        | .yield b' => inv (.inl b')
        | .done b' => inv (.inr b')) True) :
    Triple (forIn.loop (m := Option) f init) (inv (.inl init))
      (fun b => inv (.inr b)) True := by
  let post : β → Prop := fun b => inv (.inr b)
  let mid : ForInStep β → Prop := fun r => match r with
    | .yield b' => inv (.inl b')
    | .done b' => inv (.inr b')
  let k : (β → Option β) → ForInStep β → Option β := fun loop r => match r with
    | .done b => pure b
    | .yield b => loop b
  let body : (β → Option β) → β → Option β := fun loop b => f () b >>= k loop
  let motive : (β → Option β) → Prop := fun loop => ∀ init, inv (.inl init) → (loop init).elim True post
  have hadm : Lean.Order.admissible motive := by
    dsimp [motive]
    apply Lean.Order.admissible_pi_apply
      (P := fun init (x : Option β) => inv (.inl init) → x.elim True post)
    intro init
    apply Lean.Order.admissible_flatOrder
      (P := fun x : Option β => inv (.inl init) → x.elim True post)
    simp [Lean.Order.FlatOrder.mk]
  have hstep : ∀ loop, motive loop → motive (body loop) := by
    intro loop ih init hpre
    have hbody : (f () init).elim True mid := by
      simpa [mid, Std.Internal.Do.WP.wp, Std.Internal.Do.WP.wpTrans] using (step init).le_wp hpre
    dsimp [body]
    simp only [Option.bind]
    cases hf : f () init with
    | none => trivial
    | some r =>
        have hmid : mid r := by simpa [hf] using hbody
        cases hr : r with
        | done b =>
            simpa [k, mid, post, hr] using hmid
        | yield b =>
            exact ih b (by simpa [k, mid, hr] using hmid)
  have h := forIn.loop.fixpoint_induct (f := f) (motive := motive) hadm hstep
  exact ⟨fun hpre => h init hpre⟩

/-
/-- Total-correctness rule for our loop: well-founded induction on the `RepeatVariant` measure. -/
theorem forInLoop_total
    {β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : RepeatVariant β Pred) (inv : β ⊕ β → Pred) (einv : EPred)
    (f : Unit → β → m (ForInStep β)) (init : β)
    (step : ∀ b (mb : measure.γ), Triple (f () b)
        (measure.EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b')) einv) :
    Triple (forIn.loop f init) (inv (.inl init)) (fun b => inv (.inr b)) einv := by
  refine Triple.intro <| measure.le_of_total_le init ?_
  refine iSup_le _ _ fun minit => ?_
  suffices key : ∀ (n : measure.γ), Acc measure.rel n → ∀ (b : β),
      Triple (forIn.loop f b) (measure.EvalsTo b n ⊓ inv (.inl b)) (fun b => inv (.inr b)) einv
    from (key minit (measure.wf.apply minit) init).le_wp
  intro n hacc
  induction hacc with
  | intro n _ ih =>
    intro b
    rw [forIn.loop.eq_1]
    refine Triple.bind (f := fun r => match r with
      | .done b' => pure b'
      | .yield b' => forIn.loop f b')
      (f () b) (fun r => match r with
        | .yield b' => measure.EvalsBelow b' n ⊓ inv (.inl b')
        | .done b' => inv (.inr b'))
      (step b n) ?_
    intro r
    cases r with
    | yield b' =>
        refine Triple.intro ?_
        refine iSup_meet_le fun mb' => ?_
        rw [meet_comm (P := measure.EvalsTo b' mb'), meet_assoc]
        exact ofProp_meet_le_left fun hlt => (ih mb' hlt b').le_wp
    | done b' =>
        exact Triple.pure b' PartialOrder.rel_refl
-/

/-- Our version of the annotated loop gadget, built on `forIn.loop`. -/
@[inline] def forInLoopWithInvariantAndVariant {β : Type u} {m : Type u → Type v} {Pred : Type uₚ}
    {Fun : Type} [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (_l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (_inv? : Option (RepeatInvariant β β Pred)) (_var? : Option (β → Fun)) : m β :=
  forIn.loop f init

/-- Partial spec for the `noMeasure` gadget, specialized to `Option`. -/
@[spec 1200]
theorem Spec.forInLoop_partial
    {β : Type u} {l : Lean.Loop} {init : β} {f : Unit → β → Option (ForInStep β)}
    (inv : β ⊕ β → Prop)
    (step : ∀ b, Triple (f () b) (inv (.inl b))
      (fun r => match r with
        | .yield b' => inv (.inl b')
        | .done b' => inv (.inr b')) True) :
    Triple
      (forInLoopWithInvariantAndVariant l init f
        (some (RepeatInvariant.mk inv)) Std.Internal.Do.Gadget.noMeasure)
      (inv (.inl init)) (fun b => inv (.inr b)) True := by
  unfold forInLoopWithInvariantAndVariant
  exact Option.forInLoop_partial f init inv step

end Velvet2.Loop

/-!
## HACK: redirecting the `noMeasure` loop gadget via `macro_rules`

`while'` (no `decreasing`) lowers through Lean's do elaborator to the *application*

    Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant l init f inv noMeasure

That is an ordinary `def` application, not a syntactic form, so overriding it with `macro_rules`
is a hack. It works only because `Lean.Elab.BuiltinDo.For.mkForInLoopWithInvariantAndVariant` builds
that application as **syntax** and then calls `Term.elabTermEnsuringType` on it; macro expansion runs
on that syntax before it becomes a term, so a `term`-level `macro_rules` fires.

This relies on an implementation detail of the do elaborator. The clean fix is to patch the
toolchain's `mkForInLoopWithInvariantAndVariant` to emit our gadget (or to vendor the do-loop
elaborator); until then, this interception is the least-invasive way to make `while'` use our
least-fixed-point loop in the partial case while leaving the total (measure) case on Std's gadget.
-/
macro_rules
  | `(term| Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant $l $init $f $inv
      Std.Internal.Do.Gadget.noMeasure) =>
      `(term| Velvet2.Loop.forInLoopWithInvariantAndVariant $l $init $f $inv
        Std.Internal.Do.Gadget.noMeasure)

#check Std.Internal.Do.Gadget.noMeasure
