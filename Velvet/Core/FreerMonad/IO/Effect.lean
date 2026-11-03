import Velvet.Core.FreerMonad.IO.Model
import Velvet.Core.Partial
import Velvet.Core.Ghost

open Std.WP Lean.Order WPPartial

/-- IO requests over a base monad `m`, whose actions are lifted in with `lift`. -/
inductive IOEff (E Err : Type) (m : Type → Type) : Type → Type 1 where
  | call {c : Type} {op : Type → Type} {Ev α : Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]
      {P : Protocol c op Ev Err} [Model c P E] (ch : c) (o : op α) : IOEff E Err m α
  | snapshot : IOEff E Err m (Ghost (Trace E))
  | lift {α : Type} (x : m α) : IOEff E Err m α

abbrev IOProgT (E Err : Type) (m : Type → Type) := FreerMonad (IOEff E Err m)

abbrev IOProg (E Err : Type) := IOProgT E Err Option

/-! `⇨` is a supremum, so these hold in any complete lattice, without the frame law. -/

theorem himp_mono_right' {α : Type} [CompleteLattice α] {a b b' : α} (h : b ⊑ b') : (a ⇨ b) ⊑ (a ⇨ b') :=
  sup_le _ fun _ hx => le_sup _ (PartialOrder.rel_trans hx h)

theorem ofProp_himp_le {α : Type} [CompleteLattice α] {p : Prop} (hp : p) (b : α) : (⌜p⌝ ⇨ b) ⊑ b :=
  sup_le _ fun x hx => PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (le_top x) (top_le_ofProp p hp)) PartialOrder.rel_refl) hx

section Effect
variable {E Err : Type} {m : Type → Type} {Pred EPred : Type}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

noncomputable instance instWPIOEff {α : Type} :
    WP (IOEff E Err m α) α (Trace E → Pred) ((Err → Trace E → Pred) × EPred) where
  wpTrans x := ⟨fun post epost h => match x with
    | @IOEff.call _ _ _ c _ _ _ _ _ _ P _ ch o =>
        ⌜P.allow ch (h.traceOf ch) o⌝ ⊓
          ((⨅ v, ⌜P.onReply ch (h.traceOf ch) o (.ok v)⌝ ⇨
              post v (h.recordFor ch (Channel.log c o (.ok v)))) ⊓
            ⨅ e, ⌜P.onReply ch (h.traceOf ch) o (.error e)⌝ ⇨
              epost.1 e (h.recordFor ch (Channel.log c o (.error e))))
    | .snapshot => post (Ghost.mk h) h
    | .lift x => wp x (fun a => post a h) epost.2⟩
  wp_trans_monotone x post post' epost epost' he hp h := by
    cases x with
    | call ch o =>
      exact meet_mono PartialOrder.rel_refl (meet_mono
        (le_iInf _ _ fun v => PartialOrder.rel_trans (iInf_le _ v) (himp_mono_right' (hp _ _)))
        (le_iInf _ _ fun e => PartialOrder.rel_trans (iInf_le _ e) (himp_mono_right' (he.1 _ _))))
    | snapshot => exact hp _ _
    | lift x => exact WP.wp_trans_monotone x _ _ _ _ he.2 (fun a => hp a h)

/- Divergence is taken at the level of the whole `IOModelT`, so loop rules and specs see the same
`div_pre` without having to unfold how it is built from `m`'s. -/
noncomputable instance instWPMonadIOProgT [∀ γ, CCPO (m γ)]
    {div_post : (Err → Trace E → Pred) × EPred} {div_pre : (Err → Trace E → Pred) × EPred → Trace E → Pred}
    [WPPartial (IOModelT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) div_post div_pre] :
    WPMonad (IOProgT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) :=
  FreerMonad.wpMonadInst (m := IOModelT E Err m) (div_post := div_post) (div_pre := div_pre)

end Effect

namespace IOProg

section Specs
variable {E Err : Type} {m : Type → Type} {Pred EPred : Type}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
  {div_post : (Err → Trace E → Pred) × EPred} {div_pre : (Err → Trace E → Pred) × EPred → Trace E → Pred}
  [WPPartial (IOModelT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) div_post div_pre]

/-- `⨅ h', ⌜h' = x⌝ ⇨ f h'` is `f x`. -/
theorem iInf_eq_himp_le (x : Trace E) (f : Trace E → Pred) : (⨅ h', ⌜h' = x⌝ ⇨ f h') ⊑ f x :=
  PartialOrder.rel_trans (iInf_le _ x) (ofProp_himp_le rfl _)

section Call
variable {c Ev α : Type} {op : Type → Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]
  {P : Protocol c op Ev Err} [Model c P E]

def call (ch : c) (o : op α) : IOProgT E Err m α := .vis (.call ch o) .ret

@[spec]
theorem call_spec (ch : c) (o : op α) {post : α → Trace E → Pred}
    {epost : (Err → Trace E → Pred) × EPred} :
    Triple (call (E := E) (m := m) ch o)
      (fun h => ⌜Named.mk `allow none (P.allow ch (h.traceOf ch) o)⌝ ⊓
        ((⨅ v, ⌜Named.mk `onReply none (P.onReply ch (h.traceOf ch) o (.ok v))⌝ ⇨
            ⨅ h', ⌜Named.mk `h_trace none (h' = h.recordFor ch (Channel.log c o (.ok v)))⌝ ⇨ post v h') ⊓
          ⨅ e, ⌜Named.mk `onReply none (P.onReply ch (h.traceOf ch) o (.error e))⌝ ⇨
            ⨅ h', ⌜Named.mk `h_trace none (h' = h.recordFor ch (Channel.log c o (.error e)))⌝ ⇨ epost.1 e h'))
      post epost :=
  Triple.intro fun _ => meet_mono PartialOrder.rel_refl (meet_mono
    (le_iInf _ _ fun v => PartialOrder.rel_trans (iInf_le _ v) (himp_mono_right' (iInf_eq_himp_le _ _)))
    (le_iInf _ _ fun e => PartialOrder.rel_trans (iInf_le _ e) (himp_mono_right' (iInf_eq_himp_le _ _))))

end Call

/-- The trace so far, as a ghost value for specs and invariants. -/
def snapshot : IOProgT E Err m (Ghost (Trace E)) := .vis .snapshot .ret

@[spec]
theorem snapshot_spec {post : Ghost (Trace E) → Trace E → Pred}
    {epost : (Err → Trace E → Pred) × EPred} :
    Triple (snapshot (E := E) (Err := Err) (m := m)) (fun h => post (Ghost.mk h) h) post epost :=
  Triple.intro fun _ => PartialOrder.rel_refl

/-- Run an action of the base monad; it does not touch the trace. -/
def lift {α : Type} (x : m α) : IOProgT E Err m α := .vis (.lift x) .ret

@[spec]
theorem lift_spec {α : Type} (x : m α) {post : α → Trace E → Pred}
    {epost : (Err → Trace E → Pred) × EPred} :
    Triple (lift (E := E) (Err := Err) x) (fun h => wp x (fun a => post a h) epost.2) post epost :=
  Triple.intro fun _ => PartialOrder.rel_refl

end Specs

instance {E Err : Type} {m : Type → Type} : MonadLift m (IOProgT E Err m) where
  monadLift := lift

section Lift
variable {E Err : Type} {m : Type → Type} {Pred EPred : Type}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
  {div_post : (Err → Trace E → Pred) × EPred} {div_pre : (Err → Trace E → Pred) × EPred → Trace E → Pred}
  [WPPartial (IOModelT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) div_post div_pre]

@[spec]
theorem monadLift_spec {α : Type} (x : m α) {post : α → Trace E → Pred}
    {epost : (Err → Trace E → Pred) × EPred} :
    Triple (MonadLift.monadLift x : IOProgT E Err m α) (fun h => wp x (fun a => post a h) epost.2) post epost :=
  lift_spec x

end Lift

end IOProg
