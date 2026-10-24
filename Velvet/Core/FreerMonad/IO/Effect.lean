import Velvet.Core.FreerMonad.IO.Model
import Velvet.Core.Partial
import Velvet.Core.Ghost

open Std.WP Lean.Order

universe v

inductive IOEff (E Err : Type) : Type → Type 1 where
  | call {c : Type} {op : Type → Type} {Ev α : Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]
      {P : Protocol c op Ev Err} [Model c P E] (ch : c) (o : op α) : IOEff E Err α
  | snapshot : IOEff E Err (Ghost (Trace E))

abbrev IOProg (E Err : Type) := FreerMonad (IOEff E Err)

section Effect
variable {E Err : Type}

noncomputable instance instWPIOEff {α : Type} :
    WP (IOEff E Err α) α (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop)) where
  wpTrans x := ⟨fun post epost h => match x with
    | @IOEff.call _ _ c _ _ _ _ _ _ P _ ch o =>
        P.allow ch (h.traceOf ch) o ∧
        (∀ v, P.onReply ch (h.traceOf ch) o (.ok v) → post v (h.recordFor ch (Channel.log c o (.ok v)))) ∧
        ∀ e, P.onReply ch (h.traceOf ch) o (.error e) →
          epost.1 e (h.recordFor ch (Channel.log c o (.error e)))
    | .snapshot => post (Ghost.mk h) h⟩
  wp_trans_monotone x post post' epost epost' he hp h := by
    cases x with
    | call ch o =>
      exact fun ⟨ha, hk, hn⟩ => ⟨ha, fun v hv => hp _ _ (hk v hv), fun e he' => he.1 e _ (hn e he')⟩
    | snapshot => exact hp _ _

end Effect

noncomputable instance instWPMonadIOFreer {E Err : Type} {es : Type → Type v}
    [∀ α, WP (es α) α (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop))] :
    WPMonad (FreerMonad es) (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop)) :=
  FreerMonad.wpMonadInst (m := IOModel E Err)
    (div_post := ((fun _ => ⊥), fun _ => True)) (div_pre := fun X _ => X.2 ())

theorem FreerMonad.wp_eq_wp {E Err : Type} {es : Type → Type v}
    [∀ α, WP (es α) α (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop))]
    {α : Type} (x : FreerMonad es α) (post : α → Trace E → Prop) (epost : (Err → Trace E → Prop) × (Unit → Prop)) :
    Std.WP.wp x post epost =
      FreerMonad.wp (m := IOModel E Err) (div_post := ((fun _ => ⊥), fun _ => True))
        (div_pre := fun X _ => X.2 ()) x post epost :=
  rfl

namespace IOProg

section Call
variable {E Err c Ev α : Type} {op : Type → Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]
  {P : Protocol c op Ev Err} [Model c P E]

def call (ch : c) (o : op α) : IOProg E Err α := .vis (.call ch o) .ret

@[spec]
theorem call_spec (ch : c) (o : op α) {post : α → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (call (E := E) ch o)
      ((fun h => Named.mk `allow none (P.allow ch (h.traceOf ch) o)) ⊓
        ((fun h => ∀ v, Named.mk `onReply none (P.onReply ch (h.traceOf ch) o (.ok v)) →
            ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (Channel.log c o (.ok v))) → post v h') ⊓
          fun h => ∀ e, Named.mk `onReply none (P.onReply ch (h.traceOf ch) o (.error e)) →
            ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (Channel.log c o (.error e))) → epost.1 e h'))
      post epost := by
  apply Triple.intro
  intro h
  simp only [meet_apply, meet_prop_eq_and]
  intro hw
  exact ⟨hw.1, fun v hv => hw.2.1 v hv _ rfl, fun e he => hw.2.2 e he _ rfl⟩

end Call

variable {E Err : Type}

/-- The trace so far, as a ghost value for specs and invariants. -/
def snapshot : IOProg E Err (Ghost (Trace E)) := .vis .snapshot .ret

@[spec]
theorem snapshot_spec {post : Ghost (Trace E) → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (snapshot (E := E) (Err := Err)) (fun h => post (Ghost.mk h) h) post epost :=
  ⟨fun _ hk => hk⟩

end IOProg
