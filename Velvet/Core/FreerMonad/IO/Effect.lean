import Velvet.Core.FreerMonad.IO.Trace
import Velvet.Core.Partial
import Velvet.Core.Ghost

open Std.WP Lean.Order

universe v

inductive IOEff (E Err : Type) : Type → Type 1 where
  | read {c In Out : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E] {P : Protocol In Out Err}
      [Model P c E] (ch : c) : IOEff E Err In
  | write {c In Out : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E] {P : Protocol In Out Err}
      [Model P c E] (ch : c) (o : Out) : IOEff E Err Unit
  | snapshot : IOEff E Err (Ghost (Trace E))

abbrev IOProg (E Err : Type) := FreerMonad (IOEff E Err)

abbrev IOModel (E Err : Type) := ExceptT Err (StateT (Trace E) Option)

section Effect
variable {E Err : Type}

noncomputable instance instWPIOEff [Policy E] {α : Type} :
    WP (IOEff E Err α) α (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop)) where
  wpTrans x := ⟨fun post epost h => match x with
    | @IOEff.read _ _ _ In _ _ _ _ P _ ch =>
        (∀ i : In, P.onRead (h.traceOf ch) (.ok i) → post i (h.recordFor ch (.read (.ok i)))) ∧
        ∀ e, P.onRead (h.traceOf ch) (.error e) → epost.1 e (h.recordFor ch (.read (.error e)))
    | @IOEff.write _ _ _ _ _ _ _ _ P _ ch o =>
        Policy.allow (h.recordFor ch (.write o .ok)) ∧
        P.allow (h.traceOf ch) o ∧
        (P.onWrite (h.traceOf ch) o .ok → post () (h.recordFor ch (.write o .ok))) ∧
        ∀ e, P.onWrite (h.traceOf ch) o (.error e) → epost.1 e (h.recordFor ch (.write o (.error e)))
    | .snapshot => post (Ghost.mk h) h⟩
  wp_trans_monotone x post post' epost epost' he hp h := by
    cases x with
    | read ch =>
      exact fun ⟨hk, hn⟩ => ⟨fun i hi => hp _ _ (hk i hi), fun e he' => he.1 e _ (hn e he')⟩
    | write ch o =>
      exact fun ⟨hpol, hg, hk, hn⟩ =>
        ⟨hpol, hg, fun hok => hp _ _ (hk hok), fun e he' => he.1 e _ (hn e he')⟩
    | snapshot => exact hp _ _

instance instInterpIOEff : HasInterpreter (IOEff E Err) (IOModel E Err) where
  interp
    | @IOEff.read _ _ _ _ Out _ _ _ P _ ch => fun h =>
        some ((Model.read (Out := Out) (P := P) h ch).toExcept,
          h.recordFor ch (.read (Model.read (Out := Out) (P := P) h ch)))
    | @IOEff.write _ _ _ In _ _ _ _ P _ ch o => fun h =>
        some ((Model.write (In := In) (P := P) h ch o).toExcept,
          h.recordFor ch (.write o (Model.write (In := In) (P := P) h ch o)))
    | .snapshot => fun h => some (.ok (Ghost.mk h), h)

instance instLawfulEffWPIOEff [Policy E] :
    LawfulEffWP (IOEff E Err) (IOModel E Err) (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop)) where
  ewp_le_wp_interp x post epost := by
    intro post epost h
    cases x with
    | @read c In Out _ _ _ P _ ch =>
      intro ⟨hk, hn⟩
      have hok := Model.read_ok (P := P) h ch
      show pushExcept post epost.1 (Model.read (Out := Out) (P := P) h ch).toExcept
        (h.recordFor ch (.read (Model.read (Out := Out) (P := P) h ch)))
      generalize Model.read (Out := Out) (P := P) h ch = r at hok ⊢
      cases r with
      | ok i => exact hk i hok
      | error e => exact hn e hok
    | @write c In Out _ _ _ P _ ch o =>
      intro ⟨_, _, hk, hn⟩
      have hok := Model.write_ok (P := P) h ch o
      show pushExcept post epost.1 (Model.write (In := In) (P := P) h ch o).toExcept
        (h.recordFor ch (.write o (Model.write (In := In) (P := P) h ch o)))
      generalize Model.write (In := In) (P := P) h ch o = r at hok ⊢
      cases r with
      | ok => exact hk hok
      | error e => exact hn e hok
    | snapshot => exact id

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

theorem IOModel.refines {E Err : Type} {es : Type → Type v} [HasInterpreter es (IOModel E Err)]
    [∀ α, WP (es α) α (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop))]
    [LawfulEffWP es (IOModel E Err) (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop))]
    {α : Type} {x : FreerMonad es α} {pre : Trace E → Prop} {post : α → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)}
    (hx : Triple x pre post epost) : Triple (x.interp (m := IOModel E Err)) pre post epost :=
  Triple.intro (PartialOrder.rel_trans hx.le_wp
    (FreerMonad.soundness (div_post := ((fun _ => ⊥), fun _ => True)) (div_pre := fun X _ => X.2 ()) x))

namespace IOProg
variable {E Err c In Out : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E] {P : Protocol In Out Err}
  [Model P c E] [Policy E]

def read (ch : c) : IOProg E Err In := .vis (.read ch) .ret

def write (ch : c) (o : Out) : IOProg E Err Unit := .vis (.write ch o) .ret

/-- The trace so far, as a ghost value for specs and invariants. -/
def snapshot : IOProg E Err (Ghost (Trace E)) := .vis .snapshot .ret

@[spec]
theorem read_spec (ch : c) {post : In → Trace E → Prop} {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (read (E := E) ch)
      ((fun h => ∀ i, Named.mk `onRead none (P.onRead (h.traceOf ch) (.ok i)) →
          ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.read (.ok i))) → post i h') ⊓
        fun h => ∀ e, Named.mk `onRead none (P.onRead (h.traceOf ch) (.error e)) →
          ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.read (.error e))) → epost.1 e h')
      post epost := by
  apply Triple.intro
  intro h
  simp only [meet_apply, meet_prop_eq_and]
  intro hw
  exact ⟨fun i hi => hw.1 i hi _ rfl, fun e he => hw.2 e he _ rfl⟩

@[spec]
theorem write_spec (ch : c) (o : Out) {post : Unit → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (write (E := E) ch o)
      ((fun h => ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.write o .ok)) →
          Named.mk `policy none (Policy.allow h')) ⊓
        ((fun h => Named.mk `allow none (P.allow (h.traceOf ch) o)) ⊓
          ((fun h => Named.mk `onWrite none (P.onWrite (h.traceOf ch) o .ok) →
              ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.write o .ok)) → post () h') ⊓
            fun h => ∀ e, Named.mk `onWrite none (P.onWrite (h.traceOf ch) o (.error e)) →
              ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.write o (.error e))) → epost.1 e h')))
      post epost := by
  apply Triple.intro
  intro h
  simp only [meet_apply, meet_prop_eq_and]
  intro hw
  exact ⟨hw.1 _ rfl, hw.2.1, fun hok => hw.2.2.1 hok _ rfl, fun e he => hw.2.2.2 e he _ rfl⟩

@[spec]
theorem snapshot_spec {post : Ghost (Trace E) → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (snapshot (E := E) (Err := Err)) (fun h => post (Ghost.mk h) h) post epost :=
  ⟨fun _ hk => hk⟩

end IOProg
