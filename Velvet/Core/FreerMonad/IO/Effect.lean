import Velvet.Core.FreerMonad.IO.Trace
import Velvet.Core.Partial

open Std.WP Lean.Order

universe v

inductive IOEff (E Err : Type) : Type → Type 1 where
  | read {c In Out : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E] {P : Protocol In Out Err}
      [Model P c E] (ch : c) : IOEff E Err In
  | write {c In Out : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E] {P : Protocol In Out Err}
      [Model P c E] (ch : c) (o : Out) : IOEff E Err Unit

abbrev IOProg (E Err : Type) := FreerMonad (IOEff E Err)

abbrev IOModel (E Err : Type) := ExceptT Err (StateT (List E) Option)

section Effect
variable {E Err : Type}

noncomputable instance instWPIOEff {α : Type} :
    WP (IOEff E Err α) α (List E → Prop) ((Err → List E → Prop) × (Unit → Prop)) where
  wpTrans x := ⟨fun post epost h => match x with
    | @IOEff.read _ _ _ In _ _ _ _ P _ ch =>
        (∀ i : In, P.readAssumption (trace h ch) (.ok i) → post i (record h ch (.read (.ok i)))) ∧
        ∀ e, P.readAssumption (trace h ch) (.error e) → epost.1 e (record h ch (.read (.error e)))
    | @IOEff.write _ _ _ _ _ _ _ _ P _ ch o =>
        P.guarantee (trace h ch) o ∧
        (P.writeAssumption (trace h ch) o .ok → post () (record h ch (.write o .ok))) ∧
        ∀ e, P.writeAssumption (trace h ch) o (.error e) → epost.1 e (record h ch (.write o (.error e)))⟩
  wp_trans_monotone x post post' epost epost' he hp h := by
    cases x with
    | read ch =>
      exact fun ⟨hk, hn⟩ => ⟨fun i hi => hp _ _ (hk i hi), fun e he' => he.1 e _ (hn e he')⟩
    | write ch o =>
      exact fun ⟨hg, hk, hn⟩ => ⟨hg, fun hok => hp _ _ (hk hok), fun e he' => he.1 e _ (hn e he')⟩

instance instInterpIOEff : HasInterpreter (IOEff E Err) (IOModel E Err) where
  interp
    | @IOEff.read _ _ _ _ Out _ _ _ P _ ch => fun h =>
        some ((Model.read (Out := Out) (P := P) h ch).toExcept,
          record h ch (.read (Model.read (Out := Out) (P := P) h ch)))
    | @IOEff.write _ _ _ In _ _ _ _ P _ ch o => fun h =>
        some ((Model.write (In := In) (P := P) h ch o).toExcept,
          record h ch (.write o (Model.write (In := In) (P := P) h ch o)))

instance instLawfulEffWPIOEff :
    LawfulEffWP (IOEff E Err) (IOModel E Err) (List E → Prop) ((Err → List E → Prop) × (Unit → Prop)) where
  ewp_le_wp_interp x post epost := by
    intro post epost h
    cases x with
    | @read c In Out _ _ _ P _ ch =>
      intro ⟨hk, hn⟩
      have hok := Model.read_ok (P := P) h ch
      show pushExcept post epost.1 (Model.read (Out := Out) (P := P) h ch).toExcept
        (record h ch (.read (Model.read (Out := Out) (P := P) h ch)))
      generalize Model.read (Out := Out) (P := P) h ch = r at hok ⊢
      cases r with
      | ok i => exact hk i hok
      | error e => exact hn e hok
    | @write c In Out _ _ _ P _ ch o =>
      intro ⟨_, hk, hn⟩
      have hok := Model.write_ok (P := P) h ch o
      show pushExcept post epost.1 (Model.write (In := In) (P := P) h ch o).toExcept
        (record h ch (.write o (Model.write (In := In) (P := P) h ch o)))
      generalize Model.write (In := In) (P := P) h ch o = r at hok ⊢
      cases r with
      | ok => exact hk hok
      | error e => exact hn e hok

end Effect

noncomputable instance instWPMonadIOFreer {E Err : Type} {es : Type → Type v}
    [∀ α, WP (es α) α (List E → Prop) ((Err → List E → Prop) × (Unit → Prop))] :
    WPMonad (FreerMonad es) (List E → Prop) ((Err → List E → Prop) × (Unit → Prop)) :=
  FreerMonad.wpMonadInst (m := IOModel E Err)
    (div_post := ((fun _ => ⊥), fun _ => True)) (div_pre := fun X _ => X.2 ())

theorem FreerMonad.wp_eq_wp {E Err : Type} {es : Type → Type v}
    [∀ α, WP (es α) α (List E → Prop) ((Err → List E → Prop) × (Unit → Prop))]
    {α : Type} (x : FreerMonad es α) (post : α → List E → Prop) (epost : (Err → List E → Prop) × (Unit → Prop)) :
    Std.WP.wp x post epost =
      FreerMonad.wp (m := IOModel E Err) (div_post := ((fun _ => ⊥), fun _ => True))
        (div_pre := fun X _ => X.2 ()) x post epost :=
  rfl

theorem IOModel.refines {E Err : Type} {es : Type → Type v} [HasInterpreter es (IOModel E Err)]
    [∀ α, WP (es α) α (List E → Prop) ((Err → List E → Prop) × (Unit → Prop))]
    [LawfulEffWP es (IOModel E Err) (List E → Prop) ((Err → List E → Prop) × (Unit → Prop))]
    {α : Type} {x : FreerMonad es α} {pre : List E → Prop} {post : α → List E → Prop}
    {epost : (Err → List E → Prop) × (Unit → Prop)}
    (hx : Triple x pre post epost) : Triple (x.interp (m := IOModel E Err)) pre post epost :=
  Triple.intro (PartialOrder.rel_trans hx.le_wp
    (FreerMonad.soundness (div_post := ((fun _ => ⊥), fun _ => True)) (div_pre := fun X _ => X.2 ()) x))

namespace IOProg
variable {E Err c In Out : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E] {P : Protocol In Out Err}
  [Model P c E]

def read (ch : c) : IOProg E Err In := .vis (.read ch) .ret

def write (ch : c) (o : Out) : IOProg E Err Unit := .vis (.write ch o) .ret

@[spec]
theorem read_spec (ch : c) {post : In → List E → Prop} {epost : (Err → List E → Prop) × (Unit → Prop)} :
    Triple (read (E := E) ch)
      ((fun h => ∀ i, P.readAssumption (trace h ch) (.ok i) → post i (record h ch (.read (.ok i)))) ⊓
        fun h => ∀ e, P.readAssumption (trace h ch) (.error e) → epost.1 e (record h ch (.read (.error e))))
      post epost := by
  apply Triple.intro
  intro h
  simp only [meet_apply, meet_prop_eq_and]
  intro hw
  exact hw

@[spec]
theorem write_spec (ch : c) (o : Out) {post : Unit → List E → Prop}
    {epost : (Err → List E → Prop) × (Unit → Prop)} :
    Triple (write (E := E) ch o)
      ((fun h => P.guarantee (trace h ch) o) ⊓
        ((fun h => P.writeAssumption (trace h ch) o .ok → post () (record h ch (.write o .ok))) ⊓
          fun h => ∀ e, P.writeAssumption (trace h ch) o (.error e) → epost.1 e (record h ch (.write o (.error e)))))
      post epost := by
  apply Triple.intro
  intro h
  simp only [meet_apply, meet_prop_eq_and]
  intro hw
  exact hw

end IOProg
