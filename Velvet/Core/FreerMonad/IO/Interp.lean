import Velvet.Core.FreerMonad.IO.Effect

open Std.WP Lean.Order

universe v

/-! Running IO programs in `IOModel`, each call answered by its channel's `Model`, and the soundness
of the WP against that interpretation. -/

section Interp
variable {E Err : Type}

instance instInterpIOEff : HasInterpreter (IOEff E Err) (IOModel E Err) where
  interp
    | @IOEff.call _ _ c _ _ _ _ _ _ P _ ch o => fun h =>
        some (Model.call (P := P) h ch o, h.recordFor ch (Channel.log c o (Model.call (P := P) h ch o)))
    | .snapshot => fun h => some (.ok (Ghost.mk h), h)

instance instLawfulEffWPIOEff :
    LawfulEffWP (IOEff E Err) (IOModel E Err) (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop)) where
  ewp_le_wp_interp x post epost := by
    intro post epost h
    cases x with
    | @call c op Ev α _ _ _ P _ ch o =>
      intro ⟨_, hk, hn⟩
      have hok := Model.call_ok (P := P) h ch o
      show pushExcept post epost.1 (Model.call (P := P) h ch o)
        (h.recordFor ch (Channel.log c o (Model.call (P := P) h ch o)))
      generalize Model.call (P := P) h ch o = r at hok ⊢
      cases r with
      | ok v => exact hk v hok
      | error e => exact hn e hok
    | snapshot => exact id

end Interp

theorem IOModel.refines {E Err : Type} {es : Type → Type v} [HasInterpreter es (IOModel E Err)]
    [∀ α, WP (es α) α (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop))]
    [LawfulEffWP es (IOModel E Err) (Trace E → Prop) ((Err → Trace E → Prop) × (Unit → Prop))]
    {α : Type} {x : FreerMonad es α} {pre : Trace E → Prop} {post : α → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)}
    (hx : Triple x pre post epost) : Triple (x.interp (m := IOModel E Err)) pre post epost :=
  Triple.intro (PartialOrder.rel_trans hx.le_wp
    (FreerMonad.soundness (div_post := ((fun _ => ⊥), fun _ => True)) (div_pre := fun X _ => X.2 ()) x))
