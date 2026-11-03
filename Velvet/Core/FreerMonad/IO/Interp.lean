import Velvet.Core.FreerMonad.IO.Effect

open Std.WP Lean.Order WPPartial

/-! Running IO programs in `IOModelT E Err m`, each call answered by its channel's `Model` and each
lifted action run in `m`, and the soundness of the WP against that interpretation. -/

section Interp
variable {E Err : Type} {m : Type → Type} [Monad m]

instance instInterpIOEff : HasInterpreter (IOEff E Err m) (IOModelT E Err m) where
  interp
    | @IOEff.call _ _ _ c _ _ _ _ _ _ P _ ch o => fun h =>
        pure (Model.call (P := P) h ch o, h.recordFor ch (Channel.log c o (Model.call (P := P) h ch o)))
    | .snapshot => fun h => pure (.ok (Ghost.mk h), h)
    | .lift x => MonadLift.monadLift (MonadLift.monadLift x : StateT (Trace E) m _)

variable {Pred EPred : Type} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

instance instLawfulEffWPIOEff :
    LawfulEffWP (IOEff E Err m) (IOModelT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) where
  ewp_le_wp_interp x post epost := by
    intro post epost h
    cases x with
    | @call c op Ev α _ _ _ P _ ch o =>
      have hok := Model.call_ok (P := P) h ch o
      refine PartialOrder.rel_trans ?_ (WPMonad.pure_le_wp_pure (m := m) _ _ _)
      show _ ⊑ pushExcept post epost.1 (Model.call (P := P) h ch o)
        (h.recordFor ch (Channel.log c o (Model.call (P := P) h ch o)))
      generalize Model.call (P := P) h ch o = r at hok ⊢
      cases r with
      | ok v =>
        exact PartialOrder.rel_trans (meet_le_right _ _) (PartialOrder.rel_trans (meet_le_left _ _)
          (PartialOrder.rel_trans (iInf_le _ v) (ofProp_himp_le hok _)))
      | error e =>
        exact PartialOrder.rel_trans (meet_le_right _ _) (PartialOrder.rel_trans (meet_le_right _ _)
          (PartialOrder.rel_trans (iInf_le _ e) (ofProp_himp_le hok _)))
    | snapshot =>
      refine PartialOrder.rel_trans ?_ (WPMonad.pure_le_wp_pure (m := m) _ _ _)
      exact PartialOrder.rel_refl
    | lift x =>
      refine PartialOrder.rel_trans ?_ (WPMonad.le_wp_monadLift_ExceptT_apply (m := StateT (Trace E) m) _ post epost h)
      exact WPMonad.le_wp_monadLift_StateT_apply (epost := epost.2) x post h

end Interp

theorem IOModelT.refines {E Err : Type} {m : Type → Type} {Pred EPred : Type} [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)] [MonoBind m]
    {div_post : (Err → Trace E → Pred) × EPred} {div_pre : (Err → Trace E → Pred) × EPred → Trace E → Pred}
    [WPPartial (IOModelT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) div_post div_pre]
    {α : Type} {x : IOProgT E Err m α} {pre : Trace E → Pred} {post : α → Trace E → Pred}
    {epost : (Err → Trace E → Pred) × EPred}
    (hx : Triple x pre post epost) : Triple (x.interp (m := IOModelT E Err m)) pre post epost :=
  Triple.intro (PartialOrder.rel_trans hx.le_wp (FreerMonad.soundness (m := IOModelT E Err m) x))
