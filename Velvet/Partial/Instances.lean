import Velvet.Partial.Defs

open Std.WP
open Std.WP.Assertion
open Lean.Order

universe u u₁ u₂ v w

namespace Velvet

theorem Option.wp_csup_lift {α : Type u} {c : Option α → Prop} (hc : chain c) (hne : ∃ x, c x) (Q : α → Prop) (E : Unit → Prop) :
    (⨅ (x : {x : Option α // c x}), (wp (Prog := Option α) x.val Q E : Prop)) ⊑ (wp (Prog := Option α) (CCPO.csup hc) Q E : Prop) := by
  by_cases h : ∃ a, c (some a)
  · rcases h with ⟨a, ha⟩
    have hcsup : CCPO.csup hc = some a := by
      apply PartialOrder.rel_antisymm
      · apply csup_le hc
        intro y hy
        cases hc y (some a) hy ha with
        | inl h1 => exact h1
        | inr h2 =>
          cases y with
          | none => contradiction
          | some b =>
            have : b = a := by cases h2; rfl
            subst this; exact PartialOrder.rel_refl
      · apply le_csup hc ha
    rw [hcsup]
    exact iInf_le (fun (x : {x : Option α // c x}) => (wp (Prog := Option α) x.val Q E : Prop)) ⟨some a, ha⟩
  · have hnone : ∀ y, c y → y = none := by
      intro y hy
      cases y with
      | none => rfl
      | some a => exact False.elim (h ⟨a, hy⟩)
    rcases hne with ⟨y, hy⟩
    have hy_eq : y = none := hnone y hy
    subst hy_eq
    have hcsup : CCPO.csup hc = none := by
      apply PartialOrder.rel_antisymm
      · apply csup_le hc
        intro z hz
        rw [hnone z hz]
        exact PartialOrder.rel_refl
      · apply le_csup hc hy
    rw [hcsup]
    exact iInf_le (fun (x : {x : Option α // c x}) => (wp (Prog := Option α) x.val Q E : Prop)) ⟨none, hy⟩

instance Option.instWPPartial : WPPartial (Option.{u}) Prop (Unit → Prop) where
  csup_lift hc hne Q E := Option.wp_csup_lift hc hne Q E

instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred] {ρ : Type u} :
    WPPartial (ReaderT ρ m) (ρ → Pred) EPred where
  csup_lift {α} {c} hc hne Q E := by
    intro r
    rw [ReaderT.wp_apply_eq]
    rw [iInf_apply]
    have hc_r : chain (fun y => ∃ f : ReaderT ρ m α, c f ∧ f.run r = y) := chain_apply hc r
    have hne_r : ∃ y, (fun y => ∃ f : ReaderT ρ m α, c f ∧ f.run r = y) y := by
      rcases hne with ⟨f, hf⟩
      exact ⟨f.run r, ⟨f, hf, rfl⟩⟩
    have h_csup : (CCPO.csup hc).run r = CCPO.csup hc_r := by
      change (CCPO.csup (α := ρ → m α) hc) r = CCPO.csup (chain_apply hc r)
      rw [← fun_csup_eq]
      rfl
    rw [h_csup]
    have h1 := WPPartial.csup_lift hc_r hne_r (fun a => Q a r) E
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, ⟨f, hf, rfl⟩⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => (wp x.val Q E) r) ⟨f, hf⟩) ?_
    rw [ReaderT.wp_apply_eq]

instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred] {σ : Type u} :
    WPPartial (StateT σ m) (σ → Pred) EPred where
  csup_lift {α} {c} hc hne Q E := by
    intro s
    rw [StateT.wp_apply_eq]
    rw [iInf_apply]
    have hc_s : chain (fun y => ∃ f : StateT σ m α, c f ∧ f.run s = y) := chain_apply hc s
    have hne_s : ∃ y, (fun y => ∃ f : StateT σ m α, c f ∧ f.run s = y) y := by
      rcases hne with ⟨f, hf⟩
      exact ⟨f.run s, ⟨f, hf, rfl⟩⟩
    have h_csup : (CCPO.csup hc).run s = CCPO.csup hc_s := by
      change (CCPO.csup (α := σ → m (α × σ)) hc) s = CCPO.csup (chain_apply hc s)
      rw [← fun_csup_eq]
      rfl
    rw [h_csup]
    have h1 := WPPartial.csup_lift hc_s hne_s (fun (a, s') => Q a s') E
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, ⟨f, hf, rfl⟩⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => (wp x.val Q E) s) ⟨f, hf⟩) ?_
    rw [StateT.wp_apply_eq]

instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred] {ε : Type u} :
    WPPartial (ExceptT ε m) Pred ((ε → Pred) × EPred) where
  csup_lift {α} {c} hc hne Q E := by
    rw [ExceptT.wp_apply_eq]
    have h1 := WPPartial.csup_lift (α := Except ε α) (c := c) hc hne (pushExcept Q E.fst) E.snd
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, hx⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => wp x.val Q E) ⟨x, hx⟩) ?_
    rw [ExceptT.wp_apply_eq]
    exact PartialOrder.rel_refl

end Velvet
