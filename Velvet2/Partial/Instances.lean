import Velvet2.Partial.Defs

open Std.Internal
open Std.Internal.Do
open Std.Internal.Do.Assertion
open Lean.Order
open Std.Internal.Do.CompleteLattice

universe u u₁ u₂ v w

namespace Velvet2

theorem Option.wp_csup_lift {α : Type u} {c : Option α → Prop} (hc : chain c) (Q : α → Prop) :
    (⨅ (x : {x : Option α // c x}), (wp (Prog := Option α) x.val Q True : Prop)) ⊑ (wp (Prog := Option α) (CCPO.csup hc) Q True : Prop) := by
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
    exact iInf_le (fun (x : {x : Option α // c x}) => (wp (Prog := Option α) x.val Q True : Prop)) ⟨some a, ha⟩
  · have hnone : ∀ y, c y → y = none := by
      intro y hy
      cases y with
      | none => rfl
      | some a => exact False.elim (h ⟨a, hy⟩)
    have hcsup : CCPO.csup hc = none := by
      apply PartialOrder.rel_antisymm
      · apply csup_le hc
        intro y hy
        rw [hnone y hy]
        exact PartialOrder.rel_refl
      · cases Classical.em (c none) with
        | inl hcn => exact le_csup hc hcn
        | inr hnn => exact FlatOrder.rel.bot
    rw [hcsup]
    show _ → True
    intro _
    trivial

instance Option.instWPPartial : WPPartial (Option.{u}) Prop Prop where
  csup_lift {α} {c} hc Q E := by
    cases Classical.em (E = True) with
    | inl hE =>
      subst hE
      exact Option.wp_csup_lift hc Q
    | inr hE =>
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
        exact iInf_le (fun (x : {x : Option α // c x}) => wp x.val Q E) ⟨some a, ha⟩
      · have hnone : ∀ y, c y → y = none := by
          intro y hy
          cases y with
          | none => rfl
          | some a => exact False.elim (h ⟨a, hy⟩)
        have hcsup : CCPO.csup hc = none := by
          apply PartialOrder.rel_antisymm
          · apply csup_le hc
            intro y hy
            rw [hnone y hy]
            exact PartialOrder.rel_refl
          · cases Classical.em (c none) with
            | inl hcn => exact le_csup hc hcn
            | inr hnn => exact FlatOrder.rel.bot
        rw [hcsup]
        cases Classical.em (c none) with
        | inl hcn =>
          exact iInf_le (fun (x : {x : Option α // c x}) => wp x.val Q E) ⟨none, hcn⟩
        | inr hnn =>
          intro _
          sorry

instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred] {ρ : Type u} :
    WPPartial (ReaderT ρ m) (ρ → Pred) EPred where
  csup_lift {α} {c} hc Q E := by
    intro r
    rw [ReaderT.wp_apply_eq]
    rw [iInf_apply]
    have hc_r : chain (fun y => ∃ f : ReaderT ρ m α, c f ∧ f.run r = y) := chain_apply hc r
    have h_csup : (CCPO.csup hc).run r = CCPO.csup hc_r := by
      change (CCPO.csup (α := ρ → m α) hc) r = CCPO.csup (chain_apply hc r)
      rw [← fun_csup_eq]
      rfl
    rw [h_csup]
    have h1 := WPPartial.csup_lift hc_r (fun a => Q a r) E
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, ⟨f, hf, rfl⟩⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => (wp x.val Q E) r) ⟨f, hf⟩) ?_
    rw [ReaderT.wp_apply_eq]

instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred] {σ : Type u} :
    WPPartial (StateT σ m) (σ → Pred) EPred where
  csup_lift {α} {c} hc Q E := by
    intro s
    rw [StateT.wp_apply_eq]
    rw [iInf_apply]
    have hc_s : chain (fun y => ∃ f : StateT σ m α, c f ∧ f.run s = y) := chain_apply hc s
    have h_csup : (CCPO.csup hc).run s = CCPO.csup hc_s := by
      change (CCPO.csup (α := σ → m (α × σ)) hc) s = CCPO.csup (chain_apply hc s)
      rw [← fun_csup_eq]
      rfl
    rw [h_csup]
    have h1 := WPPartial.csup_lift hc_s (fun (a, s') => Q a s') E
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, ⟨f, hf, rfl⟩⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => (wp x.val Q E) s) ⟨f, hf⟩) ?_
    rw [StateT.wp_apply_eq]

instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred] {ε : Type u} :
    WPPartial (ExceptT ε m) Pred (EPost.Cons (ε → Pred) EPred) where
  csup_lift {α} {c} hc Q E := by
    rw [ExceptT.wp_apply_eq]
    have h1 := WPPartial.csup_lift (α := Except ε α) (c := c) hc (E.pushExcept Q) E.tail
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, hx⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => wp x.val Q E) ⟨x, hx⟩) ?_
    rw [ExceptT.wp_apply_eq]
    exact PartialOrder.rel_refl

end Velvet2
