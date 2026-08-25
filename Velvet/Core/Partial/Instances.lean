module

public import Velvet.Core.Partial.Defs

open Std.WP
open Std.WP.Assertion
open Lean.Order

universe u u₁ u₂ v w

namespace WPPartial

public theorem Option.wp_csup_lift {α : Type u} {c : Option α → Prop} (hc : chain c) (hne : ∃ x, c x) (Q : α → Prop) (E : Unit → Prop) :
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

@[simp, grind =]
public theorem Option.wp_bot {α : Type u} {Q : α → Prop} {E : Unit → Prop} :
    wp (Prog := Option α) (CCPO.csup (α := Option α) (c := fun _ => False) emptyChain) Q E = E () := by
  have hcsup : CCPO.csup (α := Option α) (c := fun _ => False) emptyChain = none := by
    apply PartialOrder.rel_antisymm
    · apply csup_le emptyChain
      intro z hz
      exact False.elim hz
    · cases (CCPO.csup (α := Option α) (c := fun _ => False) emptyChain)
      · exact PartialOrder.rel_refl
      · constructor
  rw [hcsup]
  rfl

public theorem fun_csup_apply_eq {α : Type u} {β : Type v} [CCPO β] {c : (α → β) → Prop} (hc : chain c) (x : α) :
    (CCPO.csup hc) x = CCPO.csup (chain_apply hc x) := by
  apply PartialOrder.rel_antisymm
  · have h : CCPO.csup hc ⊑ (fun a => CCPO.csup (chain_apply hc a)) := by
      apply csup_le hc
      intro f hf a
      exact le_csup (chain_apply hc a) ⟨f, hf, rfl⟩
    exact h x
  · apply csup_le (chain_apply hc x)
    rintro y ⟨f, hf, rfl⟩
    have h : f ⊑ CCPO.csup hc := le_csup hc hf
    exact h x

@[simp, grind =]
public theorem ReaderT.csup_bot {ρ : Type u} {m : Type u → Type v} [∀ α, CCPO (m α)] {α : Type u} (r : ρ) :
    (CCPO.csup (α := ReaderT ρ m α) (c := fun _ => False) emptyChain).run r =
    CCPO.csup (α := m α) (c := fun _ => False) emptyChain := by
  apply PartialOrder.rel_antisymm
  · have h : (CCPO.csup (α := ReaderT ρ m α) (c := fun _ => False) emptyChain) ⊑ (fun _ => CCPO.csup (α := m α) (c := fun _ => False) emptyChain) := by
      apply csup_le emptyChain
      intro f hf
      exact False.elim hf
    exact h r
  · apply csup_le emptyChain
    intro z hz
    exact False.elim hz

@[simp, grind =]
public theorem StateT.csup_bot {σ : Type u} {m : Type u → Type v} [∀ α, CCPO (m α)] {α : Type u} (s : σ) :
    (CCPO.csup (α := StateT σ m α) (c := fun _ => False) emptyChain).run s =
    CCPO.csup (α := m (α × σ)) (c := fun _ => False) emptyChain := by
  apply PartialOrder.rel_antisymm
  · have h : (CCPO.csup (α := StateT σ m α) (c := fun _ => False) emptyChain) ⊑ (fun _ => CCPO.csup (α := m (α × σ)) (c := fun _ => False) emptyChain) := by
      apply csup_le emptyChain
      intro f hf
      exact False.elim hf
    exact h s
  · apply csup_le emptyChain
    intro z hz
    exact False.elim hz

@[simp, grind =]
public theorem ExceptT.csup_bot {ε : Type u} {m : Type u → Type v} [∀ α, CCPO (m α)] {α : Type u} :
    (CCPO.csup (α := ExceptT ε m α) (c := fun _ => False) emptyChain).run =
    CCPO.csup (α := m (Except ε α)) (c := fun _ => False) emptyChain := by
  rfl

public instance Option.instWPPartial : WPPartial (Option.{u}) Prop (Unit → Prop) (fun _ => True) (fun E => E ()) where
  csup_lift hc hne Q E := Option.wp_csup_lift hc hne Q E
  wp_bot _ _ := Option.wp_bot
  le_divergence_post pre := by intro _; trivial

public instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre] {ρ : Type u} :
    WPPartial (ReaderT ρ m) (ρ → Pred) EPred div_post (fun E => fun _ => div_pre E) where
  csup_lift {α} {c} hc hne Q E := by
    intro r
    rw [ReaderT.wp_apply_eq]
    rw [iInf_apply]
    have hc_r : chain (fun y => ∃ f : ReaderT ρ m α, c f ∧ f.run r = y) := chain_apply hc r
    have hne_r : ∃ y, (fun y => ∃ f : ReaderT ρ m α, c f ∧ f.run r = y) y := by
      rcases hne with ⟨f, hf⟩
      exact ⟨f.run r, ⟨f, hf, rfl⟩⟩
    have h_csup : (CCPO.csup hc).run r = CCPO.csup hc_r := fun_csup_apply_eq (c := c) hc r
    rw [h_csup]
    have h1 := WPPartial.csup_lift (m := m) hc_r hne_r (fun a => Q a r) E
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, ⟨f, hf, rfl⟩⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => (wp x.val Q E) r) ⟨f, hf⟩) ?_
    rw [ReaderT.wp_apply_eq]
  wp_bot post epost := by
    ext r
    rw [ReaderT.wp_apply_eq, ReaderT.csup_bot, WPPartial.wp_bot]
  le_divergence_post pre := by
    intro r
    exact instWP.le_divergence_post (pre r)

public instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre] {σ : Type u} :
    WPPartial (StateT σ m) (σ → Pred) EPred div_post (fun E => fun _ => div_pre E) where
  csup_lift {α} {c} hc hne Q E := by
    intro s
    rw [StateT.wp_apply_eq]
    rw [iInf_apply]
    have hc_s : chain (fun y => ∃ f : StateT σ m α, c f ∧ f.run s = y) := chain_apply hc s
    have hne_s : ∃ y, (fun y => ∃ f : StateT σ m α, c f ∧ f.run s = y) y := by
      rcases hne with ⟨f, hf⟩
      exact ⟨f.run s, ⟨f, hf, rfl⟩⟩
    have h_csup : (CCPO.csup hc).run s = CCPO.csup hc_s := fun_csup_apply_eq (c := c) hc s
    rw [h_csup]
    have h1 := WPPartial.csup_lift (m := m) hc_s hne_s (fun (a, s') => Q a s') E
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, ⟨f, hf, rfl⟩⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => (wp x.val Q E) s) ⟨f, hf⟩) ?_
    rw [StateT.wp_apply_eq]
  wp_bot post epost := by
    ext s
    rw [StateT.wp_apply_eq, StateT.csup_bot, WPPartial.wp_bot]
  le_divergence_post pre := by
    intro s
    exact instWP.le_divergence_post (pre s)

public instance [Monad m] [∀ α, CCPO (m α)] [MonoBind m] {ε : Type u} : MonoBind (ExceptT ε m) where
  bind_mono_left {α β} {x₁ x₂ : ExceptT ε m α} (f : α → ExceptT ε m β) (h : x₁ ⊑ x₂) := by
    change (ExceptT.bind x₁ f : m (Except ε β)) ⊑ (ExceptT.bind x₂ f : m (Except ε β))
    unfold ExceptT.bind
    apply MonoBind.bind_mono_left
    exact h
  bind_mono_right {α β} (x : ExceptT ε m α) {f₁ f₂ : α → ExceptT ε m β} (h : f₁ ⊑ f₂) := by
    change (ExceptT.bind x f₁ : m (Except ε β)) ⊑ (ExceptT.bind x f₂ : m (Except ε β))
    unfold ExceptT.bind
    apply MonoBind.bind_mono_right
    intro res
    cases res with
    | error e => exact PartialOrder.rel_refl
    | ok a => exact h a

public noncomputable instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre] {ε : Type u} :
    WPPartial (ExceptT ε m) Pred ((ε → Pred) × EPred) (fun _ => ⊥, div_post) (fun E => div_pre E.snd) where
  csup_lift {α} {c} hc hne Q E := by
    rw [ExceptT.wp_apply_eq]
    have h1 := WPPartial.csup_lift (m := m) (α := Except ε α) (c := c) hc hne (pushExcept Q E.fst) E.snd
    apply PartialOrder.rel_trans _ h1
    apply le_iInf
    rintro ⟨x, hx⟩
    refine PartialOrder.rel_trans (iInf_le (fun (x : {x // c x}) => wp x.val Q E) ⟨x, hx⟩) ?_
    rw [ExceptT.wp_apply_eq]
    exact PartialOrder.rel_refl
  wp_bot post epost := by
    rw [ExceptT.wp_apply_eq, ExceptT.csup_bot, WPPartial.wp_bot]
  le_divergence_post pre := by
    exact instWP.le_divergence_post pre

end WPPartial
