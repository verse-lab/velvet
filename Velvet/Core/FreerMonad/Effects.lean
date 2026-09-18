import Velvet.Core.FreerMonad.Defs
import Velvet.Core.Partial

open Std.Internal.Do Lean.Order

universe u v v₁ v₂ w z

/-- The interpretation of `e` into `m` refines the specification-level `ewp`.
This is the only per-effect obligation the generic `FreerMonad` soundness theorem needs. -/
class LawfulEffWP (e : Type u → Type v₁) (m : Type u → Type v₂)
    (Pred : Type w) (EPred : Type z)
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [HasInterpreter e m] [∀ α, WP (e α) α Pred EPred] where
  /-- Interpreting an effect can only weaken its precondition. -/
  ewp_le_wp_interp {α : Type u} (c : e α) (post : α → Pred) (epost : EPred) :
    (WP.wpTrans c).apply ⊑ wp (HasInterpreter.interp (m := m) c)

/-! ## Executable effects: the base monad viewed as a signature -/

/-- The base monad `m`, wrapped as an effect signature so that it can be summed with
specification-level signatures. -/
inductive BaseEff (m : Type u → Type v) (α : Type u) : Type v where
  | mk : m α → BaseEff m α

instance : HasInterpreter (BaseEff m) m where
  interp | .mk x => x

/-- For an executable effect the specification *is* the WP of its interpretation. -/
noncomputable instance instEffWPBase [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] : WP (BaseEff m α) α Pred EPred where
  wpTrans c := ⟨fun post epost => match c with | .mk x => wp x post epost⟩
  wp_trans_monotone c post post' epost epost' he hp := by
    cases c; exact WP.wp_trans_monotone _ post post' epost epost' he hp

instance instLawfulEffWPBase [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] : LawfulEffWP (BaseEff m) m Pred EPred where
  ewp_le_wp_interp c post epost := by cases c; exact PartialOrder.rel_refl

/-! ## Sum of effect signatures -/

/-- Disjoint union of two effect signatures. -/
inductive EffSum (e₁ : Type u → Type v₁) (e₂ : Type u → Type v₂) (α : Type u) :
    Type (max v₁ v₂) where
  | inl : e₁ α → EffSum e₁ e₂ α
  | inr : e₂ α → EffSum e₁ e₂ α

instance [HasInterpreter e₁ m] [HasInterpreter e₂ m] :
    HasInterpreter (EffSum e₁ e₂) m where
  interp
    | .inl c => HasInterpreter.interp c
    | .inr c => HasInterpreter.interp c

instance instEffWPSum [Assertion Pred] [Assertion EPred]
    [WP (e₁ α) α Pred EPred] [WP (e₂ α) α Pred EPred] : WP (EffSum e₁ e₂ α) α Pred EPred where
  wpTrans c := ⟨fun post epost => match c with
    | .inl c => (WP.wpTrans c).apply post epost
    | .inr c => (WP.wpTrans c).apply post epost⟩
  wp_trans_monotone c post post' epost epost' he hp := by
    cases c <;> exact WP.wp_trans_monotone _ post post' epost epost' he hp

instance instLawfulEffWPSum [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred]
    [HasInterpreter e₁ m] [HasInterpreter e₂ m]
    [∀ α, WP (e₁ α) α Pred EPred] [∀ α, WP (e₂ α) α Pred EPred]
    [LawfulEffWP e₁ m Pred EPred] [LawfulEffWP e₂ m Pred EPred] :
    LawfulEffWP (EffSum e₁ e₂) m Pred EPred where
  ewp_le_wp_interp c post epost :=
    match c with
    | .inl c => LawfulEffWP.ewp_le_wp_interp (m := m) c post epost
    | .inr c => LawfulEffWP.ewp_le_wp_interp (m := m) c post epost
