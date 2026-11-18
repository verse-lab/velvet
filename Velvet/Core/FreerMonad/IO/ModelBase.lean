import Velvet.Core.FreerMonad.WP

open Std.WP Lean.Order

/-- What a model running in base monad `m` may do: return within a set of results, or stop.
`yields x R`: whenever `x` returns, its result is in `R` and `m`'s own state is as before. -/
class ModelBase (m : Type → Type) [Monad m] where
  yields : ∀ {α : Type}, m α → (α → Prop) → Prop
  stop : ∀ {α : Type}, String → m α
  yields_pure {α : Type} {a : α} {R : α → Prop} : R a → yields (pure a : m α) R
  yields_bind {α β : Type} {x : m α} {f : α → m β} {R : α → Prop} {S : β → Prop} :
    yields x R → (∀ a, R a → yields (f a) S) → yields (x >>= f) S
  yields_stop {α : Type} {msg : String} {R : α → Prop} : yields (stop msg : m α) R

export ModelBase (yields)

/-- How `yields` meets `wp`: stopping is fine under `stopPre`, as diverging is under `div_pre`. -/
class WPModelBase (m : Type → Type) (Pred EPred : outParam Type) [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [ModelBase m] where
  stopPre : EPred → Pred
  stopPre_mono {E E' : EPred} : E ⊑ E' → stopPre E ⊑ stopPre E'
  wp_of_yields {α : Type} {x : m α} {R : α → Prop} {pre : Pred} {Q : α → Pred} {E : EPred} :
    yields x R → (∀ a, R a → pre ⊑ Q a) → pre ⊓ stopPre E ⊑ wp x Q E

namespace ModelBase
variable {m : Type → Type} [Monad m] [ModelBase m]

/-- Run `x`, but stop instead of returning a result outside `R`. -/
def monitor {α : Type} (R : α → Prop) [DecidablePred R] (x : m α) : m α := do
  let r ← x
  if R r then pure r else stop "protocol violation"

theorem yields_monitor {α : Type} (R : α → Prop) [DecidablePred R] (x : m α)
    (free : yields x fun _ => True) : yields (monitor R x) R :=
  yields_bind free fun r _ => by
    by_cases h : R r
    · simp only [h, ite_true]; exact yields_pure h
    · simp only [h, ite_false]; exact yields_stop

end ModelBase

/-! `Option`: `none` is the stop. -/

instance : ModelBase Option where
  yields x R := ∀ a, x = some a → R a
  stop _ := none
  yields_pure h _ he := by cases he; exact h
  yields_bind hx hf b he := by
    cases hxv : ‹Option _› with
    | none => simp [hxv] at he
    | some a => simp [hxv] at he; exact hf a (hx a hxv) b he
  yields_stop := fun _ h => nomatch h

/-- `Option` has no state of its own, so every action yields within `True`. -/
@[simp] theorem ModelBase.yields_true_option {α : Type} (x : Option α) : yields x fun _ => True :=
  fun _ _ => trivial

instance : WPModelBase Option Prop (Unit → Prop) where
  stopPre E := E ()
  stopPre_mono h := h ()
  wp_of_yields := @fun _ x _ _ _ _ hx hQ => by
    cases x with
    | none => exact meet_le_right _ _
    | some a => exact PartialOrder.rel_trans (meet_le_left _ _) (hQ a (hx a rfl))

@[simp, grind =] theorem WPModelBase.stopPre_option (E : Unit → Prop) :
    WPModelBase.stopPre (m := Option) E = E () := rfl

/-! `StateT`: yielding also means handing the state back unchanged. -/

instance {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [ModelBase m] : ModelBase (StateT σ m) where
  yields x R := ∀ s, yields (x.run s) (fun p => p.2 = s ∧ R p.1)
  stop msg _ := ModelBase.stop msg
  yields_pure h s := ModelBase.yields_pure (m := m) ⟨rfl, h⟩
  yields_bind := @fun _ _ x f _ _ hx hf s => by
    show yields (x.run s >>= fun p => (f p.1).run p.2) _
    exact ModelBase.yields_bind (hx s) fun p ⟨hs, ha⟩ => by
      obtain ⟨a, s'⟩ := p; simp only at hs ha; subst hs; exact hf a ha s'
  yields_stop _ := ModelBase.yields_stop (m := m)

instance {σ Pred EPred : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [ModelBase m] [Assertion Pred]
    [Assertion EPred] [WPMonad m Pred EPred] [WPModelBase m Pred EPred] :
    WPModelBase (StateT σ m) (σ → Pred) EPred where
  stopPre E := fun _ => WPModelBase.stopPre (m := m) E
  stopPre_mono h _ := WPModelBase.stopPre_mono (m := m) h
  wp_of_yields := @fun _ x _ pre Q E hx hQ s => by
    rw [meet_apply]
    exact WPModelBase.wp_of_yields (m := m) (hx s) fun p ⟨hs, ha⟩ => by
      obtain ⟨a, s'⟩ := p; simp only at hs ha; subst hs; exact hQ a ha s'

@[simp] theorem WPModelBase.stopPre_stateT_apply {σ Pred EPred : Type} {m : Type → Type} [Monad m]
    [LawfulMonad m] [ModelBase m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [WPModelBase m Pred EPred] (E : EPred) (s : σ) :
    WPModelBase.stopPre (m := StateT σ m) E s = WPModelBase.stopPre (m := m) E := rfl

@[simp, grind =] theorem WPModelBase.stopPre_stateT_option {σ : Type} (E : Unit → Prop) (s : σ) :
    WPModelBase.stopPre (m := StateT σ Option) E s = E () := rfl
