import Velvet.Core.FreerMonad.WP

open Std.WP Lean.Order

/-- What a model running in base monad `m` may do. `yields x R`: `x`'s result is in `R` and `m`'s own
state is as before. Each base decides whether `x` must return: over `Option` it must, so programs can
be proved to finish; over `IO` it may stop. -/
class ModelBase (m : Type → Type) [Monad m] where
  yields : ∀ {α : Type}, m α → (α → Prop) → Prop
  yields_pure {α : Type} {a : α} {R : α → Prop} : R a → yields (pure a : m α) R
  yields_bind {α β : Type} {x : m α} {f : α → m β} {R : α → Prop} {S : β → Prop} :
    yields x R → (∀ a, R a → yields (f a) S) → yields (x >>= f) S

export ModelBase (yields)

/-- A base whose models may stop the run, and so can host a monitor. -/
class CanStop (m : Type → Type) [Monad m] [ModelBase m] where
  stop : ∀ {α : Type}, String → m α
  yields_stop {α : Type} {msg : String} {R : α → Prop} : yields (stop msg : m α) R

/-- How `yields` meets `wp`: a call is fine under `stopPre` in case its model stops. -/
class WPModelBase (m : Type → Type) (Pred EPred : outParam Type) [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [ModelBase m] where
  stopPre : EPred → Pred
  stopPre_mono {E E' : EPred} : E ⊑ E' → stopPre E ⊑ stopPre E'
  wp_of_yields {α : Type} {x : m α} {R : α → Prop} {pre : Pred} {Q : α → Pred} {E : EPred} :
    yields x R → (∀ a, R a → pre ⊑ Q a) → pre ⊓ stopPre E ⊑ wp x Q E

namespace ModelBase
variable {m : Type → Type} [Monad m] [ModelBase m] [CanStop m]

/-- Run `x`, but stop instead of returning a result outside `R`. -/
def monitor {α : Type} (R : α → Prop) [DecidablePred R] (x : m α) : m α := do
  let r ← x
  if R r then pure r else CanStop.stop "protocol violation"

theorem yields_monitor {α : Type} (R : α → Prop) [DecidablePred R] (x : m α)
    (free : yields x fun _ => True) : yields (monitor R x) R :=
  yields_bind free fun r _ => by
    by_cases h : R r
    · simp only [h, ite_true]; exact yields_pure h
    · simp only [h, ite_false]; exact CanStop.yields_stop

end ModelBase

/-! `Option`: a model must return, so a call never stops. -/

instance : ModelBase Option where
  yields x R := ∃ a, x = some a ∧ R a
  yields_pure h := ⟨_, rfl, h⟩
  yields_bind := fun ⟨a, hx, ha⟩ hf => by subst hx; exact hf a ha

instance : WPModelBase Option Prop (Unit → Prop) where
  stopPre _ := True
  stopPre_mono _ := id
  wp_of_yields := fun ⟨a, hx, ha⟩ hQ => by
    subst hx; exact PartialOrder.rel_trans (meet_le_left _ _) (hQ a ha)

@[simp, grind =] theorem WPModelBase.stopPre_option (E : Unit → Prop) :
    WPModelBase.stopPre (m := Option) E = True := rfl

/-! `StateT`: yielding also means handing the state back unchanged. -/

instance {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [ModelBase m] : ModelBase (StateT σ m) where
  yields x R := ∀ s, yields (x.run s) (fun p => p.2 = s ∧ R p.1)
  yields_pure h s := ModelBase.yields_pure (m := m) ⟨rfl, h⟩
  yields_bind := @fun _ _ x f _ _ hx hf s => by
    show yields (x.run s >>= fun p => (f p.1).run p.2) _
    exact ModelBase.yields_bind (hx s) fun p ⟨hs, ha⟩ => by
      obtain ⟨a, s'⟩ := p; simp only at hs ha; subst hs; exact hf a ha s'

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
    WPModelBase.stopPre (m := StateT σ Option) E s = True := rfl

/-! `IO`: a model may stop, by throwing. The world is not state the logic sees. -/

instance : ModelBase IO where
  yields x R := ∀ w a w', x w = .ok a w' → R a
  yields_pure h _ _ _ he := by cases he; exact h
  yields_bind := @fun _ _ x f _ _ hx hf w b w' he => by
    change EST.bind x f w = _ at he
    unfold EST.bind at he
    split at he
    · rename_i a s heq; exact hf a (hx _ _ _ heq) _ _ _ he
    · cases he

instance : CanStop IO where
  stop msg := throw (IO.userError msg)
  yields_stop := fun _ _ _ he => by cases he

@[simp] theorem ModelBase.yields_true_io {α : Type} (x : IO α) : yields x fun _ => True :=
  fun _ _ _ _ => trivial
