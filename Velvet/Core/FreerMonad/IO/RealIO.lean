import Velvet.Core.FreerMonad.IO.ModelBase
import Velvet.Core.Partial

open Std.WP Lean.Order WPPartial

/-! Lean's `IO` as a base monad for IO programs. Its WP ignores the world: a postcondition must hold
whatever state the world is in, so predicates are plain `Prop`. Lean takes a diverging `IO` loop to
throw one fixed, unknown error, so loops over `IO` must accept every error. -/

instance (ε σ : Type) : LawfulMonad (EST ε σ) := .mk'
  (id_map := fun x => by funext s; show EST.bind x (fun a => EST.pure (id a)) s = x s
                         simp only [EST.bind, EST.pure]; split <;> simp_all)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by funext s; show EST.bind (EST.bind x f) g s = EST.bind x (fun a => EST.bind (f a) g) s
                                 simp only [EST.bind]; cases x s <;> rfl)

instance : LawfulMonad IO := inferInstanceAs (LawfulMonad (EST IO.Error IO.RealWorld))

/-- What one outcome of an `IO` action means for a postcondition. -/
def IO.outPost {α : Type} (post : α → Prop) (epost : IO.Error → Prop) :
    EST.Out IO.Error IO.RealWorld α → Prop
  | .ok a _ => post a
  | .error e _ => epost e

/-- For every state of the world: if `x` returns `a` then `post a`, if it throws `e` then `epost e`. -/
instance IO.wpInst {α : Type} : WP (IO α) α Prop (IO.Error → Prop) where
  wpTrans x := ⟨fun post epost => ∀ w, IO.outPost post epost (x w)⟩
  wp_trans_monotone x post post' epost epost' he hp := fun h w => by
    have := h w
    revert this
    cases x w with
    | ok a _ => exact hp a
    | error e _ => exact he e

theorem IO.wp_eq {α : Type} (x : IO α) (post : α → Prop) (epost : IO.Error → Prop) :
    wp x post epost = ∀ w, IO.outPost post epost (x w) := rfl

instance IO.instWPMonad : WPMonad IO Prop (IO.Error → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := fun h _ => h
  bind_le_wp_bind x f post epost := fun h w => by
    have := h w
    show IO.outPost post epost (EST.bind x f w)
    unfold EST.bind
    revert this
    cases x w with
    | ok a w' => exact fun h => h w'
    | error e _ => exact id

/-- Where some member of a chain does not diverge, the chain's supremum agrees with it. -/
theorem EST.csup_eq_of_ne {ε σ α : Type} [Nonempty ε] {c : EST ε σ α → Prop} (hc : chain c)
    {x : EST ε σ α} (hx : c x) {w : Void σ} (hne : x w ≠ EST.bot w) : CCPO.csup hc w = x w := by
  have h : FlatOrder.rel (b := EST.bot w) (x w) (CCPO.csup hc w) := le_csup hc hx w
  revert hne h
  generalize x w = a
  generalize CCPO.csup hc w = b
  intro hne h
  cases h with
  | bot => exact absurd rfl hne
  | refl => rfl

/-- Where every member of a chain diverges, so does its supremum. -/
theorem EST.csup_eq_bot {ε σ α : Type} [Nonempty ε] {c : EST ε σ α → Prop} (hc : chain c)
    {w : Void σ} (hall : ∀ x, c x → x w = EST.bot w) : CCPO.csup hc w = EST.bot w := by
  classical
  let u : EST ε σ α := fun w' => if w' = w then EST.bot w else CCPO.csup hc w'
  have hu : CCPO.csup hc ⊑ u := csup_le hc fun x hx w' => by
    show FlatOrder.rel (x w') (u w')
    by_cases hw : w' = w
    · subst hw; simp only [u, ite_true]; rw [hall x hx]; exact .refl
    · simp only [u, hw, ite_false]; exact le_csup hc hx w'
  have h : FlatOrder.rel (b := EST.bot w) (CCPO.csup hc w) (u w) := hu w
  simp only [u, ite_true] at h
  revert h
  generalize CCPO.csup hc w = b
  intro h
  cases h <;> rfl

theorem IO.wp_csup_lift {α : Type} {c : IO α → Prop} (hc : chain c) (hne : ∃ x, c x) (Q : α → Prop)
    (E : IO.Error → Prop) :
    (⨅ (x : {x : IO α // c x}), (wp x.val Q E : Prop)) ⊑ (wp (CCPO.csup hc) Q E : Prop) := by
  intro h w
  have hall : ∀ x, c x → wp x Q E := fun x hx =>
    (iInf_le (fun (y : {y : IO α // c y}) => (wp y.val Q E : Prop)) ⟨x, hx⟩ : _ → _) h
  by_cases hex : ∃ x, c x ∧ x w ≠ EST.bot (ε := IO.Error) w
  · obtain ⟨x, hx, hne'⟩ := hex
    rw [show CCPO.csup hc w = x w from EST.csup_eq_of_ne (ε := IO.Error) hc hx hne']
    exact hall x hx w
  · have hb : ∀ x, c x → x w = EST.bot (ε := IO.Error) w := fun x hx =>
      Classical.byContradiction fun hn => hex ⟨x, hx, hn⟩
    rw [show CCPO.csup hc w = EST.bot (ε := IO.Error) w from EST.csup_eq_bot (ε := IO.Error) hc hb]
    obtain ⟨x, hx⟩ := hne
    have := hall x hx w
    rw [hb x hx] at this
    exact this

theorem IO.wp_bot {α : Type} {Q : α → Prop} {E : IO.Error → Prop} :
    wp (CCPO.csup (α := IO α) (c := fun _ => False) emptyChain) Q E = E Classical.ofNonempty := by
  have hb : ∀ w, CCPO.csup (α := IO α) (c := fun _ => False) emptyChain w = EST.bot (ε := IO.Error) w :=
    fun w => EST.csup_eq_bot (ε := IO.Error) emptyChain fun _ h => h.elim
  rw [IO.wp_eq]
  apply propext
  constructor
  · intro h
    have := h (Classical.choice inferInstance)
    rw [hb] at this
    exact this
  · intro h w
    rw [hb]
    exact h

instance IO.instWPPartial :
    WPPartial IO Prop (IO.Error → Prop) (fun _ => True) (fun E => E Classical.ofNonempty) where
  csup_lift hc hne Q E := IO.wp_csup_lift hc hne Q E
  wp_bot _ _ := IO.wp_bot
  le_divergence_post _ := fun _ => trivial

instance : WPModelBase IO Prop (IO.Error → Prop) where
  stopPre E := ∀ e, E e
  stopPre_mono h := fun hE e => h e (hE e)
  wp_of_yields := @fun _ x _ pre Q E hx hQ h w => by
    have hp := (meet_le_left pre (∀ e, E e) : pre ⊓ (∀ e, E e) → pre) h
    have hs := (meet_le_right pre (∀ e, E e) : pre ⊓ (∀ e, E e) → ∀ e, E e) h
    show IO.outPost _ _ (x w)
    have hxw := hx w
    revert hxw
    cases x w with
    | ok a w' => exact fun hxw => (hQ a (hxw a w' rfl) : pre → Q a) hp
    | error e _ => exact fun _ => hs e

@[simp, grind =] theorem WPModelBase.stopPre_io (E : IO.Error → Prop) :
    WPModelBase.stopPre (m := IO) E = ∀ e, E e := rfl
