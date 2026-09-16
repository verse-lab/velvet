import Velvet.Core.FreerMonad.Defs
import Velvet.Core.Partial

open Std.Internal.Do Lean.Order

universe u v v₁ v₂ w z

/-! # Effect signatures carrying their own WP semantics

`FreerMonad.wp` currently defines the meaning of a `vis` node as the weakest precondition
of its *interpretation*.  That is too rigid for specification-level effects such as demonic
choice, whose WP (`⨅` over all witnesses) is strictly stronger than the WP of any particular
interpretation (which resolves the choice to one witness).

We therefore decouple the two:
* `EffWP e Pred EPred` gives an effect signature its own predicate transformer;
* `LawfulEffWP e m Pred EPred` is the per-effect proof obligation that interpreting into `m`
  *refines* that transformer.

The generic soundness theorem for `FreerMonad` then follows from `LawfulEffWP` alone. -/

/-- Weakest-precondition semantics of an effect signature `e`.

`m` is not used by `ewp`; it is an `outParam` so that instance search on `e` alone fixes the
ambient monad, the way `WPMonad` fixes `Pred`/`EPred` from `m`. This is what lets
`FreerMonad.wp` be stated *without* a `HasInterpreter` argument: a specification must not
depend on the existence of a handler. -/
class EffWP (e : Type u → Type v) (m : outParam (Type u → Type v'))
    (Pred : outParam (Type w)) (EPred : outParam (Type z))
    [Assertion Pred] [Assertion EPred] where
  /-- The predicate transformer of a single effect. -/
  ewp {α : Type u} (c : e α) (post : α → Pred) (epost : EPred) : Pred
  /-- Monotonicity of `ewp`, mirroring `WP.wp_trans_monotone`. -/
  ewp_monotone {α : Type u} (c : e α) (post post' : α → Pred) (epost epost' : EPred) :
    epost ⊑ epost' → post ⊑ post' → ewp c post epost ⊑ ewp c post' epost'

export EffWP (ewp ewp_monotone)

/-- The interpretation of `e` into `m` refines the specification-level `ewp`.
This is the only per-effect obligation the generic `FreerMonad` soundness theorem needs. -/
class LawfulEffWP (e : Type u → Type v₁) (m : Type u → Type v₂)
    (Pred : Type w) (EPred : Type z)
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [HasInterpreter e m] [EffWP e m Pred EPred] where
  /-- Interpreting an effect can only weaken its precondition. -/
  ewp_le_wp_interp {α : Type u} (c : e α) (post : α → Pred) (epost : EPred) :
    ewp c post epost ⊑ wp (HasInterpreter.interp (m := m) c) post epost

/-! ## Executable effects: the base monad viewed as a signature -/

/-- The base monad `m`, wrapped as an effect signature so that it can be summed with
specification-level signatures. -/
inductive BaseEff (m : Type u → Type v) (α : Type u) : Type v where
  | mk : m α → BaseEff m α

instance : HasInterpreter (BaseEff m) m where
  interp | .mk x => x

/-- For an executable effect the specification *is* the WP of its interpretation. -/
noncomputable instance instEffWPBase [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] : EffWP (BaseEff m) m Pred EPred where
  ewp c post epost := match c with | .mk x => wp x post epost
  ewp_monotone c post post' epost epost' he hp := by
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
    [EffWP e₁ m Pred EPred] [EffWP e₂ m Pred EPred] : EffWP (EffSum e₁ e₂) m Pred EPred where
  ewp c post epost := match c with
    | .inl c => ewp c post epost
    | .inr c => ewp c post epost
  ewp_monotone c post post' epost epost' he hp := by
    cases c <;> exact ewp_monotone _ post post' epost epost' he hp

instance instLawfulEffWPSum [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred]
    [HasInterpreter e₁ m] [HasInterpreter e₂ m]
    [EffWP e₁ m Pred EPred] [EffWP e₂ m Pred EPred]
    [LawfulEffWP e₁ m Pred EPred] [LawfulEffWP e₂ m Pred EPred] :
    LawfulEffWP (EffSum e₁ e₂) m Pred EPred where
  ewp_le_wp_interp c post epost :=
    match c with
    | .inl c => LawfulEffWP.ewp_le_wp_interp (m := m) c post epost
    | .inr c => LawfulEffWP.ewp_le_wp_interp (m := m) c post epost
