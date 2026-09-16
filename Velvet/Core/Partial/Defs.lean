module

-- `Lean.Order.admissible` is a non-`@[expose]` definition, so unfolding it in the
-- admissibility proofs below requires importing its implementation.
import all Init.Internal.Order.Basic
public import Velvet.Core.Specs
public import Std.Internal.Do
public import Std.Internal.Do.Triple.SpecLemmas

open Std.Internal.Do
open Std.Internal.Do.Assertion
open Lean.Order

universe u u₁ u₂ v w

namespace WPPartial

/-- Typeclass for monads whose weakest precondition operator is continuous with respect to CCPO chain limits
(fixed-point admissibility). This supports partial correctness verification of possibly divergent recursive loops. -/
public theorem emptyChain {α : Type u} [PartialOrder α] : chain (fun (_ : α) => False) :=
  fun _ _ h => False.elim h

/--
`WPPartial` axiomatizes partial-correctness weakest precondition reasoning over
monadic computations `m` equipped with a chain-complete partial order (`CCPO`).

### Type Parameters (outParams)
- `m`: The monadic computation type (e.g. `Option`, `StateT σ Option`).
- `Pred`: The assertion type for preconditions / standard state predicates (e.g. `Prop`, `σ → Prop`).
- `EPred`: The assertion type for signals / exceptional postconditions (e.g. `Unit → Prop`, `(ε → Pred) × EPred`).
- `div_post`: The canonical divergence postcondition representing "divergence is permitted"
  (e.g. `(fun _ => True)` for `Option`).
- `div_pre`: Predicate transformer mapping an exceptional postcondition `epost : EPred` to the
  weakest precondition needed when a computation diverges (`wp ⊥ post epost = div_pre epost`).

### Fields
- `csup_lift`: Scott-subcontinuity: weakest preconditions commute with chain suprema, ensuring
  the admissibility of Hoare triple motives for Scott fixpoint induction.
- `wp_bot`: Characterizes the weakest precondition of the bottom / diverging computation `⊥`.
- `le_divergence_post`: Ensures `⊥` is universally valid under the default divergence postcondition
  (`pre ⊑ div_pre div_post`).
-/
public class WPPartial (m : Type u → Type v)
    (Pred : outParam (Type u₁)) (EPred : outParam (Type u₂))
    (div_post : outParam EPred) (div_pre : outParam (EPred → Pred))
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ α, CCPO (m α)] where
  /-- Weakest preconditions commute with chain suprema (Scott admissibility). -/
  csup_lift {α : Type u} {c : m α → Prop} (hc : chain c) (hne : ∃ x, c x) (Q : α → Pred) (E : EPred) :
    (⨅ (x : {x : m α // c x}), wp x.val Q E) ⊑ wp (CCPO.csup hc) Q E
  /-- Weakest precondition of divergence `⊥` evaluated against `epost`. -/
  wp_bot {α : Type u} (post : α → Pred) (epost : EPred) :
    wp (Prog := m α) (CCPO.csup (α := m α) (c := fun _ => False) emptyChain) post epost = div_pre epost
  /-- Divergence is valid for any precondition under the default `div_post`. -/
  le_divergence_post (pre : Pred) : pre ⊑ div_pre div_post

/-- Compatibility accessor for `divergence_post` -/
public def WPPartial.divergence_post (m : Type u → Type v)
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ α, CCPO (m α)]
    [WPPartial m Pred EPred div_post div_pre] : EPred := div_post

/-- Compatibility accessor for `divergence_pre` -/
public def WPPartial.divergence_pre (m : Type u → Type v)
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ α, CCPO (m α)]
    [WPPartial m Pred EPred div_post div_pre] : EPred → Pred := div_pre

/-- Admissibility of the Hoare wp inequality for Scott fixpoint induction.

Proved by case analysis on the chain `c`:
* if `c` is non-empty, `WPPartial.csup_lift` transports the pointwise entailments through the
  chain supremum, since `pre` is below the infimum of the `wp`s of the chain elements;
* if `c` is empty it is `fun _ => False`, so `CCPO.csup` is the diverging computation `⊥` and
  `WPPartial.wp_bot` reduces the goal to `hbot`. -/
public theorem admissible_triple_wp
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [instCCPO : ∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre]
    (pre : Pred) (post : β → Pred) (epost : EPred)
    (hbot : pre ⊑ div_pre epost) :
    admissible (fun (c : m β) => pre ⊑ wp c post epost) := by
  intro c hc h
  by_cases hne : ∃ x, c x
  · exact PartialOrder.rel_trans
      (le_iInf (fun (x : {x : m β // c x}) => wp x.val post epost) pre
        (fun x => h x.val x.property))
      (instWP.csup_lift hc hne post epost)
  · have hceq : c = fun _ => False := by
      funext x
      simp only [eq_iff_iff, iff_false]
      intro hx
      exact hne ⟨x, hx⟩
    subst hceq
    show pre ⊑ wp (Prog := m β) (CCPO.csup (α := m β) (c := fun _ => False) emptyChain) post epost
    rw [instWP.wp_bot post epost]
    exact hbot

public theorem admissible_triple_wp_partial
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [instCCPO : ∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre]
    (pre : Pred) (post : β → Pred) :
    admissible (fun (c : m β) => pre ⊑ wp c post div_post) :=
  admissible_triple_wp pre post div_post (instWP.le_divergence_post pre)

/-- Admissibility of Hoare triple motives for Scott fixpoint induction.
`Triple` is a one-field structure around the wp entailment, so this is `admissible_triple_wp`
packed and unpacked. -/
public theorem admissible_triple
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [instCCPO : ∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre]
    (pre : Pred) (post : β → Pred) (epost : EPred)
    (hbot : pre ⊑ div_pre epost) :
    admissible (fun (c : m β) => ⦃ pre ⦄ c ⦃ post ; epost ⦄) := fun c hc h =>
  ⟨admissible_triple_wp pre post epost hbot c hc fun x hx => (h x hx).le_wp⟩

public theorem admissible_triple_partial
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [instCCPO : ∀ α, CCPO (m α)] [instWP : WPPartial m Pred EPred div_post div_pre]
    (pre : Pred) (post : β → Pred) :
    admissible (fun (c : m β) => ⦃ pre ⦄ c ⦃ post ; div_post ⦄) :=
  admissible_triple pre post div_post (instWP.le_divergence_post pre)

/-- Admissibility of Hoare triple motives for 1-argument recursive methods. -/
public theorem admissible_pi_triple
    {α : Type u₁} {β : Type u₂} {m : Type u₂ → Type v}
    {Pred : Type u₃} {EPred : Type u₄} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    (pre : α → Pred) (post : α → β → Pred) (epost : α → EPred)
    (hbot : ∀ x, pre x ⊑ div_pre (epost x)) :
    admissible (fun (f : α → m β) => ∀ x, ⦃ pre x ⦄ f x ⦃ post x ; epost x ⦄) := by
  apply Lean.Order.admissible_pi_apply (P := fun x (c : m β) => ⦃ pre x ⦄ c ⦃ post x ; epost x ⦄)
  intro x
  exact admissible_triple (pre x) (post x) (epost x) (hbot x)

/-- Admissibility of Hoare triple motives for 2-argument recursive methods. -/
public theorem admissible_pi2_triple
    {α₁ : Type u₁} {α₂ : Type u₂} {β : Type u₃} {m : Type u₃ → Type v}
    {Pred : Type u₄} {EPred : Type u₅} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    (pre : α₁ → α₂ → Pred) (post : α₁ → α₂ → β → Pred) (epost : α₁ → α₂ → EPred)
    (hbot : ∀ x y, pre x y ⊑ div_pre (epost x y)) :
    admissible (fun (f : α₁ → α₂ → m β) => ∀ x y, ⦃ pre x y ⦄ f x y ⦃ post x y ; epost x y ⦄) := by
  apply Lean.Order.admissible_pi_apply (P := fun x (g : α₂ → m β) => ∀ y, ⦃ pre x y ⦄ g y ⦃ post x y ; epost x y ⦄)
  intro x
  exact admissible_pi_triple (pre x) (post x) (epost x) (hbot x)

end WPPartial
