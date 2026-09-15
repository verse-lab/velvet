module

public import Velvet.Core.NonDet.Run
public import Velvet.Core.NonDet.WP
public import Velvet.Core.Partial

open Std.Internal.Do Std.Internal.Do.CompleteLattice Lean.Order WPPartial

universe u v w z

@[expose] public section

/-- Pointwise function-order bottom is the constant bottom function. -/
private theorem pi_bot_eq {α : Sort u} {β : α → Sort v} [∀ x, CCPO (β x)] :
    (Lean.Order.bot : ∀ x, β x) = fun _ => Lean.Order.bot := by
  apply PartialOrder.rel_antisymm
  · exact bot_le _
  · intro x
    exact bot_le ((Lean.Order.bot : ∀ x, β x) x)

/-- The operational failure computation is the true bottom of the base
monad's CCPO. -/
public class CCPOBotLawful (m : Type u → Type v) [∀ α, CCPO (m α)] [CCPOBot m] where
  bot_eq : ∀ {α : Type u}, CCPOBot.compBot (m := m) (α := α) = Lean.Order.bot

public instance : CCPOBotLawful Option where
  bot_eq := by
    intro α
    have h : (Lean.Order.bot : Option α) ⊑ none := bot_le none
    generalize hx : (Lean.Order.bot : Option α) = x at h ⊢
    change FlatOrder.rel (b := none) x none at h
    cases h <;> rfl

public instance [∀ α, CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] :
    CCPOBotLawful (ReaderT ρ m) where
  bot_eq := by
    intro α
    rw [pi_bot_eq]
    funext r
    dsimp [CCPOBot.compBot]
    rw [CCPOBotLawful.bot_eq (m := m)]

public instance [∀ α, CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] :
    CCPOBotLawful (StateT σ m) where
  bot_eq := by
    intro α
    rw [pi_bot_eq]
    funext s
    dsimp [CCPOBot.compBot]
    rw [CCPOBotLawful.bot_eq (m := m)]

public instance [∀ α, CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] :
    CCPOBotLawful (ExceptT ε m) where
  bot_eq := by
    intro α
    exact CCPOBotLawful.bot_eq (m := m)

namespace Soundness.DemonicChoice

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable {div_post : EPred} {div_pre : EPred → Pred}
variable [Monad m] [CCPOBot m] [∀ γ, CCPO (m γ)] [MonoBind m]
variable [CCPOBotLawful m]
variable [Assertion Pred] [∀ P : Pred, PreservesSup (meet P)] [Assertion EPred] [WPMonad m Pred EPred]
variable [WPPartial m Pred EPred div_post div_pre]

omit [MonoBind m] [∀ P : Pred, PreservesSup (meet P)]
    [WPPartial m Pred EPred div_post div_pre] in
private theorem wp_compBot_eq_div_pre {α : Type u}
    [WPPartial m Pred EPred div_post div_pre]
    (post : α → Pred) (epost : EPred) :
    Std.Internal.Do.wp (CCPOBot.compBot (m := m) (α := α)) post epost = div_pre epost := by
  rw [CCPOBotLawful.bot_eq]
  have hbotEq : (⊥ : m α) =
      CCPO.csup (α := m α) (c := fun _ => False) WPPartial.emptyChain := by
    apply PartialOrder.rel_antisymm
    · exact bot_le _
    · apply csup_le
      intro y hy
      contradiction
  rw [hbotEq, WPPartial.wp_bot (div_post := div_post) (div_pre := div_pre)]

/-- Demonic nondeterministic execution refines the unified logical WP for any
exceptional postcondition. Empty choices reduce to `div_pre epost`; loops are
justified by either divergence-safe fixed-point induction or a decreasing
measure. -/
public theorem ExtractNonDet.extract_refines_wp {α : Type u}
    (s : DemonicT m α) (post : α → Pred) (epost : EPred) :
    NonDetT.wp s post epost ⊑ Std.Internal.Do.wp s.run post epost := by
  induction s with
  | pure x =>
      simp only [NonDetT.wp, NonDetT.run_pure]
      exact WPMonad.pure_le_wp_pure x post epost
  | vis c f ih =>
      simp only [NonDetT.wp, NonDetT.run_vis]
      apply PartialOrder.rel_trans
      · apply WP.wp_trans_monotone c
        · exact PartialOrder.rel_refl
        · intro b
          exact ih b post
      · exact WPMonad.bind_le_wp_bind c (fun b => (f b).run) post epost
  | @pickCont α τ p wf f ih =>
      simp only [NonDetT.wp, choice_demonic, NonDetT.run_pickCont]
      split
      · rename_i hfind
        have hnone : ∀ x, ¬p x := Findable.find_none (p := p) (by simpa using hfind)
        have hexists : ¬∃ x, p x := by simpa using hnone
        have heq : (⌜¬ ∃ x, p x⌝ : Pred) = ⊤ := by simp [hexists]
        rw [wp_compBot_eq_div_pre, heq, top_himp]
        exact meet_le_left _ _
      · rename_i x hx
        have hp : p x := Findable.find_some_p hx
        apply PartialOrder.rel_trans (meet_le_right _ _)
        exact PartialOrder.rel_trans
          (iInf_le (i := (⟨x, hp⟩ : {a // p a}))
            (fun a => NonDetT.wp (f a.val) post epost))
          (ih x post)
  | @repeatCont α β init f cont f_ih cont_ih =>
      simp only [NonDetT.wp]
      apply join_le
      · apply iSup_le; intro inv
        apply iSup_le; intro stepPost
        apply ofProp_meet_le_right; intro hdiv
        apply ofProp_meet_le_right; intro hdone
        apply ofProp_meet_le_right; intro hyield
        apply ofProp_meet_le_left; intro hbody
        rw [NonDetT.run_repeatCont]
        let inv' : β ⊕ β → Pred := fun
          | .inl b => inv b
          | .inr b => NonDetT.wp (cont b) post epost
        have hloop : Triple
            (Loop.forIn.loop (fun _ b => (f b).run) init)
            (inv' (.inl init)) (fun b => inv' (.inr b)) epost := by
          apply Loop.forInLoop_partial (div_post := div_post) (div_pre := div_pre)
          · exact hdiv
          · intro b
            apply Triple.intro
            apply PartialOrder.rel_trans (hbody b)
            apply PartialOrder.rel_trans (f_ih b (stepPost b))
            apply WP.wp_consequence
            intro r
            cases r with
            | yield b' => exact hyield b b'
            | done b' => exact hdone b b'
        apply PartialOrder.rel_trans hloop.le_wp
        apply PartialOrder.rel_trans
        · exact WP.wp_consequence _ _ _ epost (fun b => cont_ih b post)
        · exact WPMonad.bind_le_wp_bind _ _ post epost
      · apply iSup_le; intro inv
        apply iSup_le; intro measure
        apply ofProp_meet_le_right; intro hdone
        apply ofProp_meet_le_left; intro hbody
        rw [NonDetT.run_repeatCont]
        have hloop : Triple
            (Loop.forIn.loop (fun _ b => (f b).run) init)
            (inv (.yield init)) (fun b => inv (.done b)) epost := by
          apply Loop.forInLoop_total (measure := measure)
          intro b
          apply Triple.intro
          exact PartialOrder.rel_trans (hbody b)
            (f_ih b _)
        apply PartialOrder.rel_trans hloop.le_wp
        apply PartialOrder.rel_trans
        · apply WP.wp_consequence
          intro b
          exact PartialOrder.rel_trans (hdone b) (cont_ih b post)
        · exact WPMonad.bind_le_wp_bind _ _ post epost

/-- Demonic Hoare triples are preserved by deterministic execution. -/
public theorem ExtractNonDet.extract_refines {α : Type u}
    {pre : Pred} {s : DemonicT m α} {post : α → Pred} {epost : EPred} :
    Triple s pre post epost → Triple s.run pre post epost := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans tr.le_wp
    (ExtractNonDet.extract_refines_wp s post epost))

end Soundness.DemonicChoice

end
