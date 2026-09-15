import Velvet.Core.FreerMonad.Defs
import Velvet.Core.Specs
import Velvet.Core.Partial

import Std.WP
import Std.WP.Gadget.ForIn
import Std.WP.Triple.SpecLemmas
import Std.Internal.ForIn

open Std.Internal
open Std.WP
open Std.WP.Assertion
open Lean.Order
open WPPartial
open Lean.Order



theorem inf_mono [Assertion Pred] {P P' Q Q' : Pred} (hp : P ⊑ P') (hq : Q ⊑ Q'):
  meet P Q ⊑ meet P' Q' := by
    apply le_meet
    { apply PartialOrder.rel_trans
      apply meet_le_left
      apply hp }
    apply PartialOrder.rel_trans
    apply meet_le_right
    apply hq

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable {div_post : EPred} {div_pre : EPred → Pred}
variable [Monad m] [Assertion Pred] [Heyting Pred] [Assertion EPred] [intrp : HasInterpreter e m]

namespace FreerMonad

noncomputable def wp [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u}
    (x : FreerMonad e α) (post : α → Pred) (epost : EPred) : Pred :=
  match x with
  | .ret val => post val
  | .vis c f => Std.WP.wp (intrp.interp c) (fun b => wp (f b) post epost) epost
  | .iter (β := β) init f cont =>
      let partialBranch :=
        ⨆ (inv : β → Pred) (stepPost : β → ForInStep β → Pred),
          ⌜∀ b, inv b ⊑ wp (f b) (stepPost b) epost⌝ ⊓
          inv init ⊓
          ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
          ⌜∀ b b', stepPost b (.done b') ⊑ wp (cont b') post epost⌝ ⊓
          ⌜∀ b, inv b ⊑ div_pre epost⌝
      let totalBranch :=
        ⨆ (inv : ForInStep β → Pred) (measure : β → Nat),
          ⌜∀ b, inv (.yield b) ⊑ wp (f b)
            (fun r => match r with
              | .yield b' => inv (.yield b') ⊓ ⌜measure b' < measure b⌝
              | .done b' => inv (.done b')) epost⌝ ⊓
          inv (.yield init) ⊓
          ⌜∀ b, inv (.done b) ⊑ wp (cont b) post epost⌝
      partialBranch ⊔ totalBranch

omit [Heyting Pred] in
public theorem div_pre_mono [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {epost epost' : EPred}
    (h : epost ⊑ epost') : div_pre epost ⊑ div_pre epost' := by
  let post : PUnit.{u+1} → Pred := fun _ => ⊤
  rw [← WPPartial.wp_bot (m := m) (div_post := div_post) (div_pre := div_pre) post epost]
  rw [← WPPartial.wp_bot (m := m) (div_post := div_post) (div_pre := div_pre) post epost']
  apply WP.wp_trans_monotone
  · exact h
  · intro _
    exact PartialOrder.rel_refl


theorem sup_mono' {Pred : Type w} [Assertion Pred] {P P' Q Q' : Pred}
    (hP : P ⊑ P') (hQ : Q ⊑ Q') : P ⊔ Q ⊑ P' ⊔ Q' :=
  join_mono hP hQ

omit [Heyting Pred] in
public theorem wp_monotone [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u} (x : FreerMonad e α) :
    ∀ (post post' : α → Pred) (epost epost' : EPred),
      epost ⊑ epost' → post ⊑ post' → wp x post epost ⊑ wp x post' epost' := by
  induction x with
  | ret val =>
    intro post post' epost epost' _ hpost
    exact hpost val
  | vis c g ih =>
    intro post post' epost epost' hepost hpost
    dsimp [wp]
    apply WP.wp_trans_monotone (intrp.interp c)
    · exact hepost
    · intro b
      exact ih b post post' epost epost' hepost hpost
  | iter init g cont g_ih cont_ih =>
    intro post post' epost epost' hepost hpost
    simp only [wp]
    apply sup_mono'
    · apply iSup_mono; intro inv
      apply iSup_mono; intro stepPost
      refine meet_mono (meet_mono (meet_mono (meet_mono ?_ PartialOrder.rel_refl)
        PartialOrder.rel_refl) ?_) ?_
      · apply ofProp_mono
        intro h b
        exact PartialOrder.rel_trans (h b)
          (g_ih b (stepPost b) (stepPost b) epost epost' hepost
            (fun _ => PartialOrder.rel_refl))
      · apply ofProp_mono
        intro h b b'
        exact PartialOrder.rel_trans (h b b')
          (cont_ih b' post post' epost epost' hepost hpost)
      · apply ofProp_mono
        intro h b
        exact PartialOrder.rel_trans (h b) (div_pre_mono (m := m) (div_post := div_post) (div_pre := div_pre) hepost)
    · apply iSup_mono; intro inv
      apply iSup_mono; intro measure
      refine meet_mono (meet_mono ?_ PartialOrder.rel_refl) ?_
      · apply ofProp_mono
        intro h b
        exact PartialOrder.rel_trans (h b)
          (g_ih b _ _ epost epost' hepost (fun _ => PartialOrder.rel_refl))
      · apply ofProp_mono
        intro h b
        exact PartialOrder.rel_trans (h b)
          (cont_ih b post post' epost epost' hepost hpost)

@[instance_reducible]
public noncomputable def wpInst [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u} :
    WP (FreerMonad e α) α Pred EPred where
  wpTrans x := ⟨wp x⟩
  wp_trans_monotone x := wp_monotone x

public noncomputable instance instWPMonadFreerMonad [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre] :
    WPMonad (FreerMonad e) Pred EPred where
  toWP _ := wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := by
    show wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost
    induction x with
    | ret val =>
      simp [wp, Bind.bind, FreerMonad.bind]
      rfl
    | vis x k k_ih =>
      simp [wp, Bind.bind, FreerMonad.bind]
      apply WP.wp_consequence
      simp
      intro s
      apply k_ih
    | iter init body k body_ih k_ih =>
      simp [wp, Bind.bind, FreerMonad.bind] at *
      apply sup_mono'
      { apply iSup_mono
        intro inv
        apply iSup_mono
        intro b
        simp; unhygienic intros; simp [*]
        repeat' apply le_meet
        any_goals simp
        { rfl }
        simp [CompleteLattice.ofProp]
        split
        { simp }
        rename_i hc
        false_or_by_contra
        apply hc; clear hc
        intro b1 b2
        apply PartialOrder.rel_trans
        { apply a_1 b1 b2 }
        apply k_ih }
      apply iSup_mono
      intro inv
      apply iSup_mono
      intro b
      simp; unhygienic intros; simp [*]
      repeat' apply le_meet
      any_goals simp
      { rfl }
      simp [CompleteLattice.ofProp]
      split
      { simp }
      rename_i hc
      false_or_by_contra
      apply hc; clear hc
      intro b1
      apply PartialOrder.rel_trans
      { apply a b1 }
      apply k_ih

theorem soundness [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre] (c : FreerMonad e α):
    ⦃ pre ⦄ c ⦃ post ⦄ → ⦃ pre ⦄ c.interp ⦃ post ⦄ := by
      intro htc
      rcases htc with ⟨htc⟩
      constructor
      apply PartialOrder.rel_trans
      { apply htc }
      unfold WP.wp
      rw [WP.wpTrans]
      simp [instWPOfWPMonad, WPMonad.toWP, wpInst]
      clear htc
      induction c with
      | ret val =>
        simp [FreerMonad.wp, FreerMonad.interp]
        apply WPMonad.pure_le_wp_pure
      | vis x k k_ih =>
        simp [FreerMonad.wp, FreerMonad.interp]
        apply PartialOrder.rel_trans; rotate_left
        apply WPMonad.bind_le_wp_bind
        apply WP.wp_consequence
        simp
        intro b
        apply k_ih
      | iter init f cont f_ih cont_ih =>
        rename_i β
        simp [FreerMonad.wp, FreerMonad.interp]
        apply join_le
        · apply iSup_le; intro inv
          apply iSup_le; intro stepPost
          apply ofProp_meet_le_right; intro hdiv
          apply ofProp_meet_le_right; intro hdone
          apply ofProp_meet_le_right; intro hyield
          apply ofProp_meet_le_left; intro hbody
          let inv' : β ⊕ β → Pred := fun
            | .inl b => inv b
            | .inr b => wp (cont b) post ⊥
          simp [forIn, Lean.Loop.forIn, repeatM]
          have hloop : Triple
              (Loop.forIn.loop (fun _ b => (f b).run) init)
              (inv' (.inl init)) (fun b => inv' (.inr b)) ⊥ := by
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

end FreerMonad
