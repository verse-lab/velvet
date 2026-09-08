module

public import Velvet.Core.NonDet.Defs
public import Velvet.Core.Loop.Gadgets
public import Std.WP

open Std.WP Lean.Order Loop.Gadget WPPartial

universe u v w z

@[expose] public section

variable {mode : NondetMode}
variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable {div_post : EPred} {div_pre : EPred → Pred}
variable [Monad m] [Assertion Pred] [Heyting Pred] [Assertion EPred]

/-- Non-deterministic choice quantifier. Demonic choice requires all valid
branches and requires `fallback` whenever no valid branch exists. Angelic
choice requires one valid branch and ignores `fallback`. -/
public noncomputable def NondetMode.choice (mode : NondetMode) {τ : Type u}
    (p : τ → Prop) (post : τ → Pred) (fallback : Pred) : Pred :=
  match mode with
  | .demonic =>
      (⌜¬ ∃ a, p a⌝ ⇨ fallback) ⊓ ⨅ (a : { a : τ // p a }), post a.val
  | .angelic => ⨆ (a : { a : τ // p a }), post a.val

theorem choice_mono (mode : NondetMode) {τ : Type u} (p : τ → Prop)
    {post post' : τ → Pred} {fallback fallback' : Pred}
    (hpost : ∀ t, post t ⊑ post' t) (hfallback : fallback ⊑ fallback') :
    mode.choice p post fallback ⊑ mode.choice p post' fallback' := by
  cases mode with
  | demonic =>
      apply le_meet
      · apply PartialOrder.rel_trans (meet_le_left _ _)
        exact himp_mono_right hfallback
      · apply PartialOrder.rel_trans (meet_le_right _ _)
        exact iInf_mono (fun (a : { a // p a }) => hpost a.val)
  | angelic => exact iSup_mono (fun (a : { a // p a }) => hpost a.val)

omit [Heyting Pred] in
@[simp]
public theorem choice_demonic {τ : Type u} (p : τ → Prop) (post : τ → Pred)
    (fallback : Pred) :
    NondetMode.demonic.choice p post fallback =
      (⌜¬ ∃ a, p a⌝ ⇨ fallback) ⊓
        ⨅ (a : { a : τ // p a }), post a.val := rfl

omit [Heyting Pred] in
@[simp]
public theorem choice_angelic {τ : Type u} (p : τ → Prop) (post : τ → Pred)
    (fallback : Pred) :
    NondetMode.angelic.choice p post fallback =
      ⨆ (a : { a : τ // p a }), post a.val := rfl

namespace NonDetT

theorem meet_mono {Pred : Type w} [Assertion Pred] {P P' Q Q' : Pred}
    (hP : P ⊑ P') (hQ : Q ⊑ Q') : P ⊓ Q ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_of_left_le hP) (meet_le_of_right_le hQ)

theorem sup_mono' {Pred : Type w} [Assertion Pred] {P P' Q Q' : Pred}
    (hP : P ⊑ P') (hQ : Q ⊑ Q') : P ⊔ Q ⊑ P' ⊔ Q' :=
  join_mono hP hQ

/-- Unified weakest-precondition semantics for `NonDetT mode m`.

Demonic choice requires `div_pre epost` when no witness exists. A
loop can be justified either by an invariant whose states permit divergence,
or by an invariant paired with a strictly decreasing measure. -/
public noncomputable def wp [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u}
    (x : NonDetT mode m α) (post : α → Pred) (epost : EPred) : Pred :=
  match x with
  | .pure ret => post ret
  | .vis c f => Std.WP.wp c (fun b => wp (f b) post epost) epost
  | @NonDetT.pickCont _ _ _ _ p _ f =>
      mode.choice p (fun t => wp (f t) post epost) (div_pre epost)
  | .repeatCont (β := β) init f cont =>
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

public noncomputable abbrev wpDemonic [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u} :=
  wp (mode := .demonic) (m := m) (α := α)

public noncomputable abbrev wpAngelic [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u} :=
  wp (mode := .angelic) (m := m) (α := α)

omit [Heyting Pred] in
public theorem wp_bind [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α β : Type u}
    (x : NonDetT mode m α) (f : α → NonDetT mode m β)
    (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost := by
  induction x generalizing post epost with
  | pure ret => rfl
  | vis c g ih =>
      show Std.WP.wp c (fun b => wp (g b >>= f) post epost) epost =
        Std.WP.wp c (fun b => wp (g b)
          (fun a => wp (f a) post epost) epost) epost
      congr 1
      funext b
      exact ih b f post epost
  | pickCont τ p g ih =>
      show mode.choice p (fun t => wp (g t >>= f) post epost) (div_pre epost) =
        mode.choice p (fun t => wp (g t)
          (fun a => wp (f a) post epost) epost) (div_pre epost)
      congr 1
      funext t
      exact ih t f post epost
  | @repeatCont α' state init g cont _ ih =>
      change
        ((⨆ (inv : state → Pred) (stepPost : state → ForInStep state → Pred),
          ⌜∀ b, inv b ⊑ wp (g b) (stepPost b) epost⌝ ⊓ inv init ⊓
          ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
          ⌜∀ b b', stepPost b (.done b') ⊑ wp (cont b' >>= f) post epost⌝ ⊓
          ⌜∀ b, inv b ⊑ div_pre epost⌝) ⊔
        (⨆ (inv : ForInStep state → Pred) (measure : state → Nat),
          ⌜∀ b, inv (.yield b) ⊑ wp (g b)
            (fun r => match r with
              | .yield b' => inv (.yield b') ⊓ ⌜measure b' < measure b⌝
              | .done b' => inv (.done b')) epost⌝ ⊓
          inv (.yield init) ⊓
          ⌜∀ b, inv (.done b) ⊑ wp (cont b >>= f) post epost⌝)) =
        ((⨆ (inv : state → Pred) (stepPost : state → ForInStep state → Pred),
          ⌜∀ b, inv b ⊑ wp (g b) (stepPost b) epost⌝ ⊓ inv init ⊓
          ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
          ⌜∀ b b', stepPost b (.done b') ⊑
            wp (cont b') (fun a => wp (f a) post epost) epost⌝ ⊓
          ⌜∀ b, inv b ⊑ div_pre epost⌝) ⊔
        (⨆ (inv : ForInStep state → Pred) (measure : state → Nat),
          ⌜∀ b, inv (.yield b) ⊑ wp (g b)
            (fun r => match r with
              | .yield b' => inv (.yield b') ⊓ ⌜measure b' < measure b⌝
              | .done b' => inv (.done b')) epost⌝ ⊓
          inv (.yield init) ⊓
          ⌜∀ b, inv (.done b) ⊑
            wp (cont b) (fun a => wp (f a) post epost) epost⌝))
      simp only [ih]

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

public theorem wp_monotone [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] {α : Type u} (x : NonDetT mode m α) :
    ∀ (post post' : α → Pred) (epost epost' : EPred),
      epost ⊑ epost' → post ⊑ post' → wp x post epost ⊑ wp x post' epost' := by
  induction x with
  | pure ret =>
    intro post post' epost epost' _ hpost
    exact hpost ret
  | vis c g ih =>
    intro post post' epost epost' hepost hpost
    dsimp [wp]
    apply WP.wp_trans_monotone c
    · exact hepost
    · intro b
      exact ih b post post' epost epost' hepost hpost
  | pickCont τ p g ih =>
    intro post post' epost epost' hepost hpost
    cases mode with
    | demonic =>
      simp only [wp]
      apply meet_mono
      · exact himp_mono_right
          (div_pre_mono (m := m) (div_post := div_post)
            (div_pre := div_pre) hepost)
      · apply iInf_mono
        intro a
        exact ih a.val post post' epost epost' hepost hpost
    | angelic =>
      simp only [wp]
      apply iSup_mono
      intro a
      exact ih a.val post post' epost epost' hepost hpost
  | repeatCont init g cont g_ih cont_ih =>
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
    WP (NonDetT mode m α) α Pred EPred where
  wpTrans x := ⟨wp x⟩
  wp_trans_monotone x := wp_monotone x

public noncomputable instance instWPMonadNonDetT [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre] :
    WPMonad (NonDetT mode m) Pred EPred where
  toWP _ := wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := by
    show wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost
    rw [wp_bind]

@[simp]
public theorem wp_pickSuchThat [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] (τ : Type u) (p : τ → Prop)
    [wf : Findable p] (name : Lean.Name)
    (post : τ → Pred) (epost : EPred) :
    Std.WP.wp (NonDetT.pickSuchThat (m := m) (mode := mode) τ p (wf := wf) name) post epost =
      mode.choice p post (div_pre epost) := rfl

@[simp]
public theorem wp_pick (τ : Type u) [Inhabited τ] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    (post : τ → Pred) (epost : EPred) :
    Std.WP.wp (NonDetT.pick (m := m) (mode := mode) τ) post epost =
      match mode with
      | .demonic => ⨅ (a : τ), post a
      | .angelic => ⨆ (a : τ), post a := by
  change mode.choice (fun _ => True) post (div_pre epost) = _
  cases mode
  · rw [choice_demonic]
    have hnone : (⌜¬ ∃ _ : τ, True⌝ : Pred) = ⊥ := by simp
    rw [hnone, bot_himp, top_meet]
    apply PartialOrder.rel_antisymm
    · apply le_iInf; intro a; exact iInf_le (i := (⟨a, trivial⟩ : { a : τ // True })) (fun (a : { a : τ // True }) => post a.val)
    · apply le_iInf; intro ⟨a, _⟩; exact iInf_le (i := a) post
  · apply PartialOrder.rel_antisymm
    · apply iSup_le; intro ⟨a, _⟩; exact le_iSup (i := a) post
    · apply iSup_le; intro a; exact le_iSup (i := (⟨a, trivial⟩ : { a : τ // True })) (fun (a : { a : τ // True }) => post a.val)

@[simp]
public theorem wp_assume' [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] (as : Prop)
    [Decidable as] (post : PUnit.{u+1} → Pred) (epost : EPred) :
    Std.WP.wp (NonDetT.assume' (m := m) (mode := mode) as) post epost =
      match mode with
      | .demonic => (⌜¬as⌝ ⇨ div_pre epost) ⊓ (⌜as⌝ ⇨ post .unit)
      | .angelic => ⌜as⌝ ⊓ post .unit := by
  change mode.choice (fun _ => as) (fun _ => post .unit) (div_pre epost) = _
  cases mode with
  | demonic =>
    rw [choice_demonic]
    by_cases h : as
    · have hinf : (⨅ (_ : {a : PUnit.{u+1} // as}), post .unit) = post .unit := by
        apply PartialOrder.rel_antisymm
        · exact iInf_le (i := (⟨.unit, h⟩ : {a : PUnit.{u+1} // as})) _
        · apply le_iInf
          intro _
          exact PartialOrder.rel_refl
      have hp : (⌜as⌝ : Pred) = ⊤ := by simp [CompleteLattice.ofProp, h]
      have hnot : (⌜¬ ∃ _ : PUnit.{u+1}, as⌝ : Pred) = ⊥ := by simp [h]
      have hnotAs : (⌜¬as⌝ : Pred) = ⊥ := by simp [h]
      rw [hp, hnot, hnotAs, hinf, bot_himp, top_meet, top_himp]
      simp only [top_meet]
    · have hinf : (⨅ (_ : {a : PUnit.{u+1} // as}), post .unit) = ⊤ := by
        apply PartialOrder.rel_antisymm (le_top _)
        apply le_iInf
        intro a
        exact False.elim (h a.property)
      have hp : (⌜as⌝ : Pred) = ⊥ := by simp [CompleteLattice.ofProp, h]
      have hnot : (⌜¬ ∃ _ : PUnit.{u+1}, as⌝ : Pred) = ⊤ := by simp [h]
      have hnotAs : (⌜¬as⌝ : Pred) = ⊤ := by simp [h]
      rw [hp, hnot, hnotAs, hinf, top_himp, meet_top, bot_himp]
      simp only [meet_top]
  | angelic =>
    rw [choice_angelic]
    by_cases h : as
    · have hsup : (⨆ (_ : {a : PUnit.{u+1} // as}), post .unit) = post .unit := by
        apply PartialOrder.rel_antisymm
        · apply iSup_le
          intro _
          exact PartialOrder.rel_refl
        · exact le_iSup
            (fun (_ : {a : PUnit.{u+1} // as}) => post .unit)
            (⟨.unit, h⟩ : {a : PUnit.{u+1} // as})
      have hp : (⌜as⌝ : Pred) = ⊤ := by simp [CompleteLattice.ofProp, h]
      rw [hp, hsup, top_meet]
    · have hsup : (⨆ (_ : {a : PUnit.{u+1} // as}), post .unit) = ⊥ := by
        apply PartialOrder.rel_antisymm
        · apply iSup_le
          intro a
          exact False.elim (h a.property)
        · exact bot_le _
      have hp : (⌜as⌝ : Pred) = ⊥ := by simp [CompleteLattice.ofProp, h]
      rw [hp, hsup, bot_meet]

/- ============================================================================
   DEMONIC HOARE / VC TRIPLE SPECIFICATIONS
   ============================================================================ -/

@[spec]
public theorem demonic_pickSuchThat_spec {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Heyting Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre]
    (name : Lean.Name) (τ : Type u) (p : τ → Prop) [wf : Findable p]
    {post : τ → Pred} {epost : EPred} :
    Triple (NonDetT.pickSuchThat (mode := .demonic) (m := m) τ p (wf := wf) name)
      ((⌜¬ ∃ a, p a⌝ ⇨ div_pre epost) ⊓
        ⨅ (a : { a : τ // p a }), post a.val) post epost := by
  refine Triple.intro ?_
  rw [wp_pickSuchThat, choice_demonic]

@[spec]
public theorem demonic_pick_spec {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Heyting Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre]
    (τ : Type u) [Inhabited τ] {post : τ → Pred} {epost : EPred} :
    Triple (NonDetT.pick (mode := .demonic) (m := m) τ)
      (⨅ (a : τ), post a) post epost := by
  refine Triple.intro ?_
  rw [wp_pick]

@[spec]
public theorem demonic_assume_spec {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [Heyting Pred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    (as : Prop) [Decidable as] {post : PUnit.{u+1} → Pred} {epost : EPred} :
    Triple (NonDetT.assume' (mode := .demonic) (m := m) as)
      ((⌜¬as⌝ ⇨ div_pre epost) ⊓ (⌜as⌝ ⇨ post .unit)) post epost := by
  refine Triple.intro ?_
  rw [wp_assume']

/- ============================================================================
   ANGELIC HOARE / VC TRIPLE SPECIFICATIONS
   ============================================================================ -/

@[spec]
public theorem angelic_pickSuchThat_spec {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [Heyting Pred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    (name : Lean.Name) (τ : Type u) (p : τ → Prop) [wf : Findable p]
    (w : τ)
    (h : Named.mk name none (p w))
    {post : τ → Pred} {epost : EPred} :
    Triple (NonDetT.pickSuchThat (mode := .angelic) (m := m) τ p (wf := wf) name)
      ((⌜(Named.mk name none (p w) : Prop)⌝ ⇨ post w) : Pred) post epost := by
  apply Triple.intro
  change (⌜(Named.mk name none (p w) : Prop)⌝ ⇨ post w) ⊑
    Std.WP.wp (NonDetT.pickSuchThat (m := m) (mode := .angelic) τ p (wf := wf) name) post epost
  rw [wp_pickSuchThat, choice_angelic]
  have hpw : p w := h
  have hp : (⌜(Named.mk name none (p w) : Prop)⌝ : Pred) = ⊤ := by
    simp [CompleteLattice.ofProp, Named.mk_eq, hpw]
  rw [hp, top_himp]
  exact le_iSup (α := Pred) (i := ⟨w, h⟩) (fun (a : { a : τ // p a }) => post a.val)

@[spec]
public theorem angelic_pick_spec {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Heyting Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre]
    (τ : Type u) [Inhabited τ] (w : τ) {post : τ → Pred} {epost : EPred} :
    Triple (NonDetT.pick (mode := .angelic) (m := m) τ)
      (post w) post epost := by
  apply Triple.intro
  rw [wp_pick]
  exact le_iSup (i := w) post

@[spec]
public theorem angelic_assume_spec {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [Heyting Pred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    (as : Prop) [Decidable as] {post : PUnit.{u+1} → Pred} {epost : EPred} :
    Triple (NonDetT.assume' (mode := .angelic) (m := m) as)
      (⌜as⌝ ⊓ post .unit) post epost := by
  refine Triple.intro ?_
  rw [wp_assume']

@[spec 1250]
public theorem Spec.whileLoop_partial
    {mode : NondetMode} {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β}
    (inv : β → Pred) (done : β → Pred)
    {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' => inv b'
          | .done b' => done b') einv) :
    Triple (whileLoopPartial init f inv done) (inv init)
      (fun b => binderNameHint b done <| done b) einv := by
  apply Triple.intro
  dsimp only [whileLoopPartial, forIn, instForInLoopNonDetT, NonDetT.wp,
    binderNameHint]
  let stepPost : β → ForInStep β → Pred := fun _ r => match r with
    | .yield b' => inv b'
    | .done b' => done b'
  apply PartialOrder.rel_trans ?_ (left_le_join _ _)
  apply PartialOrder.rel_trans ?_
    (le_iSup (fun inv' => ⨆ (stepPost' : β → ForInStep β → Pred), _) inv)
  apply PartialOrder.rel_trans ?_ (le_iSup (fun stepPost' => _) stepPost)
  have hbody : ∀ b, inv b ⊑ (f () b).wp (stepPost b) einv :=
    fun b => (step b).le_wp
  have hyield : ∀ b b', stepPost b (.yield b') ⊑ inv b' := by
    intro b b'; exact PartialOrder.rel_refl
  have hdone : ∀ b b', stepPost b (.done b') ⊑
      (Pure.pure (f := NonDetT mode m) b').wp (fun b => done b) einv := by
    intro b b'; exact PartialOrder.rel_refl
  have eqBody : (⌜∀ b, inv b ⊑ (f () b).wp (stepPost b) einv⌝ : Pred) = ⊤ := by
    simp [hbody]
  have eqYield : (⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ : Pred) = ⊤ := by
    simp [hyield]
  have eqDone : (⌜∀ b b', stepPost b (.done b') ⊑
      (Pure.pure (f := NonDetT mode m) b').wp (fun b => done b) einv⌝ : Pred) = ⊤ := by
    simp [hdone]
  have eqDiv : (⌜∀ b, inv b ⊑ div_pre einv⌝ : Pred) = ⊤ := by
    simp [hdiv]
  rw [eqBody, eqYield, eqDone, eqDiv]
  exact le_meet _ _ _
    (le_meet _ _ _
      (le_meet _ _ _
        (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
        (le_top _))
      (le_top _))
    (le_top _)

@[spec 1250]
public theorem Spec.whileLoop_total
    {mode : NondetMode} {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β}
    (inv : β → Pred) (done : β → Pred) (measure : β → Named.Measure)
    {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (step : ∀ b,
      Triple (f () b)
        (binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' =>
              match measure b, measure b' with
              | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
                  ⌜Named.mk name stx (next < current)⌝ ⊓ inv b'
          | .done b' => done b')
        einv) :
    Triple (whileLoopTotal init f inv done measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv := by
  apply Triple.intro
  dsimp only [whileLoopTotal, forIn, instForInLoopNonDetT, NonDetT.wp,
    binderNameHint]
  let inv' : ForInStep β → Pred := fun
    | .yield b => inv b
    | .done b => done b
  let measure' : β → Nat := fun b => (measure b).value
  apply PartialOrder.rel_trans ?_ (right_le_join _ _)
  apply PartialOrder.rel_trans ?_
    (le_iSup (fun inv' => ⨆ (measure' : β → Nat), _) inv')
  apply PartialOrder.rel_trans ?_ (le_iSup (fun measure' => _) measure')
  have hbody : ∀ b, inv' (.yield b) ⊑ (f () b).wp
      (fun r => match r with
        | .yield b' => inv' (.yield b') ⊓ ⌜measure' b' < measure' b⌝
        | .done b' => inv' (.done b')) einv := by
    intro b
    apply PartialOrder.rel_trans (step b).le_wp
    apply WP.wp_consequence
    intro r
    cases r with
    | done b' => exact PartialOrder.rel_refl
    | yield b' =>
      dsimp [inv', measure']
      cases hb : measure b with
      | mk name stx current =>
        cases hb' : measure b' with
        | mk name' stx' next =>
          simp only [Named.mk_eq]
          exact le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)
  have hdone : ∀ b, inv' (.done b) ⊑
      (Pure.pure (f := NonDetT mode m) b).wp (fun b => done b) einv := by
    intro b
    exact PartialOrder.rel_refl
  have eqBody : (⌜∀ b, inv' (.yield b) ⊑ (f () b).wp
      (fun r => match r with
        | .yield b' => inv' (.yield b') ⊓ ⌜measure' b' < measure' b⌝
        | .done b' => inv' (.done b')) einv⌝ : Pred) = ⊤ := by
    simp [hbody]
  have eqDone : (⌜∀ b, inv' (.done b) ⊑
      (Pure.pure (f := NonDetT mode m) b).wp (fun b => done b) einv⌝ : Pred) = ⊤ := by
    simp [hdone]
  rw [eqBody, eqDone]
  exact le_meet _ _ _
    (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
    (le_top _)

end NonDetT

export NonDetT (
  wp wpDemonic wpAngelic wp_bind wp_monotone
  wp_pickSuchThat
  wp_pick
  wp_assume'
  demonic_pickSuchThat_spec demonic_pick_spec demonic_assume_spec
  angelic_pickSuchThat_spec angelic_pick_spec angelic_assume_spec
)

end
