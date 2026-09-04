module

public import Velvet.Core.NonDet.Defs
public import Velvet.Core.Loop.Gadgets
public import Std.WP

open Std.WP Lean.Order Loop.Gadget

universe u v w z

@[expose] public section

variable {mode : NondetMode}
variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable [Monad m] [Assertion Pred] [Assertion EPred]

/-- Non-deterministic choice quantifier:
- `demonic`: universal choice `⨅` (postcondition must hold for all choices)
- `angelic`: existential choice `⨆` (there exists at least one choice) -/
public noncomputable def NondetMode.choice (mode : NondetMode) {τ : Type u} (p : τ → Prop) (post : τ → Pred) : Pred :=
  match mode with
  | .demonic => ⨅ (a : { a : τ // p a }), post a.val
  | .angelic => ⨆ (a : { a : τ // p a }), post a.val

theorem choice_mono (mode : NondetMode) {τ : Type u} (p : τ → Prop)
    {post post' : τ → Pred} (h : ∀ t, post t ⊑ post' t) :
    mode.choice p post ⊑ mode.choice p post' := by
  cases mode with
  | demonic => exact iInf_mono (fun (a : { a // p a }) => h a.val)
  | angelic => exact iSup_mono (fun (a : { a // p a }) => h a.val)

@[simp]
public theorem choice_demonic {τ : Type u} (p : τ → Prop) (post : τ → Pred) :
    (NondetMode.demonic.choice p post) = ⨅ (a : { a : τ // p a }), post a.val := rfl

@[simp]
public theorem choice_angelic {τ : Type u} (p : τ → Prop) (post : τ → Pred) :
    (NondetMode.angelic.choice p post) = ⨆ (a : { a : τ // p a }), post a.val := rfl

namespace NonDetT

theorem meet_mono {Pred : Type w} [Assertion Pred] {P P' Q Q' : Pred} (hP : P ⊑ P') (hQ : Q ⊑ Q') : P ⊓ Q ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_of_left_le hP) (meet_le_of_right_le hQ)

/-- Unified weakest precondition semantics for `NonDetT mode m`. -/
public noncomputable def wp [WPMonad m Pred EPred] {α : Type u}
    (x : NonDetT mode m α) (post : α → Pred) (epost : EPred) : Pred :=
  match x with
  | .pure ret => post ret
  | .vis c f => Std.WP.wp c (fun b => wp (f b) post epost) epost
  | .pickCont _ p _ f => mode.choice p (fun t => wp (f t) post epost)
  | .repeatCont (β := β) init f cont =>
    ⨆ (inv : β → Pred) (stepPost : β → ForInStep β → Pred),
      ⌜∀ b, inv b ⊑ wp (f b) (stepPost b) epost⌝ ⊓
      inv init ⊓
      ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
      ⌜∀ b b', stepPost b (.done b') ⊑ wp (cont b') post epost⌝

public noncomputable abbrev wpDemonic [WPMonad m Pred EPred] {α : Type u} := wp (mode := .demonic) (m := m) (α := α)
public noncomputable abbrev wpAngelic [WPMonad m Pred EPred] {α : Type u} := wp (mode := .angelic) (m := m) (α := α)

public theorem wp_bind [WPMonad m Pred EPred] {α β : Type u}
    (x : NonDetT mode m α) (f : α → NonDetT mode m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost := by
  induction x generalizing post epost with
  | pure ret => rfl
  | vis c g ih =>
    show Std.WP.wp c (fun b => wp (g b >>= f) post epost) epost =
         Std.WP.wp c (fun b => wp (g b) (fun a => wp (f a) post epost) epost) epost
    congr 1; funext b; exact ih b f post epost
  | pickCont _ p _ g ih =>
    show mode.choice p (fun t => wp (g t >>= f) post epost) =
         mode.choice p (fun t => wp (g t) (fun a => wp (f a) post epost) epost)
    congr 1; funext t; exact ih t f post epost
  | repeatCont init g cont _ ih =>
    change (⨆ (inv : _ → Pred) (stepPost : _ → ForInStep _ → Pred),
      ⌜∀ b, inv b ⊑ wp (g b) (stepPost b) epost⌝ ⊓
      inv init ⊓
      ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
      ⌜∀ b b', stepPost b (.done b') ⊑ wp (cont b' >>= f) post epost⌝) =
      (⨆ (inv : _ → Pred) (stepPost : _ → ForInStep _ → Pred),
      ⌜∀ b, inv b ⊑ wp (g b) (stepPost b) epost⌝ ⊓
      inv init ⊓
      ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
      ⌜∀ b b', stepPost b (.done b') ⊑ wp (cont b') (fun a => wp (f a) post epost) epost⌝)
    congr 1; funext inv; congr 1; funext stepPost
    congr 1; congr 1; congr 1
    congr 1
    simp only [ih]

public theorem wp_monotone [WPMonad m Pred EPred] {α : Type u} (x : NonDetT mode m α) :
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
  | pickCont _ p _ g ih =>
    intro post post' epost epost' hepost hpost
    dsimp [wp]
    apply choice_mono
    intro t
    exact ih t post post' epost epost' hepost hpost
  | repeatCont init g cont g_ih cont_ih =>
    intro post post' epost epost' hepost hpost
    dsimp [wp]
    apply iSup_mono; intro inv
    apply iSup_mono; intro stepPost
    refine meet_mono (meet_mono (meet_mono ?_ PartialOrder.rel_refl) PartialOrder.rel_refl) ?_
    · apply ofProp_mono
      intro h b
      exact PartialOrder.rel_trans (h b) (g_ih b (stepPost b) (stepPost b) epost epost' hepost (fun _ => PartialOrder.rel_refl))
    · apply ofProp_mono
      intro h b b'
      exact PartialOrder.rel_trans (h b b') (cont_ih b' post post' epost epost' hepost hpost)

public noncomputable instance instWPMonadNonDetT [WPMonad m Pred EPred] :
    WPMonad (NonDetT mode m) Pred EPred where
  toWP _ := {
    wpTrans x := ⟨wp x⟩
    wp_trans_monotone x := wp_monotone x
  }
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := by
    show wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost
    rw [wp_bind]

@[simp]
public theorem wp_pickSuchThat [WPMonad m Pred EPred] (τ : Type u) (p : τ → Prop) [FindHint p] (name : Lean.Name)
    (post : τ → Pred) (epost : EPred) :
    Std.WP.wp (NonDetT.pickSuchThat (m := m) (mode := mode) τ p name) post epost =
      mode.choice p post := rfl

@[simp]
public theorem wp_monadNonDet_pickSuchThat [WPMonad m Pred EPred] (τ : Type u) (p : τ → Prop) [FindHint p] (name : Lean.Name)
    (post : τ → Pred) (epost : EPred) :
    Std.WP.wp (MonadNonDet.pickSuchThat (m := NonDetT mode m) τ p name) post epost =
      mode.choice p post := rfl

@[simp]
public theorem wp_pick (τ : Type u) [Inhabited τ] [WPMonad m Pred EPred] (post : τ → Pred) (epost : EPred) :
    Std.WP.wp (NonDetT.pick (m := m) (mode := mode) τ) post epost =
      match mode with
      | .demonic => ⨅ (a : τ), post a
      | .angelic => ⨆ (a : τ), post a := by
  change mode.choice (fun _ => True) post = _
  cases mode
  · apply PartialOrder.rel_antisymm
    · apply le_iInf; intro a; exact iInf_le (i := (⟨a, trivial⟩ : { a : τ // True })) (fun (a : { a : τ // True }) => post a.val)
    · apply le_iInf; intro ⟨a, _⟩; exact iInf_le (i := a) post
  · apply PartialOrder.rel_antisymm
    · apply iSup_le; intro ⟨a, _⟩; exact le_iSup (i := a) post
    · apply iSup_le; intro a; exact le_iSup (i := (⟨a, trivial⟩ : { a : τ // True })) (fun (a : { a : τ // True }) => post a.val)

@[simp]
public theorem wp_monadNonDet_pick (τ : Type u) [Inhabited τ] [WPMonad m Pred EPred] (post : τ → Pred) (epost : EPred) :
    Std.WP.wp (MonadNonDet.pick (m := NonDetT mode m) τ) post epost =
      match mode with
      | .demonic => ⨅ (a : τ), post a
      | .angelic => ⨆ (a : τ), post a :=
  wp_pick τ post epost

@[simp]
public theorem wp_assume [Heyting Pred] [WPMonad m Pred EPred] (as : Prop) [Decidable as] (post : PUnit.{u+1} → Pred) (epost : EPred) :
    Std.WP.wp (NonDetT.«assume» (m := m) (mode := mode) as) post epost =
      match mode with
      | .demonic => ⌜as⌝ ⇨ post .unit
      | .angelic => ⌜as⌝ ⊓ post .unit := by
  change mode.choice (fun _ => as) (fun _ => post .unit) = _
  cases mode
  · apply PartialOrder.rel_antisymm
    · by_cases h : as
      · have h_top : (⌜as⌝ : Pred) = ⊤ := by simp [CompleteLattice.ofProp, h]
        rw [h_top, top_himp]
        exact iInf_le (i := (⟨.unit, h⟩ : { a : PUnit.{u+1} // as })) (fun (a : { a : PUnit.{u+1} // as }) => post a.val)
      · have h_bot : (⌜as⌝ : Pred) = ⊥ := by simp [CompleteLattice.ofProp, h]
        rw [h_bot, bot_himp]
        apply le_top
    · apply le_iInf
      intro ⟨_, ha⟩
      have h_top : (⌜as⌝ : Pred) = ⊤ := by simp [CompleteLattice.ofProp, ha]
      rw [h_top, top_himp]
  · apply PartialOrder.rel_antisymm
    · apply iSup_le
      intro ⟨_, ha⟩
      have h_top : (⌜as⌝ : Pred) = ⊤ := by simp [CompleteLattice.ofProp, ha]
      rw [h_top, top_meet]
    · by_cases h : as
      · have h_top : (⌜as⌝ : Pred) = ⊤ := by simp [CompleteLattice.ofProp, h]
        rw [h_top, top_meet]
        exact le_iSup (i := (⟨.unit, h⟩ : { a : PUnit.{u+1} // as })) (fun (a : { a : PUnit.{u+1} // as }) => post a.val)
      · have h_bot : (⌜as⌝ : Pred) = ⊥ := by simp [CompleteLattice.ofProp, h]
        rw [h_bot, bot_meet]
        apply bot_le

@[simp]
public theorem wp_monadNonDet_assume [Heyting Pred] [WPMonad m Pred EPred] (as : Prop) [Decidable as] (post : PUnit.{u+1} → Pred) (epost : EPred) :
    Std.WP.wp (MonadNonDet.assume (m := NonDetT mode m) as) post epost =
      match mode with
      | .demonic => ⌜as⌝ ⇨ post .unit
      | .angelic => ⌜as⌝ ⊓ post .unit :=
  wp_assume as post epost

/- ============================================================================
   DEMONIC HOARE / VC TRIPLE SPECIFICATIONS
   ============================================================================ -/

@[spec]
public theorem demonic_pickSuchThat_spec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (name : Lean.Name) (τ : Type u) (p : τ → Prop) [hint : FindHint p]
    {post : τ → Pred} {epost : EPred} :
    Triple (MonadNonDet.pickSuchThat (m := DemonicT m) τ p name)
      (⨅ (a : { a : τ // p a }), post a.val) post epost := by
  refine Triple.intro ?_
  rw [wp_monadNonDet_pickSuchThat, choice_demonic]

@[spec]
public theorem demonic_pick_spec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (τ : Type u) [Inhabited τ] {post : τ → Pred} {epost : EPred} :
    Triple (MonadNonDet.pick (m := DemonicT m) τ)
      (⨅ (a : τ), post a) post epost := by
  refine Triple.intro ?_
  rw [wp_monadNonDet_pick]

@[spec]
public theorem demonic_assume_spec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [Heyting Pred] [WPMonad m Pred EPred]
    (as : Prop) [Decidable as] {post : PUnit.{u+1} → Pred} {epost : EPred} :
    Triple (MonadNonDet.assume (m := DemonicT m) as)
      (⌜as⌝ ⇨ post .unit) post epost := by
  refine Triple.intro ?_
  rw [wp_monadNonDet_assume]

/- ============================================================================
   ANGELIC HOARE / VC TRIPLE SPECIFICATIONS
   ============================================================================ -/

@[spec]
public theorem angelic_pickSuchThat_spec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [Heyting Pred] [WPMonad m Pred EPred]
    (name : Lean.Name) (τ : Type u) (p : τ → Prop) [hint : FindHint p]
    (w : τ)
    (h : Named.mk name none (p w))
    {post : τ → Pred} {epost : EPred} :
    Triple (MonadNonDet.pickSuchThat (m := AngelicT m) τ p name)
      ((⌜(Named.mk name none (p w) : Prop)⌝ ⇨ post w) : Pred) post epost := by
  apply Triple.intro
  change (⌜(Named.mk name none (p w) : Prop)⌝ ⇨ post w) ⊑
    Std.WP.wp (NonDetT.pickSuchThat (m := m) (mode := .angelic) τ p name) post epost
  rw [wp_pickSuchThat, choice_angelic]
  have hpw : p w := h
  have hp : (⌜(Named.mk name none (p w) : Prop)⌝ : Pred) = ⊤ := by
    simp [CompleteLattice.ofProp, Named.mk_eq, hpw]
  rw [hp, top_himp]
  exact le_iSup (α := Pred) (i := ⟨w, h⟩) (fun (a : { a : τ // p a }) => post a.val)

@[spec]
public theorem angelic_pick_spec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (τ : Type u) [Inhabited τ] (w : τ) {post : τ → Pred} {epost : EPred} :
    Triple (MonadNonDet.pick (m := AngelicT m) τ)
      (post w) post epost := by
  apply Triple.intro
  rw [wp_monadNonDet_pick]
  exact le_iSup (i := w) post

@[spec]
public theorem angelic_assume_spec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [Heyting Pred] [WPMonad m Pred EPred]
    (as : Prop) [Decidable as] {post : PUnit.{u+1} → Pred} {epost : EPred} :
    Triple (MonadNonDet.assume (m := AngelicT m) as)
      (⌜as⌝ ⊓ post .unit) post epost := by
  refine Triple.intro ?_
  rw [wp_monadNonDet_assume]

@[spec 1250]
public theorem Spec.whileLoop_total
    {mode : NondetMode} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
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
    Triple
      (whileLoopTotal init f inv done measure)
      (inv init)
      (fun b => binderNameHint b done <| done b)
      einv := by
  apply Triple.intro
  dsimp only [whileLoopTotal, forIn, instForInLoopNonDetT, NonDetT.wp, binderNameHint]
  let stepPost : β → ForInStep β → Pred := fun b r => match r with
    | .yield b' =>
        match measure b, measure b' with
        | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
            ⌜Named.mk name stx (next < current)⌝ ⊓ inv b'
    | .done b' => done b'
  refine PartialOrder.rel_trans ?_ (le_iSup (fun inv' => ⨆ (stepPost' : β → ForInStep β → Pred), _) inv)
  refine PartialOrder.rel_trans ?_ (le_iSup (fun stepPost' => _) stepPost)
  change inv init ⊑
    ⌜∀ b, inv b ⊑ (f () b).wp (stepPost b) einv⌝ ⊓ inv init ⊓
    ⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ ⊓
    ⌜∀ b b', stepPost b (.done b') ⊑ done b'⌝
  have h1 : ∀ b, inv b ⊑ (f () b).wp (stepPost b) einv := fun b => (step b).le_wp
  have h3 : ∀ b b', stepPost b (.yield b') ⊑ inv b' := by
    intro b b'
    dsimp [stepPost]
    exact meet_le_right _ _
  have h4 : ∀ b b', stepPost b (.done b') ⊑ done b' := by
    intro b b'
    dsimp [stepPost]
    exact PartialOrder.rel_refl
  have eq1 : (⌜∀ b, inv b ⊑ (f () b).wp (stepPost b) einv⌝ : Pred) = ⊤ := by simp [h1]
  have eq3 : (⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ : Pred) = ⊤ := by simp [h3]
  have eq4 : (⌜∀ b b', stepPost b (.done b') ⊑ done b'⌝ : Pred) = ⊤ := by simp [h4]
  rw [eq1, eq3, eq4]
  refine le_meet _ _ _ (le_meet _ _ _ (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) (le_top _)) (le_top _)

end NonDetT

export NonDetT (
  wp wpDemonic wpAngelic wp_bind wp_monotone
  wp_pickSuchThat wp_monadNonDet_pickSuchThat
  wp_pick wp_monadNonDet_pick
  wp_assume wp_monadNonDet_assume
  demonic_pickSuchThat_spec demonic_pick_spec demonic_assume_spec
  angelic_pickSuchThat_spec angelic_pick_spec angelic_assume_spec
)

end
