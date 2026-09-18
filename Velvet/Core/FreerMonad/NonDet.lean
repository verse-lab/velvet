import Velvet.Core.FreerMonad.WP
import Velvet.Core.NonDet.Soundness

open Std.Internal.Do Std.Internal.Do.CompleteLattice Lean.Order Loop.Gadget WPPartial


universe u v w z

/-! # Non-determinism as a `FreerMonad` effect

`NonDetT` is re-derived here as `FreerMonad (EffSum (BaseEff m) (PickEff mode m))`:

* `BaseEff m` covers `NonDetT.vis`,
* `PickEff mode m` covers `NonDetT.pickCont`,
* `FreerMonad.iter` covers `NonDetT.repeatCont`.

The demonic soundness theorem is then an instance of the generic `FreerMonad.soundness`,
with the single non-trivial obligation discharged by `instLawfulEffWPPickDemonic`. -/

/-- The non-deterministic choice effect: pick a `τ` satisfying `p`.
`m` is a phantom parameter: the *specification* of a failed choice is
`div_pre`, which is determined by the ambient monad. -/
inductive PickEff (mode : NondetMode) (m : Type u → Type v) : Type u → Type u where
  | pick (τ : Type u) (p : τ → Prop) [wf : Findable p] : PickEff mode m τ

/-- Executable reading of a choice: consult the `Findable` witness generator,
and diverge (`CCPOBot.compBot`) when no witness exists. -/
instance instHasInterpreterPick [Monad m] [CCPOBot m] :
    HasInterpreter (PickEff mode m) m where
  interp c := match c with
    | @PickEff.pick _ _ _ _p wf =>
      match wf.find () with
      | none => CCPOBot.compBot
      | some x => Pure.pure x

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable {div_post : EPred} {div_pre : EPred → Pred}

/-- Specification reading of a choice: `NondetMode.choice`, i.e. `⨅` over all
witnesses for `demonic` and `⨆` over all witnesses for `angelic`. This is *not*
the WP of the interpretation above -- that is the whole point. -/
noncomputable instance instEffWPPick [Monad m] [Assertion Pred] [∀ (P : Pred), PreservesSup (meet P)]
    [Assertion EPred] [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
    [WPPartial m Pred EPred div_post div_pre] :
    WP (PickEff mode m α) α Pred EPred where
  wpTrans c := ⟨fun post epost => match c with
    | @PickEff.pick _ _ _ p _ => mode.choice p post (div_pre epost)⟩
  wp_trans_monotone c post post' epost epost' he hp := by
    cases c
    exact choice_mono mode _ hp
      (NonDetT.div_pre_mono (m := m) (div_post := div_post) (div_pre := div_pre) he)

section Sound
variable [Monad m] [CCPOBot m] [∀ γ, CCPO (m γ)] [CCPOBotLawful m]
variable [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
variable [WPPartial m Pred EPred div_post div_pre]

omit [WPPartial m Pred EPred div_post div_pre] in
private theorem wp_compBot_eq_div_pre {α : Type u}
    [WPPartial m Pred EPred div_post div_pre]
    (post : α → Pred) (epost : EPred) :
    wp (CCPOBot.compBot (m := m) (α := α)) post epost = div_pre epost := by
  rw [CCPOBotLawful.bot_eq]
  have hbotEq : (⊥ : m α) =
      CCPO.csup (α := m α) (c := fun _ => False) WPPartial.emptyChain := by
    apply PartialOrder.rel_antisymm
    · exact bot_le _
    · apply csup_le
      intro y hy
      contradiction
  rw [hbotEq, WPPartial.wp_bot (div_post := div_post) (div_pre := div_pre)]

/-- **The one genuinely non-trivial obligation.** Resolving a demonic choice to the
single `Findable` witness refines the `⨅`-over-all-witnesses specification, and an
empty choice refines the `div_pre` fallback.

There is deliberately no angelic counterpart: `⨆` over witnesses is *not* refined by
the particular witness `find ()` returns. -/
instance instLawfulEffWPPickDemonic [∀ (P : Pred), PreservesSup (meet P)] :
    LawfulEffWP (PickEff .demonic m) m Pred EPred where
  ewp_le_wp_interp c post epost := by
    match c with
    | @PickEff.pick _ _ _ p wf =>
      rw [WP.wpTrans, instEffWPPick]
      simp only [le_iff_forall_le_1, interp]
      intro post1 epost1
      rw [choice_demonic]
      split
      · rename_i hfind
        have hexists : ¬∃ x, p x := by
          have := Findable.find_none (p := p) (by simpa using hfind)
          simpa using this
        have heq : (⌜¬ ∃ x, p x⌝ : Pred) = ⊤ := by simp [hexists]
        rw [wp_compBot_eq_div_pre (div_post := div_post) (div_pre := div_pre), heq, top_himp]
        exact meet_le_left _ _
      · rename_i x hx
        have hp : p x := Findable.find_some_p hx
        apply PartialOrder.rel_trans (meet_le_right _ _)
        exact PartialOrder.rel_trans
          (iInf_le (i := (⟨x, hp⟩ : {a // p a})) (fun a => post1 a.val))
          (WPMonad.pure_le_wp_pure x post1 epost1)

end Sound

/-- The full non-determinism signature: base effects plus choice. -/
abbrev NonDetEff (mode : NondetMode) (m : Type u → Type v) :=
  EffSum (BaseEff m) (PickEff mode m)

/-- `NonDetT`, re-derived as a `FreerMonad` over `NonDetEff`. -/
abbrev NonDetF (mode : NondetMode) (m : Type u → Type v) :=
  FreerMonad (NonDetEff mode m)

abbrev DemonicF (m : Type u → Type v) := NonDetF .demonic m

noncomputable instance instWPMonadNonDetF [Monad m] [∀ γ, CCPO (m γ)]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ (P : Pred), PreservesSup (meet P)]
    [WPPartial m Pred EPred div_post div_pre] :
    WPMonad (NonDetF mode m) Pred EPred :=
  FreerMonad.wpMonadInst (m := m) (div_post := div_post) (div_pre := div_pre)

instance : MonadLift m (NonDetF mode m) where
  monadLift x := .vis (.inl (.mk x)) .ret

/-- Pick a value of `τ` satisfying `p`. -/
def NonDetF.pickSuchThat (τ : Type u) (p : τ → Prop) [wf : Findable p]
    (_name : Lean.Name := .anonymous) : NonDetF mode m τ :=
  .vis (.inr (PickEff.pick τ p)) .ret

/-- Assume a proposition. -/
def NonDetF.assume' (as : Prop) [Decidable as] : NonDetF mode m PUnit.{u+1} :=
  .vis (.inr (PickEff.pick PUnit.{u+1} (fun _ => as))) .ret

section Specs
variable [Monad m] [CCPOBot m] [∀ γ, CCPO (m γ)] [MonoBind m] [CCPOBotLawful m]
variable [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ (P : Pred), PreservesSup (meet P)]
variable [WPPartial m Pred EPred div_post div_pre]

omit [CCPOBot m] [MonoBind m] [CCPOBotLawful m] in
/-- The choice rule is definitionally the same as `NonDetT.wp_pickSuchThat`. -/
@[simp]
theorem NonDetF.wp_pickSuchThat (τ : Type u) (p : τ → Prop) [wf : Findable p]
    (name : Lean.Name) (post : τ → Pred) (epost : EPred) :
    FreerMonad.wp (m := m) (NonDetF.pickSuchThat (mode := mode) (m := m) τ p name) post epost =
      mode.choice p post (div_pre epost) := rfl

/-- **Payoff.** Demonic soundness for the Freer encoding is the generic
`FreerMonad.soundness`; no separate induction over the non-determinism syntax. -/
theorem NonDetF.demonic_soundness {α : Type u} (c : DemonicF m α)
    (post : α → Pred) (epost : EPred) :
    FreerMonad.wp (m := m) c post epost ⊑ wp c.interp post epost :=
  FreerMonad.soundness (div_post := div_post) (div_pre := div_pre) c

/-- ... and the triple-level corollary, matching `ExtractNonDet.extract_refines`. -/
theorem NonDetF.demonic_refines {α : Type u} {pre : Pred} {s : DemonicF m α}
    {post : α → Pred} {epost : EPred} :
    Triple s pre post epost → Triple s.interp pre post epost :=
  fun tr => Triple.intro (PartialOrder.rel_trans tr.le_wp
    (NonDetF.demonic_soundness (div_post := div_post) (div_pre := div_pre) s post epost))

end Specs

/-! ## Bridge: the existing `NonDetT` syntax embeds, preserving WP on the nose -/

/-- Structural translation of the hand-rolled `NonDetT` syntax into the Freer encoding. -/
def NonDetT.toFreer {mode : NondetMode} {m : Type u → Type v} :
    {α : Type u} → NonDetT mode m α → NonDetF mode m α
  | _, .pure x => .ret x
  | _, .vis x f => .vis (.inl (.mk x)) (fun b => (f b).toFreer)
  | _, @NonDetT.pickCont _ _ _ τ p wf f =>
      .vis (.inr (PickEff.pick (wf := wf) τ p)) (fun t => (f t).toFreer)
  | _, .repeatCont init f cont =>
      .iter init (fun b => (f b).toFreer) (fun b => (cont b).toFreer)

section Bridge
variable [Monad m] [CCPOBot m] [∀ γ, CCPO (m γ)]
variable [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ (P : Pred), PreservesSup (meet P)]
variable [WPPartial m Pred EPred div_post div_pre]

omit [CCPOBot m] in
/-- **The two weakest-precondition definitions are literally the same function.** -/
theorem NonDetT.wp_toFreer {α : Type u} (x : NonDetT mode m α)
    (post : α → Pred) (epost : EPred) :
    FreerMonad.wp (m := m) (div_post := div_post) (div_pre := div_pre) x.toFreer post epost
      = NonDetT.wp (div_post := div_post) (div_pre := div_pre) x post epost := by
  induction x with
  | pure x => rfl
  | vis c f ih =>
      show Std.Internal.Do.wp c (fun b => FreerMonad.wp (f b).toFreer post epost) epost = _
      simp only [ih]
      rfl
  | pickCont τ p f ih =>
      show mode.choice p (fun t => FreerMonad.wp (f t).toFreer post epost) (div_pre epost) = _
      simp only [ih]
      rfl
  | repeatCont init f cont f_ih cont_ih =>
      dsimp only [NonDetT.toFreer, FreerMonad.wp, NonDetT.wp]
      simp only [f_ih, cont_ih]
      rfl

end Bridge
