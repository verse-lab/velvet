module

public import Velvet.Core.Loop.Gadgets

/-!
# Loop specifications

The specifications `velvet_vcgen` applies to Velvet's loop gadgets (`Gadgets.lean`) and to Lean's
own `for` loops.

A loop's `.done` exits (`break`, `return`, and a `while` condition turning false) either go
straight to the code after the loop, or, with `done_with`, establish the `done_with` condition,
which the code after the loop then starts from. A `return` always goes straight to the code after
the loop, which returns the value.

## How the specs are written

- A spec without `done_with` ends in a postcondition `Q` that `vcgen` fills in with what the code
  after the loop needs, as for `Spec.pure`. Its exits go to `Q`, so the code after the loop is
  verified once per exit.
- Each kind of loop has one core rule over `forIn` (`whileLoopPartial_core`,
  `whileLoopTotal_core`, `Spec.forIn'_list_state_inv`, `Spec.forIn'_list_inv_done`). Each `@[spec]`
  theorem instantiates one for its gadget: it picks where exits go (`Q`, `done`, or `onExit Q
  done`) and, for a body that can `return`, the invariant `noReturn inv`.
- What one iteration establishes is written with the reducible definitions below (`stepPost`,
  `stepPostDecreasing`, `noReturn`, `onExit`), not with inline `match`es: each inline `match`
  compiles to its own matcher, and `vcgen` cannot unify the matchers of different theorems. Sym
  unfolds reducible definitions when it loads a spec, and `vcgen` reduces the `match` once the
  body's `ForInStep` is known, so the VCs state `inv i'` or `Q i` directly.
- Each `@[spec]` theorem's docstring names its gadget, whose docstring shows the loop it comes
  from.
- Facts about the cursor are wrapped in `Named.mk` (`h_mem`, `h_prefix`, `h_last`, `h_empty`,
  `h_nonempty`), so they become hypotheses with those names.

## Naming variables with `binderNameHint`

`binderNameHint v binder e` is `e`. When `vcgen` introduces the variable `v`, it names it after
`binder`'s first lambda, or after the names of the pattern its `match` uses, as long as that name
is one the user wrote (not `__pref` or a macro-generated name). Without a hint, the variable
appears in the VCs as `b✝`. Every premise that introduces a variable the user sees gets one:

- the loop state, after the invariant: `binderNameHint b inv <| inv b` names `b` after
  `fun i => …`, or a tuple state after `fun (i, s) => …`;
- the current element, after the body: `binderNameHint cur f` names it after `fun x h_mem s => …`;
- the state at an exit: `binderNameHint s done (done s)`;
- the visited and remaining elements, which have no lambda in the user's code: the binder is
  written for the purpose, as in `fun rest : List α => (rest, `rest)`. The name also appears in
  the body: terms are shared up to binder names, which would merge the hints for `pref` and
  `rest`, and a body like `f rest` would be eta-reduced away from its binder.
-/
open Std.Internal
open Std.WP
open Std.WP.Assertion
open Lean.Order
open WPPartial

universe u u₁ u₂ v w

namespace Loop

open Gadget

/-! ## Fixed-point loop rules -/

/-- Generic partial-correctness rule for `forIn.loop` over any monad satisfying `WPPartial`. -/
public theorem forInLoop_partial
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    (f : Unit → β → m (ForInStep β)) (init : β)
    (inv : β ⊕ β → Pred) (einv : EPred)
    (hdiv : ∀ b, inv (.inl b) ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (inv (.inl b))
      (fun r => match r with
        | .yield b' => inv (.inl b')
        | .done b' => inv (.inr b')) einv) :
    Triple (forIn.loop f init) (inv (.inl init))
      (fun b => inv (.inr b)) einv := by
  let post : β → Pred := fun b => inv (.inr b)
  let motive : (β → m β) → Prop := fun loop => ∀ init, inv (.inl init) ⊑ wp (loop init) post einv
  have hadm : admissible motive := by
    dsimp [motive]
    apply admissible_pi_apply (P := fun init (x : m β) => inv (.inl init) ⊑ wp x post einv)
    intro init
    exact admissible_triple_wp (inv (.inl init)) post einv (hdiv init)
  refine ⟨forIn.loop.fixpoint_induct (f := f) (motive := motive) hadm ?_ init⟩
  intro loop ih b
  have h1 := (step b).le_wp
  let k : ForInStep β → m β := fun r => match r with
    | .done val => pure val
    | .yield val => loop val
  have hk : (fun r => match r with
      | .yield b' => inv (.inl b')
      | .done b' => inv (.inr b')) ⊑ (fun r => wp (k r) post einv) := by
    intro r
    cases r with
    | done val =>
      dsimp [k]
      exact WPMonad.pure_le_wp_pure val post einv
    | yield val =>
      dsimp [k]
      exact ih val
  have h2 : wp (f () b) (fun r => match r with
      | .yield b' => inv (.inl b')
      | .done b' => inv (.inr b')) einv ⊑ wp (f () b) (fun r => wp (k r) post einv) einv := by
    apply WP.wp_consequence (f () b) _ _ einv hk
  have h3 : wp (f () b) (fun r => wp (k r) post einv) einv ⊑ wp (f () b >>= k) post einv := by
    exact WPMonad.bind_le_wp_bind (f () b) k post einv
  exact PartialOrder.rel_trans h1 (PartialOrder.rel_trans h2 h3)

/-- Total-correctness rule for the least-fixed-point loop, justified by a
strictly decreasing natural-number measure. -/
public theorem forInLoop_total
    {m : Type u → Type v} {Pred : Type u₁} {EPred : Type u₂}
    [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} (f : Unit → β → m (ForInStep β)) (init : β)
    (inv : ForInStep β → Pred) (measure : β → Nat) (einv : EPred)
    (step : ∀ b,
      Triple (f () b) (inv (.yield b))
        (fun r => match r with
          | .yield b' => inv (.yield b') ⊓ ⌜measure b' < measure b⌝
          | .done b' => inv (.done b')) einv) :
    Triple (Loop.forIn.loop f init) (inv (.yield init))
      (fun b => inv (.done b)) einv := by
  have measure_induction (C : β → Prop) (a : β)
      (h : ∀ x, (∀ y, measure y < measure x → C y) → C x) : C a := by
    have aux : ∀ n : Nat, ∀ x, measure x ≤ n → C x := by
      intro n
      induction n with
      | zero =>
        intro x hx
        exact h x (fun y hy => by omega)
      | succ n ih =>
        intro x hx
        by_cases hle : measure x ≤ n
        · exact ih x hle
        · exact h x (fun y hy => ih y (by omega))
    exact aux (measure a) a (by omega)
  apply measure_induction
    (fun b => Triple (Loop.forIn.loop f b) (inv (.yield b))
      (fun b => inv (.done b)) einv) init
  intro b ih
  rw [Loop.forIn.loop.eq_def]
  apply Triple.bind (mid := fun r => match r with
    | .yield b' => inv (.yield b') ⊓ ⌜measure b' < measure b⌝
    | .done b' => inv (.done b'))
  · exact step b
  · intro r
    cases r with
    | done b' => exact Triple.pure b' PartialOrder.rel_refl
    | yield b' =>
      apply Triple.intro
      change inv (.yield b') ⊓ ⌜measure b' < measure b⌝ ⊑
        wp (Loop.forIn.loop f b') (fun b => inv (.done b)) einv
      rw [meet_comm]
      apply ofProp_meet_le_left
      intro hlt
      exact (ih b' hlt).le_wp


/-! ## What one iteration establishes -/

section StepPost
variable {β : Type u} {Pred : Type u₁} [Assertion Pred]

/-- `stepPost inv Q (.yield i')` is `inv i'`, and `stepPost inv Q (.done i)` is `Q i`. -/
@[expose, reducible] public def stepPost (next exit : β → Pred) : ForInStep β → Pred
  | .yield b' => next b'
  | .done b' => exit b'

/-- `stepPost` that also decreases the measure: `.yield i'` gives
`⌜⟪termination : n - i' < n - i⟫⌝ ⊓ inv i'`. -/
@[expose, reducible] public noncomputable def stepPostDecreasing (inv : β → Pred)
    (measure : β → Named.Measure) (exit : β → Pred) (b : β) : ForInStep β → Pred :=
  stepPost (fun b' => match measure b, measure b' with
    | ⟨name, stx, current⟩, ⟨_, _, next⟩ => ⌜Named.mk name stx (next < current)⌝ ⊓ inv b') exit

/-- `noReturn inv (none, s)` is `inv s`, and `noReturn inv (some r, s)` is `⊥`. -/
@[expose, reducible] public noncomputable def noReturn {γ τ : Type u} (inv : τ → Pred) :
    Option γ × τ → Pred
  | (none, s) => inv s
  | (some _, _) => ⊥

/-- `onExit Q done (some r, s)` is `Q (some r, s)`, and `onExit Q done (none, s)` is `done s`. -/
@[expose, reducible] public def onExit {γ τ : Type u} (Q : Option γ × τ → Pred) (done : τ → Pred) :
    Option γ × τ → Pred
  | (some r, s) => Q (some r, s)
  | (none, s) => done s

end StepPost

/-! ## Postconditions -/

/-- Weaken a triple's postcondition. -/
public theorem triple_post_le {m : Type u → Type v} {Pred : Type u₁} {EPred : Type u₂}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type u} {x : m α} {P : Pred} {Q Q' : α → Pred} {epost : EPred}
    (h : Triple x P Q epost) (hQ : ∀ a, Q a ⊑ Q' a) : Triple x P Q' epost :=
  ⟨PartialOrder.rel_trans h.le_wp (WP.wp_consequence x Q Q' epost hQ)⟩

/-- A loop that ends in `onExit Q done` ends in `Q`, once `done` leads to `Q`. -/
public theorem triple_onExit {m : Type u → Type v} {Pred : Type u₁} {EPred : Type u₂}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {γ τ : Type u} {x : m (Option γ × τ)} {P : Pred} {Q : Option γ × τ → Pred} {done : τ → Pred}
    {epost : EPred}
    (h : Triple x P (onExit Q done) epost) (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple x P Q epost :=
  triple_post_le h fun b => by
    rcases b with ⟨_ | r, s⟩
    · exact hD s
    · exact PartialOrder.rel_refl

/-- A loop step proved for every state whose return slot is empty covers every state, since
`noReturn` holds of no other. -/
public theorem noReturn_step {m : Type u → Type v} {Pred : Type u₁} {EPred : Type u₂}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {γ τ α : Type u} {inv : τ → Pred} {x : Option γ × τ → m α}
    {post : Option γ × τ → α → Pred} {epost : EPred}
    (h : ∀ s, Triple (x (none, s)) (inv s) (post (none, s)) epost) :
    ∀ b, Triple (x b) (noReturn inv b) (post b) epost
  | (none, s) => h s
  | (some _, _) => ⟨bot_le _⟩

/-- `noReturn inv` entails what every state with an empty return slot entails. -/
public theorem noReturn_le {Pred : Type u₁} [Assertion Pred] {γ τ : Type u}
    {inv : τ → Pred} {X : Pred} (h : ∀ s, inv s ⊑ X) :
    ∀ b : Option γ × τ, noReturn inv b ⊑ X
  | (none, s) => h s
  | (some _, _) => bot_le _

/-- `noReturn inv` entails `Q` wherever every state with an empty return slot does. -/
public theorem noReturn_le_fun {Pred : Type u₁} [Assertion Pred] {γ τ : Type u}
    {inv : τ → Pred} {Q : Option γ × τ → Pred} (h : ∀ s, inv s ⊑ Q (none, s)) :
    ∀ b, noReturn inv b ⊑ Q b
  | (none, s) => h s
  | (some _, _) => bot_le _

/-- Weaken a triple's precondition. -/
public theorem triple_pre_le {m : Type u → Type v} {Pred : Type u₁} {EPred : Type u₂}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type u} {x : m α} {P P' : Pred} {Q : α → Pred} {epost : EPred}
    (hP : P' ⊑ P) (h : Triple x P Q epost) : Triple x P' Q epost :=
  ⟨PartialOrder.rel_trans hP h.le_wp⟩

/-- An implication from a true proposition gives its conclusion. -/
public theorem himp_of_true_le {Pred : Type u₁} [Assertion Pred]
    [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)] {p : Prop} (hp : p) (X : Pred) :
    (⌜p⌝ ⇨ X) ⊑ X := by
  have h_meet : (⌜p⌝ ⊓ (⌜p⌝ ⇨ X)) ⊑ X := meet_himp_le
  have h_top : (⌜p⌝ : Pred) = ⊤ := by simp [hp]
  rw [h_top] at h_meet ⊢
  rw [top_meet] at h_meet
  exact h_meet

/-! ## `while` loops -/

/-- Partial-correctness rule for a `while` loop: every iteration re-establishes `inv`, and every
exit establishes `exit`. -/
public theorem whileLoopPartial_core
    {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β} {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (inv exit : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv exit) einv) :
    Triple (forIn PartialLoop.mk init f) (inv init) exit einv := by
  let inv' : β ⊕ β → Pred := fun
    | .inl b => inv b
    | .inr b => exit b
  exact forInLoop_partial f init inv' einv hdiv fun b =>
    triple_post_le (step b) fun r => by cases r <;> exact PartialOrder.rel_refl

/-- Total-correctness rule for a `while` loop: every iteration re-establishes `inv` and decreases
`measure`, and every exit establishes `exit`. -/
public theorem whileLoopTotal_core
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {init : β} {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (inv exit : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure exit b) einv) :
    Triple (forIn Lean.Loop.mk init f) (inv init) exit einv := by
  have step₀ : ∀ b, Triple (f () b) (inv b)
      (fun r => match r with
        | .yield b' =>
            match measure b, measure b' with
            | ⟨name, stx, current⟩, ⟨_, _, next⟩ => ⌜Named.mk name stx (next < current)⌝ ⊓ inv b'
        | .done b' => exit b') einv :=
    fun b => triple_post_le (step b) fun r => by cases r <;> exact PartialOrder.rel_refl
  let inv' : WhileInvariant β Pred := WhileInvariant.mk fun
    | false, b => inv b
    | true, b => exit b
  let loopMeasure := Variant.ofMeasure (Pred := Pred)
    (fun b => (measure b).value)
  have step' : ∀ b (mb : loopMeasure.γ),
      Triple (f () b)
        (loopMeasure.EvalsTo b mb ⊓ inv' false b)
        (fun r => match r with
          | .yield b' => loopMeasure.EvalsBelow b' mb ⊓ inv' false b'
          | .done b' => inv' true b')
        einv := by
    intro b mb
    apply Triple.intro
    apply ofProp_meet_le_left
    intro h
    subst mb
    have natRel (a b : Nat) : WellFoundedRelation.rel a b = (a < b) := rfl
    simpa [Named.mk_eq, loopMeasure, inv', WhileInvariant.mk_apply,
      Variant.evalsBelow_ofMeasure, natRel] using (step₀ b).le_wp
  exact Spec.forIn_loop (l := Lean.Loop.mk) (init := init) loopMeasure inv' einv step'

/-- The spec for `Gadget.whileLoopPartial` without `done_with`: every exit goes straight to the code
after the loop. -/
@[spec 1200]
public theorem Spec.whileLoopPartial
    {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β} {f : Unit → β → m (ForInStep β)} {einv : EPred} {Q : β → Pred}
    (inv : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv Q) einv) :
    Triple (Gadget.whileLoopPartial init f inv none) (inv init) Q einv :=
  whileLoopPartial_core inv Q hdiv step

/-- The spec for `Gadget.whileLoopPartial` with `done_with`: every exit establishes `done`, which the
code after the loop starts from. -/
@[spec 1200]
public theorem Spec.whileLoopPartialAndDone
    {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β} {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv done) einv) :
    Triple (Gadget.whileLoopPartial init f inv (some done)) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  whileLoopPartial_core inv done hdiv step

/-- The spec for `Gadget.whileLoopPartialReturning` with `done_with`: a `return` goes straight to the
code after the loop, and every other exit establishes `done`. -/
@[spec 1200]
public theorem Spec.whileLoopPartialAndDoneReturning
    {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    {γ τ : Type u} {init : Option γ × τ} {f : Unit → Option γ × τ → m (ForInStep (Option γ × τ))}
    {einv : EPred} {Q : Option γ × τ → Pred}
    (inv done : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) (onExit Q done)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (Gadget.whileLoopPartialReturning init f inv (some done)) (noReturn inv init) Q einv :=
  triple_onExit (whileLoopPartial_core (noReturn inv) _ (noReturn_le hdiv)
    (noReturn_step (inv := inv) (x := f ()) (post := fun _ => stepPost (noReturn inv) (onExit Q done))
      step)) hD

/-- The spec for `Gadget.whileLoopPartialReturning` without `done_with`: every exit goes straight to
the code after the loop. -/
@[spec 1200]
public theorem Spec.whileLoopPartialReturning
    {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    {γ τ : Type u} {init : Option γ × τ} {f : Unit → Option γ × τ → m (ForInStep (Option γ × τ))}
    {einv : EPred} {Q : Option γ × τ → Pred}
    (inv : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) Q) einv) :
    Triple (Gadget.whileLoopPartialReturning init f inv none) (noReturn inv init) Q einv :=
  whileLoopPartial_core (noReturn inv) Q (noReturn_le hdiv)
    (noReturn_step (inv := inv) (x := f ()) (post := fun _ => stepPost (noReturn inv) Q) step)

/-- The spec for `Gadget.whileLoopTotal` without `done_with`: every exit goes straight to the code
after the loop. -/
@[spec 1200]
public theorem Spec.whileLoopTotal
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {init : β} {f : Unit → β → m (ForInStep β)} {einv : EPred} {Q : β → Pred}
    (inv : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure Q b) einv) :
    Triple (Gadget.whileLoopTotal init f inv none measure) (inv init) Q einv :=
  whileLoopTotal_core inv Q measure step

/-- The spec for `Gadget.whileLoopTotal` with `done_with`: every exit establishes `done`, which the
code after the loop starts from. -/
@[spec 1200]
public theorem Spec.whileLoopTotalAndDone
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {init : β} {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure done b) einv) :
    Triple (Gadget.whileLoopTotal init f inv (some done) measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  whileLoopTotal_core inv done measure step

/-- The spec for `Gadget.whileLoopTotalReturning` with `done_with`: a `return` goes straight to the
code after the loop, and every other exit establishes `done`. -/
@[spec 1200]
public theorem Spec.whileLoopTotalAndDoneReturning
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {γ τ : Type u} {init : Option γ × τ} {f : Unit → Option γ × τ → m (ForInStep (Option γ × τ))}
    {einv : EPred} {Q : Option γ × τ → Pred}
    (inv done : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) (none, s)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (Gadget.whileLoopTotalReturning init f inv (some done) measure) (noReturn inv init) Q einv :=
  triple_onExit (whileLoopTotal_core (noReturn inv) _ (fun b => measure b.2)
    (noReturn_step (inv := inv) (x := f ())
      (post := fun b => stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) b) step)) hD

/-- The spec for `Gadget.whileLoopTotalReturning` without `done_with`: every exit goes straight to
the code after the loop. -/
@[spec 1200]
public theorem Spec.whileLoopTotalReturning
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {γ τ : Type u} {init : Option γ × τ} {f : Unit → Option γ × τ → m (ForInStep (Option γ × τ))}
    {einv : EPred} {Q : Option γ × τ → Pred}
    (inv : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q (none, s)) einv) :
    Triple (Gadget.whileLoopTotalReturning init f inv none measure) (noReturn inv init) Q einv :=
  whileLoopTotal_core (noReturn inv) Q (fun b => measure b.2)
    (noReturn_step (inv := inv) (x := f ())
      (post := fun b => stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q b) step)

/-! ## `for` loops with a state invariant -/

/-- A `for` loop over a list whose invariant only mentions the loop state: every exit goes
straight to `exit`, and so does running out of elements, from `inv`. -/
public theorem Spec.forIn'_list_state_inv
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv exit : β → Pred)
    {epost : EPred}
    (step : ∀ cur (h : cur ∈ xs) b,
      Triple (f cur h b) (binderNameHint cur f <| binderNameHint b inv <| inv b)
        (stepPost inv exit) epost)
    (hEnd : ∀ b, inv b ⊑ exit b) :
    Triple (forIn' xs init f) (inv init) exit epost := by
  let inv' : Invariant α β Pred := fun _ suff b =>
    match suff with
    | [] => exit b
    | _ :: _ => inv b
  have h := Spec.forIn'_list (init := init) inv' fun pref cur suff h b =>
    triple_post_le (step cur (by simp [h]) b) fun r => by
      cases r with
      | yield b' =>
        cases suff with
        | nil => exact hEnd b'
        | cons => exact PartialOrder.rel_refl
      | done b' => exact PartialOrder.rel_refl
  cases xs with
  | nil => exact ⟨PartialOrder.rel_trans (hEnd init) h.le_wp⟩
  | cons => exact h

set_option linter.unusedVariables false in
/-- The spec for `Gadget.forLoopWithInvariant`: every exit goes straight to the code after the loop,
and so does running out of elements, from the invariant. -/
@[spec]
public theorem Spec.forLoopWithInvariant
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)} {Q : β → Pred}
    (inv : β → Pred)
    {epost : EPred}
    (step : ∀ cur (h : Named.mk `h_mem none (cur ∈ ForIn.toList xs)) b,
      Triple (f cur ((LawfulMemForInId.mem_toList_iff).mp h) b)
        (binderNameHint cur f <| binderNameHint b inv <| inv b)
        (stepPost inv Q) epost)
    (hEnd : ∀ b, binderNameHint b inv (inv b) ⊑ Q b) :
    Triple (forLoopWithInvariant xs init f inv) (inv init) Q epost := by
  unfold Gadget.forLoopWithInvariant
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list_state_inv (init := init) inv Q step hEnd

/-- The spec for `Gadget.forLoopWithInvariantReturning`: every exit goes straight to the code after
the loop, and so does running out of elements, from the invariant. -/
@[spec]
public theorem Spec.forLoopWithInvariantReturning
    {α : Type u₁} {γ τ : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : Option γ × τ} {f : (a : α) → a ∈ xs → Option γ × τ → m (ForInStep (Option γ × τ))}
    {Q : Option γ × τ → Pred}
    (inv : τ → Pred)
    {epost : EPred}
    (step : ∀ cur (h : Named.mk `h_mem none (cur ∈ ForIn.toList xs)) s,
      Triple (f cur ((LawfulMemForInId.mem_toList_iff).mp h) (none, s))
        (binderNameHint cur f <| binderNameHint s inv <| inv s)
        (stepPost (noReturn inv) Q) epost)
    (hEnd : ∀ s, binderNameHint s inv (inv s) ⊑ Q (none, s)) :
    Triple (forLoopWithInvariantReturning xs init f inv) (noReturn inv init) Q epost := by
  have h := Spec.forLoopWithInvariant (xs := xs) (init := init) (f := f) (noReturn inv)
    (fun cur hc => noReturn_step (inv := inv) (x := fun b => f cur ((LawfulMemForInId.mem_toList_iff).mp hc) b)
      (post := fun _ => stepPost (noReturn inv) Q) (step cur hc))
    (noReturn_le_fun hEnd)
  unfold Gadget.forLoopWithInvariant at h
  unfold Gadget.forLoopWithInvariantReturning
  exact h

/-- Lean's own `for` loop, which carries no invariant: every exit, and finishing the last element,
goes straight to the code after the loop, as does an empty collection. -/
@[spec high]
public theorem Spec.forInTop
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α] [PureForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)} {Q : β → Pred}
    {epost : EPred}
    (step : ∀ pref cur suff (_h : Named.mk `h_prefix none (ForIn.toList xs = pref ++ cur :: suff)) b,
      Triple (f cur b) (binderNameHint pref (fun pref : List α => (pref, `pref)) <| binderNameHint cur f <|
          binderNameHint suff (fun rest : List α => (rest, `rest)) ⊤) (stepPost (fun b' => ⌜Named.mk `h_last none (suff = [])⌝ ⇨ Q b') Q) epost) :
    Triple (forIn xs init f) (⌜Named.mk `h_empty none (ForIn.toList xs = [])⌝ ⇨ Q init) Q epost := by
  rw [PureForIn.forIn_eq]
  let inv : Invariant α β Pred := fun _ suff b =>
    match suff with
    | [] => Q b
    | _ :: _ => ⊤
  have h := Spec.forIn_list (init := init) inv fun pref cur suff h b =>
    triple_post_le (step pref cur suff h b) fun r => by
      cases r with
      | yield b' =>
        cases suff with
        | nil => exact himp_of_true_le rfl _
        | cons => exact le_top _
      | done b' => exact PartialOrder.rel_refl
  refine triple_pre_le ?_ h
  cases ForIn.toList xs with
  | nil => exact himp_of_true_le rfl _
  | cons => exact le_top _

/-- `Spec.forInTop` for Lean's own `for h : x in xs` loop. -/
@[spec high]
public theorem Spec.forIn'Top
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)} {Q : β → Pred}
    {epost : EPred}
    (step : ∀ pref cur suff (h : Named.mk `h_prefix none (ForIn.toList xs = pref ++ cur :: suff)) b,
      Triple (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at h; simp [h])) b) (binderNameHint pref (fun pref : List α => (pref, `pref)) <| binderNameHint cur f <|
          binderNameHint suff (fun rest : List α => (rest, `rest)) ⊤)
        (stepPost (fun b' => ⌜Named.mk `h_last none (suff = [])⌝ ⇨ Q b') Q) epost) :
    Triple (forIn' xs init f) (⌜Named.mk `h_empty none (ForIn.toList xs = [])⌝ ⇨ Q init) Q epost := by
  rw [PureForIn'.forIn'_eq]
  let inv : Invariant α β Pred := fun _ suff b =>
    match suff with
    | [] => Q b
    | _ :: _ => ⊤
  have h := Spec.forIn'_list (init := init)
    (f := fun a h b => f a ((LawfulMemForInId.mem_toList_iff).mp h) b) inv
    fun pref cur suff h b =>
      triple_post_le (step pref cur suff h b) fun r => by
        cases r with
        | yield b' =>
          cases suff with
          | nil => exact himp_of_true_le rfl _
          | cons => exact le_top _
        | done b' => exact PartialOrder.rel_refl
  refine triple_pre_le ?_ h
  cases ForIn.toList xs with
  | nil => exact himp_of_true_le rfl _
  | cons => exact le_top _

/-! ## `for` loops with `done_with` -/

public theorem Spec.forIn_init_le
    {α : Type u₁} {β : Type (max u₁ u₂)}
    {Pred : Type (max u₁ u₂)} [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    (xs : List α) (init : β)
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred) :
    ((⌜xs = []⌝ ⇨ done [] init) ⊓ (⨅ cur, ⨅ rest, ⌜xs = cur :: rest⌝ ⇨ inv [] cur rest init)) ⊑
      (match xs with | [] => done [] init | cur :: rest => inv [] cur rest init) := by
  cases xs with
  | nil =>
    have h1 := meet_le_left (⌜([] : List α) = []⌝ ⇨ done [] init)
      (⨅ (cur : α), ⨅ (rest : List α), ⌜([] : List α) = cur :: rest⌝ ⇨ inv [] cur rest init)
    have h2 : (⌜([] : List α) = []⌝ ⇨ done [] init) ⊑ done [] init := by
      have h_meet : (⌜([] : List α) = []⌝ ⊓ (⌜([] : List α) = []⌝ ⇨ done [] init)) ⊑ done [] init := meet_himp_le
      have h_top : ⌜([] : List α) = []⌝ = (⊤ : Pred) := by simp
      rw [h_top]
      rw [h_top, top_meet] at h_meet
      exact h_meet
    exact PartialOrder.rel_trans h1 h2
  | cons head tail =>
    have h1 := meet_le_right (⌜head :: tail = []⌝ ⇨ done [] init)
      (⨅ (cur : α), ⨅ (rest : List α), ⌜head :: tail = cur :: rest⌝ ⇨ inv [] cur rest init)
    have h2 := iInf_le (i := head) (fun cur => ⨅ (rest : List α), ⌜head :: tail = cur :: rest⌝ ⇨ inv [] cur rest init)
    have h3 := iInf_le (i := tail) (fun rest => ⌜head :: tail = head :: rest⌝ ⇨ inv [] head rest init)
    have h4 : (⌜head :: tail = head :: tail⌝ ⇨ inv [] head tail init) ⊑ inv [] head tail init := by
      have h_meet : (⌜head :: tail = head :: tail⌝ ⊓ (⌜head :: tail = head :: tail⌝ ⇨ inv [] head tail init)) ⊑ inv [] head tail init := meet_himp_le
      have h_top : ⌜head :: tail = head :: tail⌝ = (⊤ : Pred) := by simp
      rw [h_top]
      rw [h_top, top_meet] at h_meet
      exact h_meet
    exact PartialOrder.rel_trans (PartialOrder.rel_trans (PartialOrder.rel_trans h1 h2) h3) h4


/-- A `for` loop over a list with a cursor-dependent invariant and an exit condition `done`: every
exit establishes `done`, and so does finishing the last element. -/
public theorem Spec.forIn'_list_inv_done
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred)
    {epost : EPred}
    (step_mid : ∀ pref cur next rest (h : xs = pref ++ cur :: next :: rest) b,
      Triple
        (f cur (by simp [h]) b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur (next :: rest)) <|
          inv pref cur (next :: rest) b)
        (stepPost (inv (pref ++ [cur]) next rest) (done xs))
        epost)
    (step_last : ∀ pref cur (h : xs = pref ++ [cur]) b,
      Triple
        (f cur (by simp [h]) b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur []) <|
          inv pref cur [] b)
        (stepPost (done xs) (done xs))
        epost) :
    Triple
      (forIn' xs init f)
      ((⌜xs = []⌝ ⇨ done [] init) ⊓ (⨅ cur, ⨅ rest, ⌜xs = cur :: rest⌝ ⇨ inv [] cur rest init))
      (fun b => binderNameHint b (done xs) <| done xs b)
      epost := by
  let inv' : Invariant α β Pred := fun pref suff b =>
    match suff with
    | [] => done xs b
    | cur :: rest => inv pref cur rest b
  have step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [h]) b)
        (inv' pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv' (pref ++ [cur]) suff b'
          | .done b' => inv' xs [] b')
        epost := by
    intro pref cur suff h b
    cases suff with
    | cons next rest =>
      exact triple_post_le (step_mid pref cur next rest h b) fun r => by
        cases r <;> exact PartialOrder.rel_refl
    | nil =>
      exact triple_post_le (step_last pref cur h b) fun r => by
        cases r <;> exact PartialOrder.rel_refl
  have h := Spec.forIn'_list (init := init) inv' step
  apply Triple.intro
  exact PartialOrder.rel_trans (Spec.forIn_init_le xs init inv done) (by cases xs <;> exact h.le_wp)

/-- The spec for `Gadget.forLoopWithInvariantAndDone`: every exit establishes `done`, which the code
after the loop starts from. -/
@[spec]
public theorem Spec.forLoopWithInvariantAndDone
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred)
    {epost : EPred}
    (step_mid : ∀ pref cur next rest (h : Named.mk `h_prefix none (ForIn.toList xs = pref ++ cur :: next :: rest)) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at h; simp [h])) b)
        (binderNameHint pref (fun pref : List α => (pref, `pref)) <| binderNameHint cur f <|
          binderNameHint next (fun next : α => (next, `next)) <| binderNameHint rest (fun rest : List α => (rest, `rest)) <|
          binderNameHint b (inv pref cur (next :: rest)) <|
          inv pref cur (next :: rest) b)
        (stepPost (inv (pref ++ [cur]) next rest) (done (ForIn.toList xs)))
        epost)
    (step_last : ∀ pref cur (h : Named.mk `h_prefix none (ForIn.toList xs = pref ++ [cur])) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at h; simp [h])) b)
        (binderNameHint pref (fun pref : List α => (pref, `pref)) <| binderNameHint cur f <| binderNameHint b (inv pref cur []) <|
          inv pref cur [] b)
        (stepPost (done (ForIn.toList xs)) (done (ForIn.toList xs)))
        epost) :
    Triple
      (forLoopWithInvariantAndDone xs init f inv done)
      ((⌜Named.mk `h_empty none (ForIn.toList xs = [])⌝ ⇨ done [] init) ⊓ (⨅ cur, ⨅ rest, binderNameHint cur f <| binderNameHint rest (fun rest : List α => (rest, `rest)) <|
          ⌜Named.mk `h_nonempty none (ForIn.toList xs = cur :: rest)⌝ ⇨ inv [] cur rest init))
      (fun b => binderNameHint b (done (ForIn.toList xs)) <| done (ForIn.toList xs) b)
      epost := by
  unfold Gadget.forLoopWithInvariantAndDone
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list_inv_done (xs := ForIn.toList xs) (init := init) (f := fun a h b => f a ((LawfulMemForInId.mem_toList_iff).mp h) b) inv done step_mid step_last

/-- The spec for `Gadget.forLoopWithInvariantAndDoneReturning`: a `return` goes straight to the code
after the loop, and every other exit establishes `done`. -/
@[spec]
public theorem Spec.forLoopWithInvariantAndDoneReturning
    {α : Type u₁} {γ τ : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : Option γ × τ} {f : (a : α) → a ∈ xs → Option γ × τ → m (ForInStep (Option γ × τ))}
    {Q : Option γ × τ → Pred}
    (inv : List α → α → List α → τ → Pred)
    (done : List α → τ → Pred)
    {epost : EPred}
    (step_mid : ∀ pref cur next rest (h : Named.mk `h_prefix none (ForIn.toList xs = pref ++ cur :: next :: rest)) s,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at h; simp [h])) (none, s))
        (binderNameHint pref (fun pref : List α => (pref, `pref)) <| binderNameHint cur f <|
          binderNameHint next (fun next : α => (next, `next)) <| binderNameHint rest (fun rest : List α => (rest, `rest)) <|
          binderNameHint s (inv pref cur (next :: rest)) <|
          inv pref cur (next :: rest) s)
        (stepPost (noReturn (inv (pref ++ [cur]) next rest)) (onExit Q (done (ForIn.toList xs))))
        epost)
    (step_last : ∀ pref cur (h : Named.mk `h_prefix none (ForIn.toList xs = pref ++ [cur])) s,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at h; simp [h])) (none, s))
        (binderNameHint pref (fun pref : List α => (pref, `pref)) <| binderNameHint cur f <| binderNameHint s (inv pref cur []) <|
          inv pref cur [] s)
        (stepPost (onExit Q (done (ForIn.toList xs))) (onExit Q (done (ForIn.toList xs))))
        epost)
    (hD : ∀ s, binderNameHint s (done (ForIn.toList xs)) (done (ForIn.toList xs) s) ⊑ Q (none, s)) :
    Triple
      (forLoopWithInvariantAndDoneReturning xs init f inv done)
      ((⌜Named.mk `h_empty none (ForIn.toList xs = [])⌝ ⇨ onExit Q (done []) init) ⊓
        (⨅ cur, ⨅ rest, binderNameHint cur f <| binderNameHint rest (fun rest : List α => (rest, `rest)) <|
          ⌜Named.mk `h_nonempty none (ForIn.toList xs = cur :: rest)⌝ ⇨ noReturn (inv [] cur rest) init))
      Q epost := by
  have h := Spec.forLoopWithInvariantAndDone (xs := xs) (init := init) (f := f)
    (fun pref cur rest => noReturn (inv pref cur rest)) (fun l => onExit Q (done l))
    (fun pref cur next rest hh => noReturn_step (inv := inv pref cur (next :: rest))
      (x := fun b => f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at hh; simp [hh])) b)
      (post := fun _ => stepPost (noReturn (inv (pref ++ [cur]) next rest))
        (onExit Q (done (ForIn.toList xs))))
      (step_mid pref cur next rest hh))
    (fun pref cur hh => noReturn_step (inv := inv pref cur [])
      (x := fun b => f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [Named.mk_eq] at hh; simp [hh])) b)
      (post := fun _ => stepPost (onExit Q (done (ForIn.toList xs))) (onExit Q (done (ForIn.toList xs))))
      (step_last pref cur hh))
  unfold Gadget.forLoopWithInvariantAndDone at h
  unfold Gadget.forLoopWithInvariantAndDoneReturning
  exact triple_onExit (done := done (ForIn.toList xs)) h hD

/-! ## Lemmas for range loops -/

@[simp, grind =]
public theorem list_append_cons_ne_nil {α} (l1 : List α) (x : α) (l2 : List α) :
    (l1 ++ x :: l2 = []) ↔ False := by simp

@[grind →]
public theorem list_range_head {n : Nat} {cur : Nat} {rest : List Nat} (h : List.range n = cur :: rest) :
    cur = 0 := by
  have : (List.range n)[0]? = (cur :: rest)[0]? := by rw [h]
  simp only [List.getElem?_cons_zero] at this
  cases n with
  | zero => simp at h
  | succ m =>
    rw [List.getElem?_range] at this
    · cases this; rfl
    · omega

@[grind →]
public theorem list_range_mem {n : Nat} {pref : List Nat} {cur : Nat} {rest : List Nat}
    (h : List.range n = pref ++ cur :: rest) : cur = pref.length ∧ cur < n := by
  have hcur : (List.range n)[pref.length]? = (pref ++ cur :: rest)[pref.length]? := by rw [h]
  rw [List.getElem?_append_right (by omega)] at hcur
  simp only [Nat.sub_self, List.getElem?_cons_zero] at hcur
  have hlen_lt : pref.length < n := by
    have := congrArg List.length h
    simp only [List.length_range, List.length_append, List.length_cons] at this
    omega
  rw [List.getElem?_range hlen_lt] at hcur
  cases hcur
  omega

@[grind →]
public theorem list_range_next {n : Nat} {pref : List Nat} {cur next : Nat} {rest : List Nat}
    (h : List.range n = pref ++ cur :: next :: rest) : next = cur + 1 ∧ cur + 1 ≤ n := by
  have hcur : (List.range n)[pref.length]? = (pref ++ cur :: next :: rest)[pref.length]? := by rw [h]
  have hnext : (List.range n)[pref.length + 1]? = (pref ++ cur :: next :: rest)[pref.length + 1]? := by rw [h]
  rw [List.getElem?_append_right (by omega)] at hcur
  simp only [Nat.sub_self, List.getElem?_cons_zero] at hcur
  have hlen : pref.length + 1 - pref.length = 1 := by omega
  rw [List.getElem?_append_right (by omega), hlen] at hnext
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hnext
  have hlen_lt : pref.length + 1 < n := by
    have := congrArg List.length h
    simp only [List.length_range, List.length_append, List.length_cons] at this
    omega
  rw [List.getElem?_range (by omega)] at hcur
  rw [List.getElem?_range hlen_lt] at hnext
  cases hcur; cases hnext
  omega

@[grind →]
public theorem list_range_last {n : Nat} {pref : List Nat} {cur : Nat}
    (h : List.range n = pref ++ [cur]) : cur + 1 = n := by
  have hcur : (List.range n)[pref.length]? = (pref ++ [cur])[pref.length]? := by rw [h]
  rw [List.getElem?_append_right (by omega)] at hcur
  simp only [Nat.sub_self, List.getElem?_cons_zero] at hcur
  have hlen : pref.length + 1 = n := by
    have := congrArg List.length h
    simp only [List.length_range, List.length_append, List.length_cons, List.length_nil] at this
    omega
  rw [List.getElem?_range (by omega)] at hcur
  cases hcur
  omega


end Loop

export Loop (list_range_head list_range_next list_range_last)
