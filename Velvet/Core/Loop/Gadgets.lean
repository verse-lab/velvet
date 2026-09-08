module

public import Velvet.Core.Specs
public import Velvet.Core.Partial
public import Std.WP
public import Std.WP.Gadget.ForIn
public import Std.WP.Triple.SpecLemmas
public import Std.Internal.ForIn

open Std.Internal
open Std.WP
open Std.WP.Assertion
open Lean.Order
open WPPartial

universe u u₁ u₂ v w

namespace Loop

/-- Our own least-fixed-point loop: `partial_fixpoint` over the loop body. -/
@[expose] public def forIn.loop {β : Type u} {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => forIn.loop f b
  partial_fixpoint

/-- Dedicated collection marker for partial `while'` loops. Using a distinct
collection type lets `ForIn` dispatch to fixed-point execution without
replacing the ordinary `ForIn m Lean.Loop Unit` instance. -/
public structure PartialLoop where
  mk ::

public instance instForInPartialLoopOfCCPO {m : Type u → Type v}
    [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] :
    ForIn m PartialLoop Unit where
  forIn _ init f := forIn.loop f init

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

namespace Gadget

set_option linter.unusedVariables false in
/-- A pure `forIn` loop annotated with a state invariant (independent of the cursor variable).
The invariant holds before entering the loop, is preserved at every step, and holds upon exit. -/
@[inline] public def forInPureWithStateInv {ρ : Type w} [ForIn m ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β))
    (inv : β → Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
/-- A pure `forIn'` loop annotated with a state invariant and membership proofs in the loop body. -/
@[inline] public def forInPureWithStateInv' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : β → Pred) : m β :=
  forIn' xs init f

set_option linter.unusedVariables false in
@[inline] public def forInPureWithInvAndDone {ρ : Type w} [ForIn m ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β))
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
@[inline] public def forInPureWithInvAndDone' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred) : m β :=
  forIn' xs init f

set_option linter.unusedVariables false in
@[expose, inline] public def whileLoopPartial {β : Type u} {m : Type u → Type v}
    [ForIn m PartialLoop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (done : β → Pred) : m β :=
  forIn PartialLoop.mk init f

set_option linter.unusedVariables false in
@[expose, inline] public def whileLoopTotal {β : Type u} {m : Type u → Type v} [ForIn m Lean.Loop Unit]
    (init : β) (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (done : β → Pred) (measure : β → Named.Measure) : m β :=
  forIn Lean.Loop.mk init f

end Gadget

open Gadget

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
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) next rest b'
          | .done b' => done xs b')
        epost)
    (step_last : ∀ pref cur (h : xs = pref ++ [cur]) b,
      Triple
        (f cur (by simp [h]) b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur []) <|
          inv pref cur [] b)
        (fun r => match r with
          | .yield b' => done xs b'
          | .done b' => done xs b')
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
      exact step_mid pref cur next rest h b
    | nil =>
      exact step_last pref cur h b
  have h := Spec.forIn'_list (init := init) inv' step
  apply Triple.intro
  exact PartialOrder.rel_trans (Spec.forIn_init_le xs init inv done) (by cases xs <;> exact h.le_wp)

set_option linter.unusedVariables false in
public theorem Spec.forIn_list_inv_done
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred)
    {epost : EPred}
    (step_mid : ∀ pref cur next rest (h : xs = pref ++ cur :: next :: rest) b,
      Triple
        (f cur b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur (next :: rest)) <|
          inv pref cur (next :: rest) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) next rest b'
          | .done b' => done xs b')
        epost)
    (step_last : ∀ pref cur (h : xs = pref ++ [cur]) b,
      Triple
        (f cur b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur []) <|
          inv pref cur [] b)
        (fun r => match r with
          | .yield b' => done xs b'
          | .done b' => done xs b')
        epost) :
    Triple
      (forIn xs init f)
      ((⌜xs = []⌝ ⇨ done [] init) ⊓ (⨅ cur, ⨅ rest, ⌜xs = cur :: rest⌝ ⇨ inv [] cur rest init))
      (fun b => binderNameHint b (done xs) <| done xs b)
      epost := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list_inv_done inv done (fun pref cur next rest h b => step_mid pref cur next rest h b) (fun pref cur h b => step_last pref cur h b)

set_option linter.unusedVariables false in
@[spec]
public theorem Spec.forInPure
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
    [PureForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)}
    (inv : List α → α → List α → β → Pred)
    (done : List α → β → Pred)
    {epost : EPred}
    (step_mid : ∀ pref cur next rest (h : ForIn.toList xs = pref ++ cur :: next :: rest) b,
      Triple
        (f cur b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur (next :: rest)) <|
          inv pref cur (next :: rest) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) next rest b'
          | .done b' => done (ForIn.toList xs) b')
        epost)
    (step_last : ∀ pref cur (h : ForIn.toList xs = pref ++ [cur]) b,
      Triple
        (f cur b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur []) <|
          inv pref cur [] b)
        (fun r => match r with
          | .yield b' => done (ForIn.toList xs) b'
          | .done b' => done (ForIn.toList xs) b')
        epost) :
    Triple
      (forInPureWithInvAndDone xs init f inv done)
      ((⌜ForIn.toList xs = []⌝ ⇨ done [] init) ⊓ (⨅ cur, ⨅ rest, ⌜ForIn.toList xs = cur :: rest⌝ ⇨ inv [] cur rest init))
      (fun b => binderNameHint b (done (ForIn.toList xs)) <| done (ForIn.toList xs) b)
      epost := by
  unfold forInPureWithInvAndDone
  rw [PureForIn.forIn_eq]
  exact Spec.forIn_list_inv_done (init := init) inv done step_mid step_last

@[spec]
public theorem Spec.forInPure'
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
    (step_mid : ∀ pref cur next rest (h : ForIn.toList xs = pref ++ cur :: next :: rest) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [h])) b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur (next :: rest)) <|
          inv pref cur (next :: rest) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) next rest b'
          | .done b' => done (ForIn.toList xs) b')
        epost)
    (step_last : ∀ pref cur (h : ForIn.toList xs = pref ++ [cur]) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [h])) b)
        (binderNameHint pref inv <| binderNameHint cur f <| binderNameHint b (inv pref cur []) <|
          inv pref cur [] b)
        (fun r => match r with
          | .yield b' => done (ForIn.toList xs) b'
          | .done b' => done (ForIn.toList xs) b')
        epost) :
    Triple
      (forInPureWithInvAndDone' xs init f inv done)
      ((⌜ForIn.toList xs = []⌝ ⇨ done [] init) ⊓ (⨅ cur, ⨅ rest, ⌜ForIn.toList xs = cur :: rest⌝ ⇨ inv [] cur rest init))
      (fun b => binderNameHint b (done (ForIn.toList xs)) <| done (ForIn.toList xs) b)
      epost := by
  unfold forInPureWithInvAndDone'
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list_inv_done (xs := ForIn.toList xs) (init := init) (f := fun a h b => f a ((LawfulMemForInId.mem_toList_iff).mp h) b) inv done step_mid step_last

public theorem Spec.forIn'_list_state_inv
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : β → Pred)
    {epost : EPred}
    (step : ∀ cur (h : cur ∈ xs) b,
      Triple
        (f cur h b)
        (binderNameHint cur f <| binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' => inv b'
          | .done b' => inv b')
        epost) :
    Triple
      (forIn' xs init f)
      (inv init)
      (fun b => binderNameHint b inv <| inv b)
      epost := by
  let inv' : Invariant α β Pred := fun _ _ b => inv b
  have step' : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [h]) b)
        (inv' pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv' (pref ++ [cur]) suff b'
          | .done b' => inv' xs [] b')
        epost := by
    intro pref cur suff h b
    exact step cur (by simp [h]) b
  have h := Spec.forIn'_list (init := init) inv' step'
  cases xs
  · exact h
  · exact h

set_option linter.unusedVariables false in
public theorem Spec.forIn_list_state_inv
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : β → Pred)
    {epost : EPred}
    (step : ∀ cur (h : cur ∈ xs) b,
      Triple
        (f cur b)
        (binderNameHint cur f <| binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' => inv b'
          | .done b' => inv b')
        epost) :
    Triple
      (forIn xs init f)
      (inv init)
      (fun b => binderNameHint b inv <| inv b)
      epost := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list_state_inv inv step

set_option linter.unusedVariables false in
/-- Specification lemma for pure `forIn` loops with state invariants (independent of loop cursor). -/
@[spec]
public theorem Spec.forInPure_state_inv
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
    [PureForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)}
    (inv : β → Pred)
    {epost : EPred}
    (step : ∀ cur (h : cur ∈ ForIn.toList xs) b,
      Triple
        (f cur b)
        (binderNameHint cur f <| binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' => inv b'
          | .done b' => inv b')
        epost) :
    Triple
      (forInPureWithStateInv xs init f inv)
      (inv init)
      (fun b => binderNameHint b inv <| inv b)
      epost := by
  unfold forInPureWithStateInv
  rw [PureForIn.forIn_eq]
  exact Spec.forIn_list_state_inv (init := init) inv step

set_option linter.unusedVariables false in
/-- Specification lemma for pure `forIn'` loops with state invariants and membership proofs. -/
@[spec]
public theorem Spec.forInPure'_state_inv
    {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
    {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : β → Pred)
    {epost : EPred}
    (step : ∀ cur (h : cur ∈ ForIn.toList xs) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp h) b)
        (binderNameHint cur f <| binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' => inv b'
          | .done b' => inv b')
        epost) :
    Triple
      (forInPureWithStateInv' xs init f inv)
      (inv init)
      (fun b => binderNameHint b inv <| inv b)
      epost := by
  unfold forInPureWithStateInv'
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list_state_inv (init := init) inv step

@[spec 1100]
public theorem bot_partial
    {Pred : Type u₁} {EPred : Type u₂} {div_post : EPred} {div_pre : EPred → Pred}
    {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred div_post div_pre]
    {α : Type u} {pre : Pred} {post : α → Pred} :
    Triple (CCPO.csup (α := m α) (c := fun _ => False) emptyChain)
      pre
      post div_post := by
  constructor
  rw [WPPartial.wp_bot]
  exact WPPartial.le_divergence_post (m := m) pre

@[spec 1200]
public theorem Spec.whileLoop_partial
    {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [MonoBind m] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β}
    (inv : β → Pred) (done : β → Pred)
    {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b)
      (binderNameHint b inv <| inv b)
      (fun r => match r with
        | .yield b' => inv b'
        | .done b' => done b')
      einv) :
    Triple (whileLoopPartial init f inv done)
      (inv init)
      (fun b => binderNameHint b done <| done b)
      einv := by
  unfold whileLoopPartial
  change Triple (Loop.forIn.loop f init) (inv init) (fun b => done b) einv
  let inv' : β ⊕ β → Pred := fun
    | .inl b => inv b
    | .inr b => done b
  have step' : ∀ b, Triple (f () b) (inv' (.inl b))
      (fun r => match r with
        | .yield b' => inv' (.inl b')
        | .done b' => inv' (.inr b')) einv := by
    intro b
    exact step b
  exact forInLoop_partial f init inv' einv hdiv step'

@[spec 1200]
public theorem Spec.whileLoop_total
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {init : β}
    (inv : β → Pred) (done : β → Pred) (measure : β → Named.Measure)
    {f : Unit → β → m (ForInStep β)} {einv : EPred}
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
  let inv' : WhileInvariant β Pred := fun
    | false, b => inv b
    | true, b => done b
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
    simpa [Named.mk_eq, loopMeasure,
      Variant.evalsBelow_ofMeasure, natRel] using (step b).le_wp
  unfold whileLoopTotal
  exact Spec.forIn_loop (l := Lean.Loop.mk) (init := init) loopMeasure inv' einv step'

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
