import Velvet
import Velvet.Examples.ITree.ITree

/-!
# Interaction trees with infinite traces, for Velvet

A weakest precondition for the interaction trees of `ITree.lean` that sees infinite runs, so that
a server meant to run forever can be given a liveness specification.

A run of a tree, with the environment choosing the answers to its events, is one of:

* *returns*: finitely many events, then `ret r`;
* *runs forever*: infinitely many events;
* *stalls*: finitely many events, then `div`: silent divergence.

`wp t Q estack⟨Ω⟩ tr` holds iff, from the past trace `tr`, every returning run of `t` satisfies
`Q` (in the trace it reaches), every infinite run satisfies `Ω` (on its whole trace, past
included), and no run stalls. Whole traces are possibly infinite lists, `CoTrace E := CoList
(Event E)`: a finite trace `tr : Trace E` is one too (`↑tr`), so one property, such as "every ping
is followed by a pong", reads on both. The postcondition `Ω` of the runs that never return is the
exception postcondition (`EStack⟨CoTrace E → Prop⟩`): a Velvet method states it with
`signals (σ : CoTrace E) => …`.

Stalling is ruled out, so a server that hangs after a request does not satisfy "every request is
eventually answered" vacuously. Velvet's partial-correctness `while` rule needs `div` to satisfy
something (`WPPartial`), which it does not here, so `whileLoopPartial_live` replaces it for
`ITree`: each round of the loop must extend the trace, and an invariant that holds at infinitely
many prefixes becomes a property of the infinite trace.
-/

open Std.WP Lean.Order

noncomputable section

universe u

/-! ## 1. Possibly infinite lists -/

/-- Possibly infinite lists. -/
codatatype CoList (α : Type u)
  | nil
  | cons (a : α) (t : CoList α)

namespace CoList

variable {α : Type u}

/-- The `n`-th element, if there is one. -/
def get? : CoList α → Nat → Option α
  | s, 0 => match s.dtor with | .nil => none | .cons a _ => some a
  | s, n + 1 => match s.dtor with | .nil => none | .cons _ t => t.get? n

/-- The first `n` elements, or all of them if there are fewer. -/
def take : Nat → CoList α → List α
  | 0, _ => []
  | n + 1, s => match s.dtor with | .nil => [] | .cons a t => a :: take n t

/-- The finite list `l`, followed by `s`. -/
def prepend (l : List α) (s : CoList α) : CoList α := l.foldr cons s

/-- A finite list, as a colist. -/
def ofList (l : List α) : CoList α := prepend l nil

instance : Coe (List α) (CoList α) := ⟨ofList⟩

@[simp] theorem prepend_nil (s : CoList α) : prepend [] s = s := rfl

@[simp] theorem prepend_cons (a : α) (l : List α) (s : CoList α) :
    prepend (a :: l) s = cons a (prepend l s) := rfl

theorem prepend_append (l₁ l₂ : List α) (s : CoList α) :
    prepend (l₁ ++ l₂) s = prepend l₁ (prepend l₂ s) := List.foldr_append

@[simp] theorem take_prepend (l : List α) (s : CoList α) : (prepend l s).take l.length = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [take, dtor_cons, ih]

@[simp] theorem get?_ofList (l : List α) (n : Nat) : (ofList l : CoList α).get? n = l[n]? := by
  induction l generalizing n with
  | nil => cases n <;> simp [ofList, get?, dtor_nil]
  | cons a l ih =>
    cases n with
    | zero => simp [ofList, get?, dtor_cons]
    | succ n => simpa [ofList, get?, dtor_cons] using ih n

theorem getElem?_take (s : CoList α) (m n : Nat) :
    (s.take m)[n]? = if n < m then s.get? n else none := by
  induction m generalizing s n with
  | zero => simp [take]
  | succ m ih =>
    cases s with
    | nil => cases n <;> simp [take, get?, dtor_nil]
    | cons a t => cases n <;> simp [take, get?, dtor_cons, ih]

end CoList


set_option experimental.vcgen true

variable {E : Type → Type} {R S : Type}

/-- A possibly infinite trace: a colist of events, each with its answer. -/
abbrev CoTrace (E : Type → Type) := CoList (Event E)

/-- The finite trace `tr`, followed by the possibly infinite trace `σ`. -/
abbrev CoTrace.prepend (tr : Trace E) (σ : CoTrace E) : CoTrace E := CoList.prepend tr σ

theorem CoTrace.prepend_cons (ev : Event E) (tr : Trace E) (σ : CoTrace E) :
    prepend (ev :: tr) σ = .cons ev (prepend tr σ) := rfl

theorem CoTrace.prepend_append (l₁ l₂ : Trace E) (σ : CoTrace E) :
    prepend (l₁ ++ l₂) σ = prepend l₁ (prepend l₂ σ) := CoList.prepend_append ..

namespace ITree

/-! ## 2. Runs of a tree -/

/-- `t.Returns l r`: `t` performs the events of `l` (with the answers recorded there), then
returns `r`. -/
def Returns (t : ITree E R) : Trace E → R → Prop
  | [], r => t.dtor = .ret r
  | ev :: l, r => ∃ k, t.dtor = .vis ev.e k ∧ (k ev.a).Returns l r

/-- `t.Stalls l`: `t` performs the events of `l`, then diverges silently (`div`). -/
def Stalls (t : ITree E R) : Trace E → Prop
  | [] => t.dtor = .div
  | ev :: l => ∃ k, t.dtor = .vis ev.e k ∧ (k ev.a).Stalls l

/-- `t.Runs σ`: `t` performs the events of `σ`, forever (so `σ` is infinite). -/
def Runs (t : ITree E R) (σ : CoTrace E) : Prop :=
  match t.dtor with
  | .vis e k => ∃ a σ', σ = .cons ⟨e, a⟩ σ' ∧ (k a).Runs σ'
  | _ => False
  coinductive_fixpoint

/-- The weakest precondition: from past trace `tr`, returning runs satisfy `Q`, infinite runs
satisfy `Ω`, and no run stalls. -/
structure Live (Q : R → Trace E → Prop) (Ω : CoTrace E → Prop) (t : ITree E R)
    (tr : Trace E) : Prop where
  finite : ∀ l r, t.Returns l r → Q r (tr ++ l)
  infinite : ∀ σ, t.Runs σ → Ω (CoTrace.prepend tr σ)
  productive : ∀ l, ¬ t.Stalls l

/-! Runs of the three kinds of node. -/

theorem returns_ret {r r' : R} {l : Trace E} : (ret r : ITree E R).Returns l r' ↔ l = [] ∧ r = r' := by
  cases l <;> simp [Returns, dtor_ret]

theorem returns_vis_nil {X : Type} {e : E X} {k : X → ITree E R} {r : R} :
    ¬ (vis e k).Returns [] r := by
  simp [Returns, dtor_vis]

theorem returns_vis {X : Type} {e : E X} {k : X → ITree E R} {a : X} {l : Trace E} {r : R} :
    (vis e k).Returns (⟨e, a⟩ :: l) r ↔ (k a).Returns l r := by
  simp [Returns, dtor_vis]

theorem returns_vis_inv {X : Type} {e : E X} {k : X → ITree E R} {ev : Event E} {l : Trace E}
    {r : R} (h : (vis e k).Returns (ev :: l) r) : ∃ a, ev = ⟨e, a⟩ ∧ (k a).Returns l r := by
  obtain ⟨e', a'⟩ := ev
  obtain ⟨k', h, hr⟩ := h
  rw [dtor_vis] at h
  cases h
  exact ⟨a', rfl, hr⟩

theorem not_returns_div {l : Trace E} {r : R} : ¬ (div : ITree E R).Returns l r := by
  cases l <;> simp [Returns, dtor_div]

theorem not_stalls_ret {r : R} {l : Trace E} : ¬ (ret r : ITree E R).Stalls l := by
  cases l <;> simp [Stalls, dtor_ret]

theorem stalls_vis_inv {X : Type} {e : E X} {k : X → ITree E R} {l : Trace E}
    (h : (vis e k).Stalls l) : ∃ ev l', l = ev :: l' ∧ ∃ a, ev = ⟨e, a⟩ ∧ (k a).Stalls l' := by
  obtain _ | ⟨⟨e', a'⟩, l⟩ := l
  · simp [Stalls, dtor_vis] at h
  obtain ⟨k', h, hs⟩ := h
  rw [dtor_vis] at h
  cases h
  exact ⟨_, _, rfl, a', rfl, hs⟩

theorem not_runs_ret {r : R} {σ : CoTrace E} : ¬ (ret r : ITree E R).Runs σ := by
  rw [Runs, dtor_ret]; exact id

theorem not_runs_div {σ : CoTrace E} : ¬ (div : ITree E R).Runs σ := by
  rw [Runs, dtor_div]; exact id

theorem runs_vis {X : Type} {e : E X} {k : X → ITree E R} {σ : CoTrace E} :
    (vis e k).Runs σ ↔ ∃ a σ', σ = .cons ⟨e, a⟩ σ' ∧ (k a).Runs σ' := by
  rw [Runs, dtor_vis]

/-! Runs of `bind`: a run of `t.bind f` is a run of `t`, or a returning run of `t` followed by a
run of the continuation. -/

theorem Returns.bind_inv {t : ITree E R} {f : R → ITree E S} {l : Trace E} {s : S}
    (h : (t.bind f).Returns l s) :
    ∃ l₁ r l₂, t.Returns l₁ r ∧ (f r).Returns l₂ s ∧ l = l₁ ++ l₂ := by
  induction l generalizing t with
  | nil =>
    cases t with
    | ret r => exact ⟨[], r, [], returns_ret.2 ⟨rfl, rfl⟩, by simpa using h, rfl⟩
    | vis e k => rw [vis_bind] at h; exact absurd h returns_vis_nil
    | div => rw [div_bind] at h; exact absurd h not_returns_div
  | cons ev l ih =>
    cases t with
    | ret r => exact ⟨[], r, ev :: l, returns_ret.2 ⟨rfl, rfl⟩, by simpa using h, rfl⟩
    | vis e k =>
      rw [vis_bind] at h
      obtain ⟨a, rfl, h'⟩ := returns_vis_inv h
      obtain ⟨l₁, r, l₂, h₁, h₂, rfl⟩ := ih h'
      exact ⟨⟨e, a⟩ :: l₁, r, l₂, returns_vis.2 h₁, h₂, rfl⟩
    | div => rw [div_bind] at h; exact absurd h not_returns_div

theorem Stalls.bind_inv {t : ITree E R} {f : R → ITree E S} {l : Trace E}
    (h : (t.bind f).Stalls l) :
    t.Stalls l ∨ ∃ l₁ r l₂, t.Returns l₁ r ∧ (f r).Stalls l₂ ∧ l = l₁ ++ l₂ := by
  induction l generalizing t with
  | nil =>
    cases t with
    | ret r => exact .inr ⟨[], r, [], returns_ret.2 ⟨rfl, rfl⟩, by simpa using h, rfl⟩
    | vis e k => rw [vis_bind] at h; simp [Stalls, dtor_vis] at h
    | div => exact .inl (by simp [Stalls, dtor_div])
  | cons ev l ih =>
    cases t with
    | ret r => exact .inr ⟨[], r, ev :: l, returns_ret.2 ⟨rfl, rfl⟩, by simpa using h, rfl⟩
    | vis e k =>
      rw [vis_bind] at h
      obtain ⟨_, _, ⟨⟩, a, rfl, h'⟩ := stalls_vis_inv h
      rcases ih h' with h'' | ⟨l₁, r, l₂, h₁, h₂, rfl⟩
      · exact .inl ⟨k, by rw [dtor_vis], h''⟩
      · exact .inr ⟨⟨e, a⟩ :: l₁, r, l₂, returns_vis.2 h₁, h₂, rfl⟩
    | div => rw [div_bind] at h; simp [Stalls, dtor_div] at h

theorem Runs.bind_inv {t : ITree E R} {f : R → ITree E S} {σ : CoTrace E}
    (h : (t.bind f).Runs σ) :
    t.Runs σ ∨ ∃ l r σ', t.Returns l r ∧ (f r).Runs σ' ∧ σ = CoTrace.prepend l σ' := by
  by_cases hd : ∃ l r σ', t.Returns l r ∧ (f r).Runs σ' ∧ σ = CoTrace.prepend l σ'
  · exact .inr hd
  refine .inl (Runs.coinduct (fun t σ => (t.bind f).Runs σ ∧
    ¬ ∃ l r σ', t.Returns l r ∧ (f r).Runs σ' ∧ σ = CoTrace.prepend l σ') ?_ t σ ⟨h, hd⟩)
  rintro t σ ⟨h, hd⟩
  cases t with
  | ret r => exact hd ⟨[], r, σ, returns_ret.2 ⟨rfl, rfl⟩, by simpa using h, by simp⟩
  | vis e k =>
    rw [vis_bind, runs_vis] at h
    obtain ⟨a, σ', rfl, h⟩ := h
    rw [dtor_vis]
    refine ⟨a, σ', rfl, h, ?_⟩
    rintro ⟨l, r, σ'', h₁, h₂, rfl⟩
    exact hd ⟨⟨e, a⟩ :: l, r, σ'', returns_vis.2 h₁, h₂, (CoTrace.prepend_cons ..).symm⟩
  | div => rw [div_bind] at h; exact absurd h not_runs_div

end ITree

/-! ## 3. The weakest precondition -/

/-- `ITree E` is a `WPMonad`: assertions are predicates on the past trace, and the one
"exception" postcondition is the predicate `Ω` on infinite traces. -/
instance : WPMonad (ITree E) (Trace E → Prop) EStack⟨CoTrace E → Prop⟩ where
  toWP _ :=
    { wpTrans t := ⟨fun Q Ω => ITree.Live Q Ω.1 t⟩
      wp_trans_monotone _ _ _ _ _ hΩ hQ tr h :=
        ⟨fun l r hr => hQ _ _ (h.finite l r hr), fun σ hσ => hΩ.1 _ (h.infinite σ hσ),
          h.productive⟩ }
  pure_le_wp_pure r Q Ω tr h := by
    refine ⟨fun l r' hr => ?_, fun σ hσ => absurd hσ ITree.not_runs_ret,
      fun l => ITree.not_stalls_ret⟩
    obtain ⟨rfl, rfl⟩ := ITree.returns_ret.1 hr
    simpa using h
  bind_le_wp_bind t f Q Ω tr h := by
    have h : ITree.Live (fun r tr => ITree.Live Q Ω.1 (f r) tr) Ω.1 t tr := h
    show ITree.Live Q Ω.1 (ITree.bind t f) tr
    refine ⟨fun l s hs => ?_, fun σ hσ => ?_, fun l hl => ?_⟩
    · obtain ⟨l₁, r, l₂, h₁, h₂, rfl⟩ := ITree.Returns.bind_inv hs
      simpa using (h.finite l₁ r h₁).finite l₂ s h₂
    · rcases ITree.Runs.bind_inv hσ with hσ | ⟨l, r, σ', h₁, h₂, rfl⟩
      · exact h.infinite σ hσ
      · simpa [CoTrace.prepend_append] using (h.finite l r h₁).infinite σ' h₂
    · rcases ITree.Stalls.bind_inv hl with hl | ⟨l₁, r, l₂, h₁, h₂, rfl⟩
      · exact h.productive l hl
      · exact (h.finite l₁ r h₁).productive l₂ h₂

/-- A triple, unfolded: the precondition entails `ITree.Live`. -/
theorem ITree.live_of_triple {t : ITree E R} {P : Trace E → Prop} {Q : R → Trace E → Prop}
    {Ω : EStack⟨CoTrace E → Prop⟩} (h : ⦃ P ⦄ t ⦃ Q; Ω ⦄) {tr : Trace E} (hP : P tr) :
    ITree.Live Q Ω.1 t tr :=
  h.le_wp tr hP

/-! ## 4. Specs for the primitives -/

namespace ITree

/-- Events: any answer `a` is possible, and the event is recorded in the trace. No infinite runs,
so no `Ω`. -/
@[spec] theorem trigger_spec {X : Type} (e : E X) (Q : X → Trace E → Prop) :
    ⦃ fun tr => ∀ a, Q a (tr ++ [⟨e, a⟩]) ⦄ trigger e ⦃ Q ⦄ := ⟨fun tr h => by
  show ITree.Live Q _ (.vis e .ret) tr
  refine ⟨fun l r hr => ?_, fun σ hσ => ?_, fun l hl => ?_⟩
  · obtain _ | ⟨ev, l⟩ := l
    · exact absurd hr ITree.returns_vis_nil
    obtain ⟨a, rfl, hr'⟩ := ITree.returns_vis_inv hr
    obtain ⟨rfl, rfl⟩ := ITree.returns_ret.1 hr'
    exact h a
  · obtain ⟨a, σ', -, hσ'⟩ := ITree.runs_vis.1 hσ
    exact absurd hσ' ITree.not_runs_ret
  · obtain ⟨_, _, rfl, a, rfl, hl'⟩ := ITree.stalls_vis_inv hl
    exact ITree.not_stalls_ret hl'⟩

/-! ## 5. `while` loops

A partial-correctness `while` in a Velvet method becomes `Loop.Gadget.whileLoopPartial init f inv
done?`, where `f () b` runs one round from loop state `b` and `inv` is the conjunction of the
loop's `invariant` clauses. -/

open Loop

theorem whileLoopPartial_unfold {β : Type} (init : β) (f : Unit → β → ITree E (ForInStep β))
    (inv : β → Trace E → Prop) (done? : Option (β → Trace E → Prop)) :
    Gadget.whileLoopPartial init f inv done? =
      (f () init).bind fun
        | .done b => .ret b
        | .yield b => Gadget.whileLoopPartial b f inv done? :=
  Loop.forIn.loop.eq_1 f init

/-- The `while` rule, for liveness.

* `step`: each round preserves the invariant `inv`, and a round that goes on to the next one
  extends the trace: the ghost `n` is the length of the trace at the start of the round. A round
  that exits establishes `Q`; a round that runs forever establishes `Ω`.
* `live`: if `inv` holds at infinitely many prefixes of a trace, the trace satisfies `Ω`.
  This is how a safety invariant, checked once per round, becomes a liveness property of a loop
  that never exits. -/
@[spec 1300] theorem whileLoopPartial_live {β : Type} {init : β}
    {f : Unit → β → ITree E (ForInStep β)} {done? : Option (β → Trace E → Prop)}
    {Q : β → Trace E → Prop} {Ω : EStack⟨CoTrace E → Prop⟩} (inv : β → Trace E → Prop)
    (step : ∀ b n, ⦃ fun tr => inv b tr ∧ tr.length = n ⦄ f () b
      ⦃ fun r tr => match r with
        | .yield b' => inv b' tr ∧ n < tr.length
        | .done b' => Q b' tr; Ω ⦄)
    (live : ∀ σ : CoTrace E, (∀ n, ∃ m, n ≤ m ∧ ∃ b, inv b (σ.take m)) → Ω.1 σ) :
    ⦃ inv init ⦄ Gadget.whileLoopPartial init f inv done? ⦃ Q; Ω ⦄ := by
  let loop b := Gadget.whileLoopPartial b f inv done?
  -- one round, as a statement about runs
  have hstep : ∀ b tr, inv b tr → Live (fun r tr' => match r with
      | .yield b' => inv b' tr' ∧ tr.length < tr'.length
      | .done b' => Q b' tr') Ω.1 (f () b) tr :=
    fun b tr h => live_of_triple (step b tr.length) ⟨h, rfl⟩
  -- returning runs: induction on the length of the run
  have hret : ∀ n (l : Trace E), l.length = n → ∀ b tr r, inv b tr →
      (loop b).Returns l r → Q r (tr ++ l) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro l hl b tr r hI hr
      rw [show loop b = _ from whileLoopPartial_unfold b f inv done?] at hr
      obtain ⟨l₁, s, l₂, h₁, h₂, rfl⟩ := Returns.bind_inv hr
      have hb := (hstep b tr hI).finite l₁ s h₁
      cases s with
      | done b' => obtain ⟨rfl, rfl⟩ := returns_ret.1 h₂; simpa using hb
      | yield b' =>
        obtain ⟨hI', hlen⟩ := hb
        simp only [List.length_append] at hlen hl
        simpa using ih l₂.length (by omega) l₂ rfl b' (tr ++ l₁) r hI' h₂
  -- stalling runs: the same induction
  have hstall : ∀ n (l : Trace E), l.length = n → ∀ b tr, inv b tr → ¬ (loop b).Stalls l := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro l hl b tr hI hs
      rw [show loop b = _ from whileLoopPartial_unfold b f inv done?] at hs
      rcases Stalls.bind_inv hs with hs | ⟨l₁, s, l₂, h₁, h₂, rfl⟩
      · exact (hstep b tr hI).productive l hs
      have hb := (hstep b tr hI).finite l₁ s h₁
      cases s with
      | done b' => exact not_stalls_ret h₂
      | yield b' =>
        obtain ⟨hI', hlen⟩ := hb
        simp only [List.length_append] at hlen hl
        exact ih l₂.length (by omega) l₂ rfl b' (tr ++ l₁) hI' h₂
  -- infinite runs: unless `Ω` holds, the run completes another round of the loop
  have hnext : ∀ b tr σ, inv b tr → (loop b).Runs σ → ¬ Ω.1 (CoTrace.prepend tr σ) →
      ∃ b' l σ', σ = CoTrace.prepend l σ' ∧ 0 < l.length ∧ inv b' (tr ++ l) ∧
        (loop b').Runs σ' := by
    intro b tr σ hI hσ hΩ
    rw [show loop b = _ from whileLoopPartial_unfold b f inv done?] at hσ
    rcases Runs.bind_inv hσ with hσ | ⟨l, s, σ', h₁, h₂, rfl⟩
    · exact absurd ((hstep b tr hI).infinite σ hσ) hΩ
    have hb := (hstep b tr hI).finite l s h₁
    cases s with
    | done b' => exact absurd h₂ not_runs_ret
    | yield b' =>
      obtain ⟨hI', hlen⟩ := hb
      simp only [List.length_append] at hlen
      exact ⟨b', l, σ', rfl, by omega, hI', h₂⟩
  refine ⟨fun tr hI => ⟨fun l r hr => hret _ l rfl init tr r hI hr, fun σ hσ => ?_,
    fun l => hstall _ l rfl init tr hI⟩⟩
  -- an infinite run that violates `Ω` passes through infinitely many rounds
  refine Classical.byContradiction fun hΩ => ?_
  have rounds : ∀ n, ∃ b tr' σ', n ≤ tr'.length ∧
      CoTrace.prepend tr σ = CoTrace.prepend tr' σ' ∧ inv b tr' ∧ (loop b).Runs σ' := by
    intro n
    induction n with
    | zero => exact ⟨init, tr, σ, Nat.zero_le _, rfl, hI, hσ⟩
    | succ n ih =>
      obtain ⟨b, tr', σ', hn, hS, hI', hσ'⟩ := ih
      obtain ⟨b', l, σ'', rfl, hl, hI'', hσ''⟩ := hnext b tr' σ' hI' hσ' (hS ▸ hΩ)
      refine ⟨b', tr' ++ l, σ'', ?_, by rw [hS, CoTrace.prepend_append], hI'', hσ''⟩
      simp only [List.length_append]; omega
  refine hΩ (live _ fun n => ?_)
  obtain ⟨b, tr', σ', hn, hS, hI', -⟩ := rounds n
  exact ⟨tr'.length, hn, b, by rwa [hS, CoTrace.prepend, CoList.take_prepend]⟩

end ITree

end
