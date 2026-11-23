import Velvet.Examples.ITree.WP

/-!
# A ping server that never leaves a ping unanswered

A terminal program, as an interaction tree over two events: read a line, print a line. It answers
every `ping` with `pong`, ignores other lines, and stops at `quit`; as long as no `quit` comes, it
runs forever.

The method's contract says: in every run, every `ping` is eventually followed by a `pong`. The
`ensures` clause covers the runs that stop (the final trace), the `signals` clause the ones that go
on forever (the infinite trace), and no run hangs silently. The loop invariant is "every ping so
far has been answered"; `ITree.whileLoopPartial_live` lifts it to the infinite trace.
-/

open Std.WP Lean.Order

noncomputable section

/-! ## The property -/

/-- Terminal events: read a line, print a line. -/
inductive Term : Type → Type
  | getLine : Term String
  | putLine (s : String) : Term Unit

/-- The user typed `ping`. -/
def Event.IsPing : Event Term → Prop
  | ⟨.getLine, s⟩ => s = "ping"
  | _ => False

/-- The program printed `pong`. -/
def Event.IsPong : Event Term → Prop
  | ⟨.putLine s, _⟩ => s = "pong"
  | _ => False

/-- Every ping in the trace, finite or infinite, is followed later by a pong. -/
def PingsAnswered (σ : CoTrace Term) : Prop :=
  ∀ i ev, σ.get? i = some ev → ev.IsPing →
    ∃ j ev', i < j ∧ σ.get? j = some ev' ∧ ev'.IsPong

/-! ## The program -/

/-- Read a line from the terminal. -/
def getLine : ITree Term String := ITree.trigger .getLine

/-- Print a line to the terminal. -/
def putLine (s : String) : ITree Term Unit := ITree.trigger (.putLine s)

/-- Any line may be read, and the read is recorded in the trace. -/
@[spec] theorem getLine_spec (Q : String → Trace Term → Prop) :
    ⦃ fun tr => ∀ s, Q s (tr ++ [⟨.getLine, s⟩]) ⦄ getLine ⦃ Q ⦄ :=
  ITree.trigger_spec _ Q

/-- The print is recorded in the trace. -/
@[spec] theorem putLine_spec (s : String) (Q : Unit → Trace Term → Prop) :
    ⦃ fun tr => Q () (tr ++ [⟨.putLine s, ()⟩]) ⦄ putLine s ⦃ Q ⦄ :=
  Loop.triple_pre_le (fun _ h _ => h) (ITree.trigger_spec _ Q)

set_option velvet.semantics.termination "partial" in
/-- Answer every `ping` with `pong`, ignore other lines, stop at `quit`. -/
method pingServer returns (r : Unit) in ITree Term
  requires (tr : Trace Term) => tr = []
  signals (σ : CoTrace Term) => PingsAnswered σ
  ensures (tr : Trace Term) => PingsAnswered ↑tr
do
  while true
    invariant answered : (fun tr : Trace Term => PingsAnswered ↑tr)
  do
    let line ← getLine
    if line = "quit" then break
    if line = "ping" then putLine "pong"
  return ()

/-! ## The proof -/

/-- Spelled out for a finite trace. -/
theorem pingsAnswered_ofList {tr : Trace Term} :
    PingsAnswered ↑tr ↔ ∀ (i : Nat) (ev : Event Term), tr[i]? = some ev → ev.IsPing →
      ∃ j : Nat, ∃ ev' : Event Term, i < j ∧ tr[j]? = some ev' ∧ ev'.IsPong := by
  simp [PingsAnswered]

theorem PingsAnswered.nil : PingsAnswered ↑([] : Trace Term) := by
  intro i ev h; simp at h

/-- A round that reads a line other than `ping`. -/
theorem PingsAnswered.read {tr : Trace Term} {ev : Event Term} (h : PingsAnswered ↑tr)
    (hev : ¬ ev.IsPing) : PingsAnswered ↑(tr ++ [ev]) := by
  rw [pingsAnswered_ofList] at h ⊢
  intro i e hi hp
  rcases Nat.lt_or_ge i tr.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    obtain ⟨j, e', hij, hj, hp'⟩ := h i e hi hp
    have hjlt : j < tr.length := (List.getElem?_eq_some_iff.1 hj).1
    exact ⟨j, e', hij, by rwa [List.getElem?_append_left hjlt], hp'⟩
  · rw [List.getElem?_append_right hge] at hi
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hi
    simp only [List.length_cons, List.length_nil] at hlt
    have h0 : i - tr.length = 0 := by omega
    exact absurd (by simpa [h0] using hp) hev

/-- A round that reads `ping` and prints `pong`. -/
theorem PingsAnswered.ping {tr : Trace Term} {ev : Event Term} {u : Unit}
    (h : PingsAnswered ↑tr) :
    PingsAnswered ↑(tr ++ [ev] ++ [(⟨Term.putLine "pong", u⟩ : Event Term)]) := by
  have hpong : (⟨Term.putLine "pong", u⟩ : Event Term).IsPong := rfl
  rw [pingsAnswered_ofList] at h ⊢
  intro i e hi hp
  rw [List.append_assoc] at hi ⊢
  rcases Nat.lt_or_ge i tr.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    obtain ⟨j, e', hij, hj, hp'⟩ := h i e hi hp
    have hjlt : j < tr.length := (List.getElem?_eq_some_iff.1 hj).1
    exact ⟨j, e', hij, by rwa [List.getElem?_append_left hjlt], hp'⟩
  · rw [List.getElem?_append_right hge] at hi
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hi
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hlt
    obtain hi | hi : i - tr.length = 0 ∨ i - tr.length = 1 := by omega
    · refine ⟨tr.length + 1, _, by omega, ?_, hpong⟩
      rw [List.getElem?_append_right (by omega)]; simp
    · simp [hi, Event.IsPing] at hp

/-- The invariant at infinitely many prefixes gives the property of the whole trace. -/
theorem PingsAnswered.of_prefixes {σ : CoTrace Term} {inv : Unit → Trace Term → Prop}
    (hinv : ∀ b tr, inv b tr → PingsAnswered ↑tr)
    (h : ∀ n, ∃ m, n ≤ m ∧ ∃ b, inv b (σ.take m)) : PingsAnswered σ := by
  intro i ev hi hp
  obtain ⟨m, hm, b, h⟩ := h (i + 1)
  obtain ⟨j, ev', hij, hj, hp'⟩ :=
    hinv b _ h i ev (by simp [CoList.getElem?_take, hi]; omega) hp
  simp only [CoList.get?_ofList, CoList.getElem?_take] at hj
  split at hj
  · exact ⟨j, ev', hij, hj, hp'⟩
  · cases hj

prove_correct pingServer by
  velvet_vcgen [pingServer]
  all_goals try simp only [Named.mk_eq, ofProp_prop_eq] at *
  case signals1 =>
    exact PingsAnswered.of_prefixes (inv := fun _ tr => PingsAnswered ↑tr) (fun _ _ h => h) ‹_›
  all_goals grind [PingsAnswered.nil, PingsAnswered.read, PingsAnswered.ping, Event.IsPing]

/-! ## What the contract says

Unfolded through `ITree.Live`, the contract is a statement about the runs of the tree. -/

/-- Every infinite run answers every ping. -/
theorem pingServer_runs (σ : CoTrace Term) (h : pingServer.Runs σ) : PingsAnswered σ := by
  simpa [Named.mk_eq] using (ITree.live_of_triple pingServer.spec (tr := []) (by simp [Named.mk_eq])).infinite σ h

/-- Every run that stops (at `quit`) has answered every ping. -/
theorem pingServer_returns (l : Trace Term) (h : pingServer.Returns l ()) : PingsAnswered ↑l := by
  simpa [Named.mk_eq] using (ITree.live_of_triple pingServer.spec (tr := []) (by simp [Named.mk_eq])).finite l () h

/-- The server never hangs silently. -/
theorem pingServer_productive (l : Trace Term) : ¬ pingServer.Stalls l :=
  (ITree.live_of_triple pingServer.spec (tr := []) (by simp [Named.mk_eq])).productive l

end
