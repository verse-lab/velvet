module

public import Velvet.Core.NonDet.Defs
public import Velvet.Core.NonDet.Findable
public import Velvet.Core.NonDet.Run
public import Velvet.Core.NonDet.WP
public import Velvet.Core.Loop.Gadgets
public import Std.WP

open Lean.Order
open Std.WP

universe u v w z

@[expose] public section

/-- Inductive certificate witnessing that non-deterministic choices in `s`
are backed by sound runtime finders. -/
public inductive ExtractNonDet {mode : NondetMode} {m : Type u → Type v} : {α : Type u} → NonDetT mode m α → Prop where
  | pure {α : Type u} (x : α) : ExtractNonDet (.pure x)
  | vis {α β : Type u} (x : m β) (f : β → NonDetT mode m α) :
      (∀ y, ExtractNonDet (f y)) → ExtractNonDet (.vis x f)
  | pickCont {α τ : Type u} (p : τ → Prop) (find : Unit → Option τ)
      (hsound : ∀ x, find () = some x → p x)
      (f : τ → NonDetT mode m α) :
      (∀ t, ExtractNonDet (f t)) → ExtractNonDet (.pickCont τ p find f)
  | repeatCont {α β : Type u} (init : β) (f : β → NonDetT mode m (ForInStep β))
      (cont : β → NonDetT mode m α) :
      (∀ b, ExtractNonDet (f b)) → (∀ b, ExtractNonDet (cont b)) →
      ExtractNonDet (.repeatCont init f cont)

/-- Inductive certificate for loop-free non-deterministic computations.
Any loop-free computation equipped with sound finders unconditionally satisfies
the extraction soundness theorems (`extract_refines_wp`, `extract_refines`). -/
public inductive ExtractLoopFree {mode : NondetMode} {m : Type u → Type v} : {α : Type u} → NonDetT mode m α → Prop where
  | pure {α : Type u} (x : α) : ExtractLoopFree (.pure x)
  | vis {α β : Type u} (x : m β) (f : β → NonDetT mode m α) :
      (∀ y, ExtractLoopFree (f y)) → ExtractLoopFree (.vis x f)
  | pickCont {α τ : Type u} (p : τ → Prop) (find : Unit → Option τ)
      (hsound : ∀ x, find () = some x → p x)
      (f : τ → NonDetT mode m α) :
      (∀ t, ExtractLoopFree (f t)) → ExtractLoopFree (.pickCont τ p find f)

public theorem ExtractLoopFree.toExtractNonDet {mode : NondetMode} {m : Type u → Type v} {α : Type u}
    {s : NonDetT mode m α} (h : ExtractLoopFree s) : ExtractNonDet s := by
  induction h with
  | pure x => exact ExtractNonDet.pure x
  | vis x f _ ih => exact ExtractNonDet.vis x f ih
  | pickCont p find hsound f _ ih => exact ExtractNonDet.pickCont p find hsound f ih

namespace ExtractLoopFree

public theorem pick {mode : NondetMode} {m : Type u → Type v} (τ : Type u) [Inhabited τ] :
    ExtractLoopFree (mode := mode) (m := m) (NonDetT.pick (mode := mode) (m := m) τ) := by
  dsimp [NonDetT.pick]
  refine ExtractLoopFree.pickCont (fun _ => True) (fun _ => some default) ?_ NonDetT.pure (fun _ => ExtractLoopFree.pure _)
  intros; trivial

public theorem assume {mode : NondetMode} {m : Type u → Type v} (as : Prop) [Decidable as] :
    ExtractLoopFree (mode := mode) (m := m) (NonDetT.assume (mode := mode) (m := m) as) := by
  dsimp [NonDetT.assume]
  refine ExtractLoopFree.pickCont (fun _ => as) _ ?_ _ (fun _ => ExtractLoopFree.pure _)
  intro x hx
  exact WeakFindable.find_some_p (p := fun (_ : PUnit) => as) hx

set_option linter.unusedVariables false in
public theorem pickSuchThat (mode : NondetMode) (m : Type u → Type v)
    (τ : Type u) (p : τ → Prop) [wf : WeakFindable p] (name : Lean.Name := .anonymous) :
    ExtractLoopFree (mode := mode) (m := m) (NonDetT.pickCont τ p wf.find NonDetT.pure) := by
  refine ExtractLoopFree.pickCont p wf.find (fun x hx => wf.find_some_p hx) NonDetT.pure (fun _ => ExtractLoopFree.pure _)

public theorem bind {mode : NondetMode} {m : Type u → Type v} {α β : Type u}
    (x : NonDetT mode m α) (f : α → NonDetT mode m β)
    (hx : ExtractLoopFree x) (hf : ∀ a, ExtractLoopFree (f a)) :
    ExtractLoopFree (x >>= f) := by
  induction x generalizing β with
  | pure a => exact hf a
  | vis c g ih =>
    cases hx with
    | vis _ _ hg =>
      change ExtractLoopFree (NonDetT.vis c (fun y => g y >>= f))
      exact ExtractLoopFree.vis c _ (fun y => ih y f (hg y) hf)
  | pickCont τ p find g ih =>
    cases hx with
    | pickCont _ _ hsound _ hg =>
      change ExtractLoopFree (NonDetT.pickCont _ p find (fun t => g t >>= f))
      exact ExtractLoopFree.pickCont p find hsound _ (fun t => ih t f (hg t) hf)
  | repeatCont =>
    cases hx

end ExtractLoopFree

namespace ExtractNonDet

public theorem pick {mode : NondetMode} {m : Type u → Type v} (τ : Type u) [Inhabited τ] :
    ExtractNonDet (mode := mode) (m := m) (NonDetT.pick (mode := mode) (m := m) τ) := by
  dsimp [NonDetT.pick]
  refine ExtractNonDet.pickCont (fun _ => True) (fun _ => some default) ?_ NonDetT.pure (fun _ => ExtractNonDet.pure _)
  intros; trivial

public theorem assume {mode : NondetMode} {m : Type u → Type v} (as : Prop) [Decidable as] :
    ExtractNonDet (mode := mode) (m := m) (NonDetT.assume (mode := mode) (m := m) as) := by
  dsimp [NonDetT.assume]
  refine ExtractNonDet.pickCont (fun _ => as) _ ?_ _ (fun _ => ExtractNonDet.pure _)
  intro x hx
  exact WeakFindable.find_some_p (p := fun (_ : PUnit) => as) hx

set_option linter.unusedVariables false in
public theorem pickSuchThat (mode : NondetMode) (m : Type u → Type v)
    (τ : Type u) (p : τ → Prop) [wf : WeakFindable p] (name : Lean.Name := .anonymous) :
    ExtractNonDet (mode := mode) (m := m) (NonDetT.pickCont τ p wf.find NonDetT.pure) := by
  refine ExtractNonDet.pickCont p wf.find (fun x hx => wf.find_some_p hx) NonDetT.pure (fun _ => ExtractNonDet.pure _)

public theorem «repeat» {mode : NondetMode} {m : Type u → Type v} {α : Type u}
    (init : α) (f : α → NonDetT mode m (ForInStep α))
    (hf : ∀ a, ExtractNonDet (f a)) :
    ExtractNonDet (NonDetT.repeat init f) :=
  ExtractNonDet.repeatCont init f NonDetT.pure hf (fun _ => ExtractNonDet.pure _)

public theorem bind {mode : NondetMode} {m : Type u → Type v} {α β : Type u}
    (x : NonDetT mode m α) (f : α → NonDetT mode m β)
    (hx : ExtractNonDet x) (hf : ∀ a, ExtractNonDet (f a)) :
    ExtractNonDet (x >>= f) := by
  induction x generalizing β with
  | pure a => exact hf a
  | vis c g ih =>
    cases hx with
    | vis _ _ hg =>
      change ExtractNonDet (NonDetT.vis c (fun y => g y >>= f))
      exact ExtractNonDet.vis c _ (fun y => ih y f (hg y) hf)
  | pickCont τ p find g ih =>
    cases hx with
    | pickCont _ _ hsound _ hg =>
      change ExtractNonDet (NonDetT.pickCont _ p find (fun t => g t >>= f))
      exact ExtractNonDet.pickCont p find hsound _ (fun t => ih t f (hg t) hf)
  | repeatCont init g cont _ ih_cont =>
    cases hx with
    | repeatCont _ _ _ hg hcont =>
      change ExtractNonDet (NonDetT.repeatCont init g (fun t => cont t >>= f))
      exact ExtractNonDet.repeatCont init g _ hg (fun t => ih_cont t f (hcont t) hf)

end ExtractNonDet

namespace DemonicChoice

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
variable [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- Soundness of demonic execution on WP: demonic choices universally over-approximate
concrete execution, so any deterministic execution refines the demonic specification. -/
public theorem extract_refines_wp {α : Type u}
    {s : DemonicT m α} (ex : ExtractLoopFree s)
    (post : α → Pred) (epost : EPred)
    (hbot : (⊤ : Pred) ⊑ Std.WP.wp (CCPOBot.compBot (m := m) (α := α)) post epost) :
    NonDetT.wp s post epost ⊑ Std.WP.wp s.run post epost := by
  induction ex with
  | pure x =>
    simp only [NonDetT.run_pure, NonDetT.wp]
    exact WPMonad.pure_le_wp_pure x post epost
  | vis c f _ ih =>
    simp only [NonDetT.run_vis, NonDetT.wp]
    have hmono : Std.WP.wp c (fun b => NonDetT.wp (f b) post epost) epost ⊑
                 Std.WP.wp c (fun b => Std.WP.wp (f b).run post epost) epost := by
      apply WP.wp_trans_monotone c
      · exact PartialOrder.rel_refl
      · intro b
        exact ih b
    exact PartialOrder.rel_trans hmono (WPMonad.bind_le_wp_bind c (fun b => (f b).run) post epost)
  | pickCont p find hsound f _ ih =>
    simp only [NonDetT.run_pickCont, NonDetT.wp, choice_demonic]
    split
    · exact PartialOrder.rel_trans (le_top _) hbot
    · rename_i x hx
      have hp : p x := hsound x hx
      refine PartialOrder.rel_trans ?_ (ih x)
      exact iInf_le (α := Pred) (i := (⟨x, hp⟩ : { a // p a })) (fun a => NonDetT.wp (f a.val) post epost)

/-- Demonic execution refines Hoare triples: if `s` satisfies `Triple s pre post epost`,
then its concrete deterministic execution `s.run` also satisfies `Triple s.run pre post epost`. -/
public theorem extract_refines {α : Type u}
    {s : DemonicT m α} (ex : ExtractLoopFree s)
    {pre : Pred} {post : α → Pred} {epost : EPred}
    (hbot : (⊤ : Pred) ⊑ Std.WP.wp (CCPOBot.compBot (m := m) (α := α)) post epost) :
    Triple s pre post epost →
    Triple s.run pre post epost := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans tr.le_wp (extract_refines_wp ex post epost hbot))

/-- Specialized demonic soundness for `Option` under partial correctness (`epost = fun _ => True`). -/
public theorem extract_refines_wp_option {α : Type}
    {s : DemonicT Option α} (ex : ExtractLoopFree s)
    (post : α → Prop) :
    NonDetT.wp s post (fun _ => True) ⊑
      Std.WP.wp (Prog := Option α) s.run post (fun _ => True) := by
  apply extract_refines_wp (epost := fun _ => True) ex post
  dsimp [CCPOBot.compBot]
  intro _; trivial

/-- Specialized Hoare triple demonic soundness for `Option` under partial correctness. -/
public theorem extract_refines_option {α : Type}
    {s : DemonicT Option α} (ex : ExtractLoopFree s)
    {pre : Prop} {post : α → Prop} :
    Triple (Prog := DemonicT Option α) s pre post (fun _ => True) →
    Triple (Prog := Option α) s.run pre post (fun _ => True) := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans (α := Prop) tr.le_wp (extract_refines_wp_option ex post))

end DemonicChoice

namespace AngelicChoice

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
variable [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- Soundness of angelic execution on WP: a successful concrete run provides a witness
for an angelic existential choice, so execution soundly refines the angelic specification. -/
public theorem extract_refines_wp {α : Type u}
    {s : AngelicT m α} (ex : ExtractLoopFree s)
    (post : α → Pred) (epost : EPred)
    (hpure : ∀ (x : α), Std.WP.wp (Pure.pure (f := m) x) post epost ⊑ post x)
    (hbind : ∀ {β : Type u} (c : m β) (g : β → m α),
      Std.WP.wp (c >>= g) post epost ⊑ Std.WP.wp c (fun b => Std.WP.wp (g b) post epost) epost)
    (hbot : Std.WP.wp (CCPOBot.compBot (m := m) (α := α)) post epost ⊑ ⊥) :
    Std.WP.wp s.run post epost ⊑ NonDetT.wp s post epost := by
  induction ex with
  | pure x =>
    simp only [NonDetT.run_pure, NonDetT.wp]
    exact hpure x
  | vis c f _ ih =>
    simp only [NonDetT.run_vis, NonDetT.wp]
    refine PartialOrder.rel_trans (hbind c (fun b => (f b).run)) ?_
    apply WP.wp_trans_monotone c
    · exact PartialOrder.rel_refl
    · intro b
      exact ih b
  | pickCont p find hsound f _ ih =>
    simp only [NonDetT.run_pickCont, NonDetT.wp, choice_angelic]
    split
    · exact PartialOrder.rel_trans hbot (bot_le _)
    · rename_i x hx
      have hp : p x := hsound x hx
      refine PartialOrder.rel_trans (ih x) ?_
      exact le_iSup (α := Pred) (i := (⟨x, hp⟩ : { a // p a })) (fun a => NonDetT.wp (f a.val) post epost)

/-- Angelic execution refines Hoare triples: if the concrete execution `s.run` satisfies
the postcondition, then the angelic non-deterministic program `s` is correct. -/
public theorem extract_refines {α : Type u}
    {s : AngelicT m α} (ex : ExtractLoopFree s)
    {pre : Pred} {post : α → Pred} {epost : EPred}
    (hpure : ∀ (x : α), Std.WP.wp (Pure.pure (f := m) x) post epost ⊑ post x)
    (hbind : ∀ {β : Type u} (c : m β) (g : β → m α),
      Std.WP.wp (c >>= g) post epost ⊑ Std.WP.wp c (fun b => Std.WP.wp (g b) post epost) epost)
    (hbot : Std.WP.wp (CCPOBot.compBot (m := m) (α := α)) post epost ⊑ ⊥) :
    Triple s.run pre post epost →
    Triple s pre post epost := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans tr.le_wp (extract_refines_wp ex post epost hpure hbind hbot))

/-- Specialized angelic soundness for `Option` under total correctness (`epost = fun _ => False`). -/
public theorem extract_refines_wp_option {α : Type}
    {s : AngelicT Option α} (ex : ExtractLoopFree s)
    (post : α → Prop) :
    Std.WP.wp (Prog := Option α) s.run post (fun _ => False) ⊑
      NonDetT.wp s post (fun _ => False) := by
  apply extract_refines_wp (epost := fun _ => False) ex post
  · intro x; rfl
  · intro β c g; cases c <;> rfl
  · dsimp [CCPOBot.compBot]
    intro h; contradiction

/-- Specialized Hoare triple angelic soundness for `Option` under total correctness. -/
public theorem extract_refines_option {α : Type}
    {s : AngelicT Option α} (ex : ExtractLoopFree s)
    {pre : Prop} {post : α → Prop} :
    Triple (Prog := Option α) s.run pre post (fun _ => False) →
    Triple (Prog := AngelicT Option α) s pre post (fun _ => False) := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans (α := Prop) tr.le_wp (extract_refines_wp_option ex post))

end AngelicChoice

end

