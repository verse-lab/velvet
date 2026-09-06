module

public import Velvet.Core.NonDet.Defs
public import Velvet.Core.NonDet.Findable
public import Velvet.Core.NonDet.WP
public import Velvet.Core.Loop.Gadgets
public import Std.WP

open Lean.Order
open Std.WP

universe u v w z

@[expose] public section

/-- Typeclass providing a computable bottom / divergent element for execution. -/
public class CCPOBot (m : Type u → Type v) where
  compBot {α : Type u} : m α

/-- Lawfulness stating that `CCPOBot.compBot` matches the mathematical `Lean.Order.bot`. -/
public class CCPOBotLawful (m : Type u → Type v) [∀ α, CCPO (m α)] [CCPOBot m] : Prop where
  prop {α : Type u} : CCPOBot.compBot (m := m) (α := α) = Lean.Order.bot

public instance : CCPOBot Option where
  compBot := none

public instance [CCPOBot m] : CCPOBot (ReaderT ρ m) where
  compBot := fun _ => CCPOBot.compBot

public instance [CCPOBot m] : CCPOBot (StateT σ m) where
  compBot := fun _ => CCPOBot.compBot

public instance [CCPOBot m] : CCPOBot (ExceptT ε m) where
  compBot := ExceptT.mk CCPOBot.compBot

namespace NonDetT

/-- Execute a non-deterministic computation by resolving non-deterministic choices
using their `Findable` witnesses. If a choice predicate is empty, returns bottom. -/
public def run {mode : NondetMode} {m : Type u → Type v} [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
    {α : Type u} : NonDetT mode m α → m α
  | .pure x => Pure.pure x
  | .vis x f => x >>= (fun y => (f y).run)
  | .pickCont _ _ find f =>
    match find () with
    | none => CCPOBot.compBot
    | some x => (f x).run
  | .repeatCont init f cont =>
    forIn Lean.Loop.mk init (fun _ x => (f x).run) >>= (fun x => (cont x).run)

@[simp]
public theorem run_pure {mode : NondetMode} {m : Type u → Type v} [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
    {α : Type u} (x : α) :
    (NonDetT.pure (mode := mode) (m := m) x).run = Pure.pure x := by
  rw [NonDetT.run]

@[simp]
public theorem run_vis {mode : NondetMode} {m : Type u → Type v} [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
    {α β : Type u} (x : m β) (f : β → NonDetT mode m α) :
    (NonDetT.vis x f).run = x >>= (fun y => (f y).run) := by
  rw [NonDetT.run]

@[simp]
public theorem run_pickCont {mode : NondetMode} {m : Type u → Type v} [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
    {α τ : Type u} (p : τ → Prop) (find : Unit → Option τ) (f : τ → NonDetT mode m α) :
    (NonDetT.pickCont τ p find f).run =
      match find () with
      | none => CCPOBot.compBot
      | some x => (f x).run := by
  rw [NonDetT.run]

@[simp]
public theorem run_repeatCont {mode : NondetMode} {m : Type u → Type v} [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
    {α β : Type u} (init : β) (f : β → NonDetT mode m (ForInStep β)) (cont : β → NonDetT mode m α) :
    (NonDetT.repeatCont init f cont).run =
      forIn Lean.Loop.mk init (fun _ x => (f x).run) >>= (fun x => (cont x).run) := by
  rw [NonDetT.run]

end NonDetT

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
  by_cases has : as
  · exact has
  · simp [has] at hx

set_option linter.unusedVariables false in
public theorem pickSuchThat (mode : NondetMode) (m : Type u → Type v)
    (τ : Type u) (p : τ → Prop) [wf : WeakFindable p] (name : Lean.Name := .anonymous) :
    ExtractNonDet (mode := mode) (m := m) (NonDetT.pickCont τ p wf.find NonDetT.pure) := by
  refine ExtractNonDet.pickCont p wf.find (fun x hx => wf.find_some_p hx) NonDetT.pure (fun _ => ExtractNonDet.pure _)

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
  | repeatCont =>
    cases hx

end ExtractNonDet

namespace DemonicChoice

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable [Monad m] [CCPOBot m] [ForIn m Lean.Loop Unit]
variable [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- Soundness of demonic execution on WP: demonic choices universally over-approximate
concrete execution, so any deterministic execution refines the demonic specification. -/
public theorem extract_refines_wp {α : Type u}
    {s : DemonicT m α} (ex : ExtractNonDet s)
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
    {s : DemonicT m α} (ex : ExtractNonDet s)
    {pre : Pred} {post : α → Pred} {epost : EPred}
    (hbot : (⊤ : Pred) ⊑ Std.WP.wp (CCPOBot.compBot (m := m) (α := α)) post epost) :
    Triple s pre post epost →
    Triple s.run pre post epost := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans tr.le_wp (extract_refines_wp ex post epost hbot))

/-- Specialized demonic soundness for `Option` under partial correctness (`epost = fun _ => True`). -/
public theorem extract_refines_wp_option {α : Type}
    {s : DemonicT Option α} (ex : ExtractNonDet s)
    (post : α → Prop) :
    NonDetT.wp s post (fun _ => True) ⊑
      Std.WP.wp (Prog := Option α) s.run post (fun _ => True) := by
  apply extract_refines_wp (epost := fun _ => True) ex post
  dsimp [CCPOBot.compBot]
  intro _; trivial

/-- Specialized Hoare triple demonic soundness for `Option` under partial correctness. -/
public theorem extract_refines_option {α : Type}
    {s : DemonicT Option α} (ex : ExtractNonDet s)
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
    {s : AngelicT m α} (ex : ExtractNonDet s)
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
    {s : AngelicT m α} (ex : ExtractNonDet s)
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
    {s : AngelicT Option α} (ex : ExtractNonDet s)
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
    {s : AngelicT Option α} (ex : ExtractNonDet s)
    {pre : Prop} {post : α → Prop} :
    Triple (Prog := Option α) s.run pre post (fun _ => False) →
    Triple (Prog := AngelicT Option α) s pre post (fun _ => False) := by
  intro tr
  exact Triple.intro (PartialOrder.rel_trans (α := Prop) tr.le_wp (extract_refines_wp_option ex post))

end AngelicChoice

end

