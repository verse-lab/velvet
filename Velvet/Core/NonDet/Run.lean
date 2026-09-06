module

public import Velvet.Core.NonDet.Defs

universe u v

@[expose] public section

/-- Typeclass providing a computable bottom / divergent element for execution.
When a non-deterministic choice fails to find a valid witness, execution
diverges / fails using `CCPOBot.compBot`. -/
public class CCPOBot (m : Type u → Type v) where
  compBot {α : Type u} : m α

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
using their `Findable` witnesses. If a choice predicate is empty, returns bottom.

This acts as the canonical ITree / Freer effect handler, interpreting:
- `.pure x`: to `Pure.pure x`
- `.vis x f`: by executing base effect `x` in `m` and continuing with handler `f`
- `.pickCont`: by querying the runtime witness finder `find ()`
- `.repeatCont`: by running loop iterations in `m`
-/
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

end
