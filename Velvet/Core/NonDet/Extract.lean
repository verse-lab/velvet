module

public import Velvet.Core.NonDet.Defs
public import Velvet.Core.Loop.Gadgets

open Lean.Order

universe u v w

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

end NonDetT

end

