
import Lean

open Lean Elab Command Term Meta Lean.Parser

abbrev LocMutVarsCtx := Array (Nat × Ident)

initialize localMutVarsCtx :
  SimpleScopedEnvExtension (Nat × Ident) LocMutVarsCtx <-
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s id => s.push id
  }

abbrev GlobalMutVarsCtx := Std.HashMap Name LocMutVarsCtx

initialize globalMutVarsCtx :
  SimpleScopedEnvExtension (Name × LocMutVarsCtx) GlobalMutVarsCtx <-
  registerSimpleScopedEnvExtension {
    initial := ∅
    addEntry := fun s (n, ids) => s.insert n ids
  }

initialize
  registerTraceClass `Loom.debug
