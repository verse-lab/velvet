
import Lean

open Lean Elab Command Term Meta Lean.Parser

def _root_.Lean.EnvExtension.set (ext : EnvExtension σ) (s : σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

def _root_.Lean.EnvExtension.modify (ext : EnvExtension σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

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
