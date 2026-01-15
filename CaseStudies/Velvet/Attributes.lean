import Lean
import Lean.Parser.Command

open Lean Elab Command Parser Meta

def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

-- Helper to get environment extension state
def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ) [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

-- Helper to modify environment extension state
def _root_.Lean.EnvExtension.modify [Inhabited σ] (ext : EnvExtension σ) [MonadEnv m] (s : σ -> σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · s)

abbrev Names := Array Name

initialize velvetSpecHelpers: SimpleScopedEnvExtension Name Names ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s' a => s'.push a
  }

syntax (name:= velvetSpecHelper) "velvetSpecHelper" : attr

initialize registerBuiltinAttribute {
  name := `velvetSpecHelper
  descr := "This is a velvet specification helper"
  add := fun declName _ _ => do
    velvetSpecHelpers.modify (·.push declName)
}

initialize allowedSymbols: SimpleScopedEnvExtension Name Names ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s' a => s'.push a
  }

syntax (name:= allowedSymbol) "allowedSymbol" : attr

initialize registerBuiltinAttribute {
  name := `allowedSymbol
  descr := "This symbol is allowed for use in velvet specifications"
  add := fun declName _ _ => do 
    allowedSymbols.modify (·.push declName)
}


-- List of forbidden function names that cannot be used in specdef sections
abbrev ForbiddenFunctionsState := List Name

-- Environment extension to track forbidden functions
initialize forbiddenFunctions : EnvExtension ForbiddenFunctionsState ←
  registerEnvExtension (pure [])

-- State to track whether recursion is forbidden in specdef sections
abbrev ForbidRecursionState := Bool

-- Environment extension to track whether recursion is forbidden
initialize forbidRecursion : EnvExtension ForbidRecursionState ←
  registerEnvExtension (pure true)

-- State to track whether we're in a Specs section
abbrev SpecsSectExtState := Bool

-- Environment extension to track active Specs section
initialize specsSect : EnvExtension SpecsSectExtState ←
  registerEnvExtension (pure false)

-- Structure to track precondition and postcondition information
structure PrePostInfo where
  preParams : Array Syntax  -- Parameters of precondition
  postParams : Array Syntax -- Parameters of postcondition
  postReturnParam : Syntax  -- The return value parameter
  hasPrecondition : Bool := false
  hasPostcondition : Bool := false

-- State to track precondition and postcondition per section
abbrev PrePostState := Option PrePostInfo

-- Environment extension to track precondition/postcondition
initialize prePostState : EnvExtension PrePostState ←
  registerEnvExtension (pure none)

-- State to track function names that need attributes added at end of Specs section
abbrev PendingAttrsState := List Name

-- Environment extension to track pending attribute additions
initialize pendingAttrs : EnvExtension PendingAttrsState ←
  registerEnvExtension (pure [])

