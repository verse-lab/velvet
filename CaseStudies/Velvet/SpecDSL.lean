import Lean
import Loom.MonadAlgebras.WP.Attr

open Lean Elab Command Term Meta
open Lean.Parser.Command

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

-- Helper to get environment extension state
private def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ) [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

-- Helper to modify environment extension state
private def _root_.Lean.EnvExtension.modify [Inhabited σ] (ext : EnvExtension σ) [MonadEnv m] (s : σ -> σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · s)

-- Check if we're currently in a Specs section
def inSpecsSection {m} [Monad m] [MonadEnv m] : m Bool := do
  specsSect.get

-- Command to register a forbidden function
elab "register_specdef_forbidden" id:ident : command => do
  let name := id.getId
  forbiddenFunctions.modify (name :: ·)

-- Command to enable recursion checking in specdef sections
elab "register_specdef_allow_recursion" : command => do
  forbidRecursion.modify (fun _ => false)

-- Check if a term contains any forbidden function
partial def containsForbiddenFunction (forbidden : List Name) (stx : Syntax) : Option Name :=
  match stx with
  | Syntax.node _ _ args =>
    -- Check if this node is a forbidden function
    if let some found := forbidden.find? (fun n => stx.isOfKind n) then
      some found
    else
      -- Recursively check all arguments
      args.findSome? (containsForbiddenFunction forbidden)
  | Syntax.ident _ _ val _ =>
    -- Check if this identifier is forbidden
    forbidden.find? (fun n => val == n)
  | _ => none

-- Check if a term contains sorry
partial def containsSorry (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node _ _ args =>
    -- Check if this is sorry
    if stx.isOfKind ``Lean.Parser.Term.sorry then
      true
    else
      -- Recursively check all arguments
      args.any containsSorry
  | Syntax.ident _ _ val _ =>
    val == `sorry
  | _ => false

-- Check if a term contains admitted (usually in tactic proofs)
partial def containsAdmitted (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node _ _ args =>
    -- Recursively check all arguments
    args.any containsAdmitted
  | Syntax.ident _ _ val _ =>
    val == `admitted
  | _ => false

-- Check if a term contains 'let rec' (recursive let binding)
partial def containsLetRec (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node _ _ args =>
    -- Check if this is a let rec
    if stx.isOfKind `Lean.Parser.Term.letrec then
      true
    else
      -- Recursively check all arguments
      args.any containsLetRec
  | _ => false

-- Check if a term contains a reference to a specific name (for recursion detection)
partial def containsReference (targetName : Name) (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node _ _ args =>
    -- Recursively check all arguments
    args.any (containsReference targetName)
  | Syntax.ident _ _ val _ =>
    val == targetName
  | _ => false

-- Extract parameter name from a bracketed binder
def getBinderIdent (binder : Syntax) : CommandElabM Ident := do
  match binder with
  | `(bracketedBinder| ($id:ident : $_)) => return id
  | `(bracketedBinder| {$id:ident : $_}) => return id
  | `(bracketedBinder| [$id:ident : $_]) => return id
  | _ => throwErrorAt binder "Unsupported binder syntax"

-- Check if two binders have the same identifier and type
def bindersMatch (b1 b2 : Syntax) : CommandElabM Bool := do
  -- For simplicity, we compare the syntax directly
  return b1 == b2

-- Intercept section command to detect "section Specs"
@[command_elab «section»] def elabSectionSpecs : CommandElab := fun stx => do
  -- First try to handle Specs section
  match stx with
  | `(section $id:ident) =>
    let sectName := id.getId
    if sectName == `Specs then
      -- Entering a Specs section
      specsSect.modify (fun _ => true)
      prePostState.modify (fun _ => none)  -- Reset pre/post state for new section
    -- Call the builtin section elaborator
    Lean.Elab.Command.elabSection stx
  | _ =>
    -- Fallback to default section elaborator
    Lean.Elab.Command.elabSection stx

-- Intercept end command to detect "end Specs"
@[command_elab «end»] def elabEndSpecs : CommandElab := fun stx => do
  -- First check if we're exiting a Specs section
  match stx with
  | `(end $id:ident) =>
    let sectName := id.getId
    let inSpecs <- inSpecsSection
    if inSpecs && sectName == `Specs then
      -- Exiting a Specs section, check that both precondition and postcondition are defined
      let state <- prePostState.get
      match state with
      | none => throwError "Specs section must contain both def precondition and def postcondition"
      | some info =>
        unless info.hasPrecondition do
          throwError "Specs section must contain def precondition"
        unless info.hasPostcondition do
          throwError "Specs section must contain def postcondition"

      specsSect.modify (fun _ => false)
      prePostState.modify (fun _ => none)  -- Clear state when exiting
    -- Call the builtin end elaborator
    Lean.Elab.Command.elabEnd stx
  | _ =>
    -- Fallback to default end elaborator
    Lean.Elab.Command.elabEnd stx

-- Apply common restrictions for Specs sections
def checkSpecsRestrictions (stx : Syntax) (defName : Option Name := none) : CommandElabM Unit := do
  -- Check for sorry
  if containsSorry stx then
    throwErrorAt stx "sorry is not allowed in Specs sections"

  -- Check for admitted
  if containsAdmitted stx then
    throwErrorAt stx "admitted is not allowed in Specs sections"

  -- Check for forbidden functions
  let forbidden <- forbiddenFunctions.get
  if let some forbiddenName := containsForbiddenFunction forbidden stx then
    throwErrorAt stx s!"'{forbiddenName}' is not allowed in Specs sections"

  -- Check for let rec if recursion is forbidden
  let forbidRec <- forbidRecursion.get
  if forbidRec && containsLetRec stx then
    throwErrorAt stx "'let rec' (recursive let binding) is not allowed in Specs sections"

  -- Check for recursion if forbidden and defName is provided
  if let some name := defName then
    if forbidRec && containsReference name stx then
      throwErrorAt stx s!"recursive function '{name}' is not allowed in Specs sections"

-- Intercept all declarations to add restrictions in Specs sections
elab dec:declaration : command => do
  -- Check if we're in a Specs section
  let inSpecs <- inSpecsSection

  if inSpecs then
    -- Apply common restrictions first
    checkSpecsRestrictions dec.raw

    -- Check if this is a precondition or postcondition definition
    match dec with
    | `(command| $[$_:docComment]? $[$_:attributes]? $[$_:visibility]? def $id:ident $params* $[: $ty]? := $val:term) =>
      let defName := id.getId

      if defName == `precondition then
        -- Handle precondition definition
        let state <- prePostState.get
        if let some info := state then
          if info.hasPrecondition then
            throwError "precondition already defined in this Specs section"

        -- Update state
        let newInfo : PrePostInfo := {
          preParams := params
          postParams := state.map (·.postParams) |>.getD #[]
          postReturnParam := state.map (·.postReturnParam) |>.getD (← `(bracketedBinder| (dummy : Unit)))
          hasPrecondition := true
          hasPostcondition := state.map (·.hasPostcondition) |>.getD false
        }
        prePostState.modify (fun _ => some newInfo)

        -- Elaborate with loomAbstractionSimp attribute
        let defStx <- `(command| @[loomAbstractionSimp] def $id $params* $[: $ty]? := $val)
        elabCommand defStx
        return

      else if defName == `postcondition then
        -- Handle postcondition definition
        let state <- prePostState.get
        if let some info := state then
          if info.hasPostcondition then
            throwError "postcondition already defined in this Specs section"

        -- Check if precondition exists
        let some info := state | throwError "precondition must be defined before postcondition"
        unless info.hasPrecondition do
          throwError "precondition must be defined before postcondition"

        -- Check parameter consistency
        let preParamCount := info.preParams.size
        if params.size <= preParamCount then
          throwError s!"postcondition must have more parameters than precondition (expected at least {preParamCount + 1}, got {params.size})"

        -- Check that first parameters match precondition
        for i in [:preParamCount] do
          let isMatch <- bindersMatch info.preParams[i]! params[i]!
          unless isMatch do
            throwErrorAt params[i]! s!"Parameter {i} of postcondition must match parameter {i} of precondition"

        -- The last parameter is the return value
        let returnParam := params[params.size - 1]!

        -- Update state
        let newInfo : PrePostInfo := {
          preParams := info.preParams
          postParams := params
          postReturnParam := returnParam
          hasPrecondition := true
          hasPostcondition := true
        }
        prePostState.modify (fun _ => some newInfo)

        -- Elaborate with loomAbstractionSimp attribute
        let defStx <- `(command| @[loomAbstractionSimp] def $id $params* $[: $ty]? := $val)
        elabCommand defStx
        return

      else
        -- Regular definition in Specs section
        -- Check for recursion (not checked by common restrictions without defName)
        checkSpecsRestrictions val.raw (some defName)

        -- Elaborate normally, then add attribute
        elabCommand dec
        let attrCmd <- `(command| attribute [loomAbstractionSimp] $id)
        elabCommand attrCmd
        return

    | `(command| $[$_:docComment]? $[$_:attributes]? $[$_:visibility]? axiom $id:ident : $_) =>
      -- Axiom is not allowed in Specs sections
      throwErrorAt id "axiom is not allowed in Specs sections"

    | `(command| $[$_:docComment]? $[$_:attributes]? $[$_:visibility]? theorem $id:ident $_ := $_) =>
      -- Elaborate normally, then add attribute
      elabCommand dec
      let attrCmd <- `(command| attribute [loomAbstractionSimp] $id)
      elabCommand attrCmd
      return

    | _ =>
      -- Other declarations, already checked by common restrictions
      pure ()

  -- Elaborate the declaration normally (checks passed or not in Specs section)
  elabCommand dec
