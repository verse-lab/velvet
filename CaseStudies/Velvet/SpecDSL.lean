import Lean

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

-- State to track whether we're in a specdef section
abbrev SpecDefSectExtState := List Name

-- Environment extension to track active specdef sections
initialize specDefSect : EnvExtension SpecDefSectExtState ←
  registerEnvExtension (pure [])

-- Structure to track def_pre and def_post information
structure PrePostInfo where
  preParams : Array Syntax  -- Parameters of def_pre
  postParams : Array Syntax -- Parameters of def_post
  postReturnParam : Syntax  -- The return value parameter
  hasDefPre : Bool := false
  hasDefPost : Bool := false

-- State to track def_pre and def_post per section
abbrev PrePostState := Option PrePostInfo

-- Environment extension to track pre/post conditions
initialize prePostState : EnvExtension PrePostState ←
  registerEnvExtension (pure none)

-- Helper to get environment extension state
private def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ) [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

-- Helper to modify environment extension state
private def _root_.Lean.EnvExtension.modify [Inhabited σ] (ext : EnvExtension σ) [MonadEnv m] (s : σ -> σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · s)

-- Check if we're currently in a specdef section
def inSpecDefSection {m} [Monad m] [MonadEnv m] : m Bool := do
  let state <- specDefSect.get
  return !state.isEmpty

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

-- Syntax for def_pre and def_post
syntax "def_pre" bracketedBinder* ":=" term : command
syntax "def_post" bracketedBinder* ":=" term : command

-- Elaborate def_pre
elab_rules : command
  | `(command| def_pre $params* := $body) => do
    let inSpecDef <- inSpecDefSection
    unless inSpecDef do
      throwError "def_pre can only be used inside a specdef section"

    -- Check if def_pre already exists
    let state <- prePostState.get
    if let some info := state then
      if info.hasDefPre then
        throwError "def_pre already defined in this specdef section"

    -- Apply the same restrictions as def
    if containsSorry body.raw then
      throwError "sorry is not allowed in def_pre"
    if containsAdmitted body.raw then
      throwError "admitted is not allowed in def_pre"

    let forbidden <- forbiddenFunctions.get
    if let some forbiddenName := containsForbiddenFunction forbidden body.raw then
      throwErrorAt body s!"'{forbiddenName}' is not allowed in def_pre"

    let forbidRec <- forbidRecursion.get
    if forbidRec && containsLetRec body.raw then
      throwError "'let rec' is not allowed in def_pre"

    -- Update state
    let newInfo : PrePostInfo := {
      preParams := params
      postParams := state.map (·.postParams) |>.getD #[]
      postReturnParam := state.map (·.postReturnParam) |>.getD (← `(bracketedBinder| (dummy : Unit)))
      hasDefPre := true
      hasDefPost := state.map (·.hasDefPost) |>.getD false
    }
    prePostState.modify (fun _ => some newInfo)

    -- Create the actual definition named 'pre' with unhygienic identifier
    let preId := mkIdent `pre
    let defStx <- `(command| def $preId $params:bracketedBinder* : Prop := $body)
    elabCommand defStx

-- Elaborate def_post
elab_rules : command
  | `(command| def_post $params* := $body) => do
    let inSpecDef <- inSpecDefSection
    unless inSpecDef do
      throwError "def_post can only be used inside a specdef section"

    -- Check if def_post already exists
    let state <- prePostState.get
    if let some info := state then
      if info.hasDefPost then
        throwError "def_post already defined in this specdef section"

    -- Check if def_pre exists
    let some info := state | throwError "def_pre must be defined before def_post"
    unless info.hasDefPre do
      throwError "def_pre must be defined before def_post"

    -- Check parameter consistency
    let preParamCount := info.preParams.size
    if params.size <= preParamCount then
      throwError s!"def_post must have more parameters than def_pre (expected at least {preParamCount + 1}, got {params.size})"

    -- Check that first parameters match def_pre
    for i in [:preParamCount] do
      let isMatch <- bindersMatch info.preParams[i]! params[i]!
      unless isMatch do
        throwErrorAt params[i]! s!"Parameter {i} of def_post must match parameter {i} of def_pre"

    -- The last parameter is the return value
    let returnParam := params[params.size - 1]!

    -- Apply the same restrictions as def
    if containsSorry body.raw then
      throwError "sorry is not allowed in def_post"
    if containsAdmitted body.raw then
      throwError "admitted is not allowed in def_post"

    let forbidden <- forbiddenFunctions.get
    if let some forbiddenName := containsForbiddenFunction forbidden body.raw then
      throwErrorAt body s!"'{forbiddenName}' is not allowed in def_post"

    let forbidRec <- forbidRecursion.get
    if forbidRec && containsLetRec body.raw then
      throwError "'let rec' is not allowed in def_post"

    -- Update state
    let newInfo : PrePostInfo := {
      preParams := info.preParams
      postParams := params
      postReturnParam := returnParam
      hasDefPre := true
      hasDefPost := true
    }
    prePostState.modify (fun _ => some newInfo)

    -- Create the actual definition named 'post' with unhygienic identifier
    let postId := mkIdent `post
    let defStx <- `(command| def $postId $params:bracketedBinder* : Prop := $body)
    elabCommand defStx

-- Enter a specdef section
elab "specdef" n:ident : command => do
  specDefSect.modify (n.getId :: ·)
  prePostState.modify (fun _ => none)  -- Reset pre/post state for new section
  elabCommand (← `(namespace $n))

-- Exit a specdef section
elab "specend" n:ident : command => do
  -- Check that both def_pre and def_post are defined
  let inSpecDef <- inSpecDefSection
  if inSpecDef then
    let state <- prePostState.get
    match state with
    | none => throwError "specdef section must contain both def_pre and def_post"
    | some info =>
      unless info.hasDefPre do
        throwError "specdef section must contain def_pre"
      unless info.hasDefPost do
        throwError "specdef section must contain def_post"

  specDefSect.modify List.tail
  prePostState.modify (fun _ => none)  -- Clear state when exiting
  elabCommand (← `(end $n))

-- Intercept all declarations to add restrictions in specdef sections
elab dec:declaration : command => do
  -- Check if we're in a specdef section
  let inSpecDef <- inSpecDefSection

  if inSpecDef then
    -- Check restrictions before elaborating
    -- First check for sorry and admitted in the entire declaration
    if containsSorry dec.raw then
      throwErrorAt dec "sorry is not allowed in specdef sections"
    if containsAdmitted dec.raw then
      throwErrorAt dec "admitted is not allowed in specdef sections"

    -- Get the list of forbidden functions
    let forbidden <- forbiddenFunctions.get

    -- Check if recursion is forbidden
    let forbidRec <- forbidRecursion.get

    -- Check for let rec if recursion is forbidden
    if forbidRec && containsLetRec dec.raw then
      throwErrorAt dec "'let rec' (recursive let binding) is not allowed in specdef sections"

    -- Then check for specific forbidden constructs
    match dec with
    | `(command| $[$_:docComment]? $[$_:attributes]? $[$_:visibility]? def $id:ident $_ := $val:term) =>
      -- Check if the definition body contains any forbidden function
      if let some forbiddenName := containsForbiddenFunction forbidden val.raw then
        throwErrorAt val s!"'{forbiddenName}' is not allowed in specdef sections"

      -- Check for recursion if forbidden
      if forbidRec then
        let defName := id.getId
        if containsReference defName val.raw then
          throwErrorAt val s!"recursive function '{defName}' is not allowed in specdef sections"
    | `(command| $[$_:docComment]? $[$_:attributes]? $[$_:visibility]? axiom $id:ident : $_) =>
      -- Axiom is not allowed in specdef sections
      throwErrorAt id "axiom is not allowed in specdef sections"
    | _ => pure ()

  -- Elaborate the declaration normally (checks passed or not in specdef section)
  elabCommand dec
