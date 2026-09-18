module

public import Velvet.Frontend.Options
public meta import Velvet.Frontend.Options
public import Velvet.Frontend.Types
public meta import Velvet.Frontend.Types
public import Velvet.Frontend.SyntaxDecls
public meta import Velvet.Frontend.SyntaxDecls
public import Velvet.Frontend.Util
public meta import Velvet.Frontend.Util
public import Velvet.Core.Named
public meta import Velvet.Core.Named
public import Velvet.Core.Specs
public meta import Velvet.Core.Specs
public import Velvet.Core.Loop
public meta import Velvet.Core.Loop
public import Velvet.Core.VCGen
public meta import Velvet.Core.VCGen
public meta import Lean.Parser
public meta import Lean.Elab.Do
public meta import Lean.Elab.Command
public import Std.Internal.Do

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do Named
open Lean Meta Elab
open Lean.Parser.Term
open Lean.Elab.Do

/-- `partial_fixpoint` hoists every parameter that is passed unchanged in all recursive calls out
of the fixpoint, so `<name>.fixpoint_induct` binds those *before* its `motive` and the motive only
ranges over the remaining, varying parameters. Recover that split by reading it back off the
generated induction principle, whose conclusion is `motive fun <varying> => <name> <args>`.

Returns one flag per method binder (`true` = fixed), or `none` if the shape is not recognised, in
which case the caller falls back to abstracting over every binder. -/
private meta def fixedParamMask (methodName : Name) (numParams : Nat) :
    MetaM (Option (Array Bool)) := do
  let inductName := methodName ++ `fixpoint_induct
  -- `fixpoint_induct` is a reserved name realized on demand; force it before looking it up.
  try
    let _ ← realizeGlobalConstNoOverload (mkIdent inductName)
  catch _ =>
    return none
  let env ← getEnv
  let some inductInfo := env.find? inductName | return none
  let some methodInfo := env.find? methodName | return none
  -- The method's own binders are the trailing parameters; section variables come first.
  let totalArgs ← forallTelescopeReducing methodInfo.type fun ys _ => pure ys.size
  if totalArgs < numParams then return none
  let leading := totalArgs - numParams
  forallTelescope inductInfo.type fun _ concl => do
    let .app _motive applied := concl | return none
    lambdaTelescope applied fun varying body => do
      unless body.getAppFn.isConstOf methodName do return none
      let args := body.getAppArgs
      if args.size < leading || args.size > totalArgs then return none
      let mut mask := #[]
      for a in args.extract leading args.size do
        mask := mask.push !(varying.any (· == a))
      -- Binders eta-contracted away in the conclusion are trailing varying ones.
      for _ in [mask.size : numParams] do
        mask := mask.push false
      return some mask

/-- Build the `<name>.fixpoint_triple_motive` command for a `method rec`.

The motive has to match what `<name>.fixpoint_induct` expects, and `partial_fixpoint` only
abstracts the parameters that actually vary across recursive calls. So the fixed ones become
parameters of the motive abbrev (they are bound by `fixpoint_induct` before the motive), and only
the varying ones are abstracted into `p`. Must run after the `def` has been elaborated, since the
split is read back off the generated `fixpoint_induct`. -/
private meta def mkFixpointMotiveCmd (ctx : MethodElabContext) (methodName : Name)
    (parts : TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) :
    CommandElabM (TSyntax `command) := do
  let (pre, post, sigs, monadStack') := parts
  let motiveId := mkIdentFrom ctx.name (ctx.name.getId ++ `fixpoint_triple_motive)
  let exploded ← ctx.binders.flatMapM fun b => explodeBinder b.raw
  let mask? ← liftTermElabM <| fixedParamMask methodName exploded.size
  -- Without a recognised split, fall back to abstracting every binder (the pre-existing shape).
  let mask := mask?.getD (Array.replicate exploded.size false)
  let fixed := exploded.zip mask |>.filterMap fun (b, f) => if f then some b else none
  let varying := exploded.zip mask |>.filterMap fun (b, f) => if f then none else some b
  let varyingIds := varying.flatMap (fun b => contractBinderIdents b.raw)
  let motiveStatement ←
    if varying.isEmpty then
      if ctx.givenBinders.isEmpty then
        `(term| fun (p : $monadStack') => Std.Internal.Do.Triple p $pre ($post) ($sigs))
      else
        let givenBinders := ctx.givenBinders
        `(term|
          fun (p : $monadStack') => ∀ $givenBinders*,
            Std.Internal.Do.Triple p $pre ($post) ($sigs))
    else
      let quantified := varying ++ ctx.givenBinders
      `(term|
        fun (p : ∀ $varying*, $monadStack') => ∀ $quantified*,
          Std.Internal.Do.Triple (p $varyingIds*) $pre ($post) ($sigs))
  if fixed.isEmpty then
    `(command|
      open scoped Std.Internal.Do Lean.Order in
      set_option linter.unusedVariables false in
      public abbrev $motiveId := $motiveStatement)
  else
    `(command|
      open scoped Std.Internal.Do Lean.Order in
      set_option linter.unusedVariables false in
      public abbrev $motiveId $fixed* := $motiveStatement)

set_option linter.unusedVariables false in
/-- Generate the `def`/`spec` command syntax for a parsed `method`, elaborate them, and register
the spec statement. All the method-generation logic lives here; the `elab_rules` only builds the
`MethodElabContext` from the syntax. -/
public meta def elaborateMethod (ctx : MethodElabContext) : CommandElabM Unit := do
  match ctx.termination with
  | .totalCorrectness => checkWhileTermination ctx.body.raw
  | .partialCorrectness => pure ()
  let (defCmd, specCmd, motiveParts, statement) ← Command.runTermElabM fun _vs => do
    let ids := ctx.binders.flatMap (fun b => contractBinderIdents b.raw)
    let binderStxs := ctx.binders
    let allBinderStxs := binderStxs ++ ctx.givenBinders
    let reqNames := makeNameArrayFromIdents (ctx.requiresClauses.map (·.name)) "requires"
    let ensNames := makeNameArrayFromIdents (ctx.ensuresClauses.map (·.name)) "ensures"
    let reqTerms ← liftMacroM <| ctx.requiresClauses.mapM (fun c => buildFun c.binders c.term)
    let ensTerms ← liftMacroM <| ctx.ensuresClauses.mapM (fun c => buildFun c.binders c.term)
    let pre ← liftMacroM <| mkAssertionList reqTerms reqNames
    let postBody ← liftMacroM <| mkAssertionList ensTerms ensNames
    -- The `fun retId =>` wrapper stays outside `mkAssertionList` so the named ensures clauses
    -- keep source references to the user's ensures terms. `mkAssertionList` captures each term's
    -- range with `Named.sourceRefTerm`; a quotation-generated `fun` wrapper would instead make
    -- that range start in this file (the macro quotation), not at the user's clause.
    let post ← `(fun ($(ctx.retId) : $(ctx.retType)) => $postBody)
    -- Default `signals` for the base `Option` monad (no `in <MonadStack>` and no explicit
    -- `signals`): total correctness forbids failure (`False`), partial permits it (`True`).
    -- It is also reused as the innermost `Option` failure postcondition of an auto-generated
    -- `ExceptT` stack.
    let defaultSig : TSyntax `term ←
      match ctx.termination with
      | .totalCorrectness => `(term| False)
      | .partialCorrectness => `(term| True)
    let sigFunTerms ← liftMacroM <| ctx.signalsClauses.mapM (fun c => buildFun c.binders c.term)
    let sigNamesBase := makeNameArrayFromIdents (ctx.signalsClauses.map (·.name)) "signals"
    let mut sigTerms : Array (TSyntax `term) := sigFunTerms
    let mut sigNames : Array Name := sigNamesBase
    let mut monadStack' : TSyntax `term ← `(term| PUnit)
    if ctx.monadStack.isSome then
      monadStack' ← `(term| $(ctx.monadStack.get!) $(ctx.retType))
    else if ctx.signalsClauses.isEmpty then
      sigTerms := #[defaultSig]
      sigNames := #[`termination_semantics]
      monadStack' ← `(term| Option $(ctx.retType))
    else
      let mut exTypes : Array (TSyntax `term) := #[]
      let mut hasOptionSignal := false
      for (c, i) in ctx.signalsClauses.zipIdx do
        if c.binders.isEmpty then
          unless i + 1 == ctx.signalsClauses.size do
            throwErrorAt c.stx "a binderless `signals` clause describes Option failure and must be last"
          hasOptionSignal := true
          continue
        if c.binders.size != 1 then
          /- Each inferred ExceptT layer requires one typed exception binder. -/
          throwErrorAt c.stx s!"expected exactly one explicit binder in `signals` when no `in` monad stack is given, got {c.binders.size}"
        /- Defensive: unreachable after the binder-count check above. -/
        let some b := c.binders[0]? | throwErrorAt c.stx "internal error: expected exactly one binder"
        /- Fires when the single `signals` binder has no type annotation, e.g.
           `signals (e) => e = "boom"` (without `in`). -/
        let some ty := b.type
          | throwErrorAt b.stx "expected a typed binder `(x : T)` in `signals` when no `in` monad stack is given"
        exTypes := exTypes.push ty
      if !hasOptionSignal then
        sigTerms := sigFunTerms.push defaultSig
        sigNames := sigNamesBase.push `termination_semantics
      monadStack' ← liftMacroM <| mkExceptTStackType ctx.retType exTypes
    let sigs ← liftMacroM <| mkSignalsList sigTerms sigNames
    let defCmd ←
      if ctx.isRec then
        match ctx.doc with
        | some doc =>
          `(command|
            set_option linter.unusedVariables false in
            $doc:docComment
            @[expose] public def $(ctx.name) $binderStxs* : ($monadStack') := do $(ctx.body)
              partial_fixpoint)
        | none =>
          `(command|
            set_option linter.unusedVariables false in
            @[expose] public def $(ctx.name) $binderStxs* : ($monadStack') := do $(ctx.body)
              partial_fixpoint)
      else
        let tb := ctx.terminationBy
        let db := ctx.decreasingBy
        match ctx.doc with
        | some doc =>
          `(command|
            set_option linter.unusedVariables false in
            $doc:docComment
            @[expose] public def $(ctx.name) $binderStxs* : ($monadStack') := do $(ctx.body)
              $[$tb]? $[$db]?)
        | none =>
          `(command|
            set_option linter.unusedVariables false in
            @[expose] public def $(ctx.name) $binderStxs* : ($monadStack') := do $(ctx.body)
              $[$tb]? $[$db]?)
    let specId := mkIdentFrom ctx.name (ctx.name.getId ++ `spec_triple)
    let statement ←
      if allBinderStxs.isEmpty then
        `(term|
          Std.Internal.Do.Triple
            (($(ctx.name) $ids* : $monadStack'))
            $pre
            ($post)
            ($sigs))
      else
        `(term|
          ∀ $allBinderStxs*, Std.Internal.Do.Triple
            (($(ctx.name) $ids* : $monadStack'))
            $pre
            ($post)
            ($sigs))
    let specCmd ← `(command|
      open scoped Std.Internal.Do Lean.Order in
      set_option linter.unusedVariables false in
      public abbrev $specId := $statement)
    return (defCmd, specCmd, (pre, post, sigs, monadStack'), statement)
  elabCommand defCmd
  elabCommand specCmd
  let methodName ← liftCoreM <| realizeGlobalConstNoOverload ctx.name
  if ctx.isRec then
    elabCommand (← mkFixpointMotiveCmd ctx methodName motiveParts)
  modifyEnv (methodSpecExt.addEntry · { name := methodName, statement := statement })
  let verifyOnDefinition := (← getOptions).getBool `velvet.verifyOnDefinition false
  if verifyOnDefinition then
    let lem : TSyntax `Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $(ctx.name):ident)
    let proveCmd ← `(command|
      prove_correct $(ctx.name) by
        velvet_vcgen [$lem] with finish)
    elabCommand proveCmd

set_option linter.unusedVariables false in
elab_rules : command
  | `(command|
      $[$doc:docComment]?
      method $[rec%$recTk]? $name:ident $binders* returns ($retId:ident : $retType:term) $[in $monadStack:term]?
        $[given $givenBinders*]?
        $[requires $[$reqNs : ]? $req]* $[signals $[$sigNs : ]? $sig]*
        $[ensures $[$ensNs : ]? $ens]* do $body:doSeq
        $[$tb:terminationBy]? $[$db:decreasingBy]?) => do
    let termination := velvet.semantics.termination.get (← getOptions)
    /- `rec` emits `partial_fixpoint`, which occupies the same `Termination.suffix` slot as
       `termination_by`; Lean would reject the combination with a confusing parse-level error. -/
    if recTk.isSome then
      if let some tb := tb then
        throwErrorAt tb "`termination_by` cannot be combined with `method rec`: \
          `rec` defines the method by `partial_fixpoint`, which has no termination measure"
      if let some db := db then
        throwErrorAt db "`decreasing_by` cannot be combined with `method rec`: \
          `rec` defines the method by `partial_fixpoint`, which has no termination measure"
    let binderStxs : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
      binders.map (⟨·.raw⟩)
    let givenBindersArr : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
      match givenBinders with
      | some arr => arr.map (⟨·.raw⟩)
      | none => #[]
    let requiresClauses ← (Array.zip reqNs req).mapM fun (nm, stx) => parseSpecTerm nm stx
    let signalsClauses ← (Array.zip sigNs sig).mapM fun (nm, stx) => parseSpecTerm nm stx
    let ensuresClauses ← (Array.zip ensNs ens).mapM fun (nm, stx) => parseSpecTerm nm stx
    elaborateMethod {
      doc := doc
      name := name
      binders := binderStxs
      givenBinders := givenBindersArr
      retId := retId
      retType := retType
      monadStack := monadStack
      termination := termination
      isRec := recTk.isSome
      body := body
      terminationBy := tb
      decreasingBy := db
      requiresClauses := requiresClauses
      signalsClauses := signalsClauses
      ensuresClauses := ensuresClauses
    }
