import Velvet.Frontend.Types
import Velvet.Frontend.SyntaxDecls
import Velvet.Frontend.Util
import Velvet.Core.Named
import Velvet.Core.Specs
import Velvet.Core.Loop
import Velvet.Core.VCGen
import Lean.Parser
import Lean.Elab.Do
import Lean.Elab.Command
import Std.WP

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.WP Named
open Lean Meta Elab
open Lean.Parser.Term
open Lean.Elab.Do

private def addMethodSpecEntry (state : Std.HashMap Name Syntax) (entry : MethodSpecEntry) :=
  state.insert entry.name entry.statement

initialize methodSpecExt : SimplePersistentEnvExtension MethodSpecEntry (Std.HashMap Name Syntax) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addMethodSpecEntry
    addImportedFn := fun entries =>
      mkStateFromImportedEntries addMethodSpecEntry {} entries }

set_option linter.unusedVariables false in
/-- Generate the `def`/`spec` command syntax for a parsed `method`, elaborate them, and register
the spec statement. All the method-generation logic lives here; the `elab_rules` only builds the
`MethodElabContext` from the syntax. -/
def elaborateMethod (ctx : MethodElabContext) : CommandElabM Unit := do
  match ctx.termination with
  | .totalCorrectness => checkWhileTermination ctx.body.raw
  | .partialCorrectness => pure ()
  let (defCmd, specCmd, motiveCmd?, statement) ← Command.runTermElabM fun _vs => do
    let ids := ctx.binders.map (·.ident)
    let binderStxs := ctx.binders.map (·.stx)
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
      | .totalCorrectness => `(term| fun (_ : Unit) => False)
      | .partialCorrectness => `(term| fun (_ : Unit) => True)
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
      for c in ctx.signalsClauses do
        if c.binders.size != 1 then
          /- Fires when a `signals` clause without an `in <MonadStack>` override does not have
             exactly one explicit binder, e.g. `signals False` (zero binders) or
             `signals (e : String) (n : Nat) => ...` (two binders). -/
          throwErrorAt c.stx s!"expected exactly one explicit binder in `signals` when no `in` monad stack is given, got {c.binders.size}"
        /- Defensive: unreachable after the binder-count check above. -/
        let some b := c.binders[0]? | throwErrorAt c.stx "internal error: expected exactly one binder"
        /- Fires when the single `signals` binder has no type annotation, e.g.
           `signals (e) => e = "boom"` (without `in`). -/
        let some ty := b.type
          | throwErrorAt b.stx "expected a typed binder `(x : T)` in `signals` when no `in` monad stack is given"
        exTypes := exTypes.push ty
      sigTerms := sigFunTerms.push defaultSig
      sigNames := sigNamesBase.push `termination_semantics
      monadStack' ← liftMacroM <| mkExceptTStackType ctx.retType exTypes
    let sigs ← liftMacroM <| mkSignalsList sigTerms sigNames
    let defCmd ←
      if ctx.isRec then
        `(command|
          set_option linter.unusedVariables false in
          def $(ctx.name) $binderStxs* : ($monadStack') := do $(ctx.body)
            partial_fixpoint)
      else
        `(command|
          set_option linter.unusedVariables false in
          def $(ctx.name) $binderStxs* : ($monadStack') := do $(ctx.body))
    let specId := mkIdentFrom ctx.name (ctx.name.getId ++ `spec_triple)
    let statement ← `(term|
      ∀ $binderStxs*, Std.WP.Triple
        ($(ctx.name) $ids*)
        $pre
        ($post)
        ($sigs))
    let specCmd ← `(command|
      open scoped Std.WP Lean.Order in
      set_option linter.unusedVariables false in
      abbrev $specId := $statement)
    let motiveCmd? : Option (TSyntax `command) ←
      if ctx.isRec then
        let motiveId := mkIdentFrom ctx.name (ctx.name.getId ++ `fixpoint_triple_motive)
        let motiveStatement ←
          if binderStxs.isEmpty then
            `(term|
              fun (p : $monadStack') => Std.WP.Triple
                p
                $pre
                ($post)
                ($sigs))
          else
            `(term|
              fun (p : ∀ $binderStxs*, $monadStack') => ∀ $binderStxs*, Std.WP.Triple
                (p $ids*)
                $pre
                ($post)
                ($sigs))
        let cmd ← `(command|
          open scoped Std.WP Lean.Order in
          set_option linter.unusedVariables false in
          abbrev $motiveId := $motiveStatement)
        pure (some cmd)
      else
        pure none
    return (defCmd, specCmd, motiveCmd?, statement)
  elabCommand defCmd
  elabCommand specCmd
  if let some motiveCmd := motiveCmd? then
    elabCommand motiveCmd
  let specName ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom ctx.name (ctx.name.getId ++ `spec_triple))
  modifyEnv (methodSpecExt.addEntry · { name := specName, statement := statement })
  let verifyDuringElab := (← getOptions).getBool `velvet.verifyDuringElab false
  if verifyDuringElab then
    let lem : TSyntax `Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $(ctx.name):ident)
    let proveCmd ← `(command|
      prove_correct $(ctx.name) by
        vcgen_ [$lem] with finish)
    elabCommand proveCmd

set_option linter.unusedVariables false in
elab_rules : command
  | `(command|
      method $[rec%$recTk]? $name:ident $binders:bracketedBinder* returns ($retId:ident : $retType:term) $[in $monadStack:term]?
        $[requires $[$reqNs : ]? $req]* $[signals $[$sigNs : ]? $sig]*
        $[ensures $[$ensNs : ]? $ens]* do $body:doSeq) => do
    let termination := velvet.semantics.termination.get (← getOptions)
    let methodBinders ← binders.mapM parseMethodParam
    let requiresClauses ← (Array.zip reqNs req).mapM fun (nm, stx) => parseSpecTerm nm stx
    let signalsClauses ← (Array.zip sigNs sig).mapM fun (nm, stx) => parseSpecTerm nm stx
    let ensuresClauses ← (Array.zip ensNs ens).mapM fun (nm, stx) => parseSpecTerm nm stx
    elaborateMethod {
      name := name
      binders := methodBinders
      retId := retId
      retType := retType
      monadStack := monadStack
      termination := termination
      isRec := recTk.isSome
      body := body
      requiresClauses := requiresClauses
      signalsClauses := signalsClauses
      ensuresClauses := ensuresClauses
    }
