import Velvet2.Elab.Types
import Velvet2.Elab.SyntaxDecls
import Velvet2.Elab.Util
import Velvet2.Named
import Velvet2.Specs
import Lean.Parser
import Lean.Elab.Do
import Lean.Elab.BuiltinDo.Let
import Velvet2.Ghost
import Velvet2.VCGen.Frontend
import Lean.Elab.Command
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.WP.Lemmas
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.Gadget
import Std.Internal.Do.Triple.SpecLemmas

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do Named
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

namespace GhostUtils

private structure GhostLocal where
  source : Ident
  binder : Ident
  fvarId : FVarId

private def isGhostType (type : Expr) : MetaM Bool := do
  return (← whnf type).isAppOf ``Ghost

private def liftGhostLocals (rhs : Term) : DoElabM Term := do
  let rewrite : Syntax → StateT (Array GhostLocal) DoElabM (Option Syntax) := fun stx => do
    unless stx.isIdent do return none
    let source : Ident := ⟨stx⟩
    let some decl := (← getLCtx).findFromUserName? source.getId | return none
    unless ← isGhostType decl.type do return none
    if let some ghostLocal := (← get).find? (·.fvarId == decl.fvarId) then
      return some ghostLocal.binder.raw
    let binder ← Lean.Elab.Term.mkFreshIdent source
    modify (·.push ⟨source, binder, decl.fvarId⟩)
    return some binder.raw
  let (rhs, locals) ← (rhs.raw.replaceM rewrite).run #[]
  let mut result ← `(Ghost.mk $(⟨rhs⟩):term)
  for ghostLocal in locals.reverse do
    result ← `($(ghostLocal.source) >>= fun $(ghostLocal.binder) => $result)
  return result

private def alreadyGhost (rhs : Term) (expectedType : Expr) : DoElabM Bool :=
  Lean.Elab.withoutModifyingStateWithInfoAndMessages do
    return (← Lean.Elab.Term.commitIfNoErrors? do
      discard <| Lean.Elab.Term.elabTermEnsuringType rhs (some expectedType)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing).isSome

end GhostUtils


/-- Walk a `do` body and require every `while'` loop to carry a `decreasing` clause. -/
private partial def checkWhilePrimeTermination (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(doElem| while' $[$_hcond : ]? $_cond $[ invariant $[$_ns : ]? $_invs]* $[decreasing $[$_hm : ]? $m]? $[done_with $[$_h_done : ]? $_d]? do $_body) =>
      if m.isNone then
        /- Fires when a `while'` loop in a total-correctness method has no `decreasing` clause,
           e.g. `while' i < n invariant True do ...` without `decreasing remaining : n - i`. -/
        throwErrorAt stx "`while'` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness"
  | _ => pure ()
  for a in stx.getArgs do
    checkWhilePrimeTermination a

set_option linter.unusedVariables false in
/-- Generate the `def`/`spec` command syntax for a parsed `method`, elaborate them, and register
the spec statement. All the method-generation logic lives here; the `elab_rules` only builds the
`MethodElabContext` from the syntax. -/
def elaborateMethod (ctx : MethodElabContext) : CommandElabM Unit := do
  match ctx.termination with
  | .totalCorrectness => checkWhilePrimeTermination ctx.body.raw
  | .partialCorrectness => pure ()
  let (defCmd, specCmd, statement) ← Command.runTermElabM fun _vs => do
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
    let post ← `(fun $(ctx.retId) => $postBody)
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
      for c in ctx.signalsClauses do
        if c.binders.size != 1 then
          /- Fires when a `signals` clause without an `in <MonadStack>` override does not have
             exactly one explicit binder, e.g. `signals False` (zero binders) or
             `signals (e : String) (n : Nat), ...` (two binders). -/
          throwErrorAt c.stx s!"expected exactly one explicit binder in `signals` when no `in` monad stack is given, got {c.binders.size}"
        /- Defensive: unreachable after the binder-count check above. -/
        let some b := c.binders[0]? | throwErrorAt c.stx "internal error: expected exactly one binder"
        /- Fires when the single `signals` binder has no type annotation, e.g.
           `signals (e), e = "boom"` (without `in`). -/
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
      ∀ $binderStxs*, Std.Internal.Do.Triple
        ($(ctx.name) $ids*)
        $pre
        ($post)
        ($sigs))
    let specCmd ← `(command|
      set_option linter.unusedVariables false in
      abbrev $specId := $statement)
    return (defCmd, specCmd, statement)
  elabCommand defCmd
  elabCommand specCmd
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

/-- Prove a method contract with `prove_correct foo`, producing the registered theorem
`foo.spec`. The generated abbreviation `foo.spec_triple` owns the complete quantified `Triple`;
this command only unfolds and proves that proposition. -/
@[incremental]
elab_rules : command
  | `(command| prove_correct $specId:ident by $proof:tacticSeq) => do
    let specIdent := mkIdentFrom specId (specId.getId ++ `spec_triple)
    let declName ← liftCoreM <| realizeGlobalConstNoOverload specIdent
    let info ← liftCoreM <| getConstInfo declName
    unless (← liftTermElabM <| whnf info.type).isProp do
      /- Fires when `prove_correct` targets a non-proposition, e.g. `prove_correct Nat.add by ...`. -/
      throwErrorAt specId "`{declName}` is not a proposition"
    /- Fires when the name has no method-contract metadata, e.g. a spec not generated by `method`. -/
    let some statement := methodSpecExt.getState (← getEnv) |>.get? declName
      | throwErrorAt specId "no method contract metadata found for `{declName}`"
    let statement : Term := ⟨statement⟩
    let proofId := mkIdentFrom specId (specId.getId ++ `spec)
    let thmCmd ← `(command|
      open scoped Std.Internal.Do Lean.Order in
      set_option linter.unusedVariables false in
      @[spec] theorem $proofId : $statement :=
        show $specIdent from by
          unfold $specIdent
          ($proof))
    elabCommand thmCmd

macro_rules
  | `(term| assert $nm:ident : $t:term) => do
    let nameStr := Lean.Syntax.mkStrLit nm.getId.toString
    let name : TSyntax `term ← `(Lean.Name.mkSimple $nameStr)
    let stx ← Named.sourceRefTerm t.raw
    `(_root_.assertGadget (Named.mk $name $stx $t))

macro_rules
  | `(doElem| for' $pat:term in $xs $[ invariant $[$ns : ]? $invs]* $[done_with $[$hDone : ]? $done]? do $body) => do
  let invs' ← mkAssertionList invs (makeNameArrayFromIdents ns "invariant")
  let doneTerm ← match done with
    | some done => pure done
    | none => `(True)
  let doneName := hDone.join.map (·.getId) |>.getD `h_done_with
  let done' ← mkAssertionList #[doneTerm] #[doneName]
  let pref := Lean.mkIdent `__pref
  let suff := Lean.mkIdent `__suff
  let cursorInv ← `(term|
    Velvet2.Spec.rangeInvariantValue (fun $pat => $invs') $done' $suff:ident)
  `(doElem| for $pat in $xs
    invariant $pref $suff => $cursorInv
    do $body)
  | `(doElem| while' $[$hcond : ]? $cond $[ invariant $[$ns : ]? $invs]* $[decreasing $[$hm : ]? $m]? $[done_with $[$h_done : ]? $d]? do $body) => do
  let defaultLoopIdent := mkIdent `h_loop
  let loopIdent := hcond.getD defaultLoopIdent
  let invNames := makeNameArrayFromIdents ns "invariant"
  let invs' ← mkAssertionList invs invNames
  let defaultDoneWith : TSyntax `term ← withRef cond do `(¬ $cond)
  let doneWith := d.getD defaultDoneWith
  let doneWithName := match h_done.join with
    | some id => id.getId
    | none => `h_done_with
  let exitedInvs ← mkAssertionList (invs.push doneWith) (invNames.push (doneWithName)) 
  let exited := Lean.mkIdent `__exited
  match m with
  | some m =>
      let measureName := match hm.join with
        | some id => id.getId
        | none => `decreasing
      let measureNameStr := Lean.Syntax.mkStrLit measureName.toString
      let measureNameTerm : TSyntax `term ←
        `(Lean.Name.mkSimple $measureNameStr)
      let measureStx ← Named.sourceRefTerm m.raw
      let measureNamed : TSyntax `term ←
        `(Named.Measure.mk $measureNameTerm $measureStx $m)
      `(doElem| while $loopIdent : $cond
        invariant $exited =>
          if $exited then $exitedInvs else $invs'
        decreasing $measureNamed
        do $body)
  | none =>
      `(doElem| while $loopIdent : $cond
        invariant $exited =>
          if $exited then $exitedInvs else $invs'
        do $body)


@[doElem_control_info ghostReassign]
def controlInfoGhostReassign : ControlInfoHandler := fun stx => do
  let `(doElem| *$x:ident := $_rhs) := stx
    | throwUnsupportedSyntax
  return { reassigns := {x.getId} }

@[doElem_elab ghostReassign]
def elabGhostReassign : DoElab := fun stx cont => do
  let `(doElem| *$x:ident := $rhs) := stx
    | throwUnsupportedSyntax
  let original ← `(doReassign| $x:ident := $rhs)
  let original : DoElem := ⟨original.raw⟩

  let some decl := (← getLCtx).findFromUserName? x.getId
    | throwUnsupportedSyntax
  unless ← GhostUtils.isGhostType decl.type do
    throwUnsupportedSyntax -- "*<lhs> := <rhs> syntax is only supported when <lhs> is a ghost type"

  if ← GhostUtils.alreadyGhost rhs decl.type then
    Lean.Elab.Do.elabDoReassign original cont
  else
    let rhs ← GhostUtils.liftGhostLocals rhs
    let stx ← `(doReassign| $x:ident := $rhs)
    Lean.Elab.Do.elabDoReassign ⟨stx.raw⟩ cont
