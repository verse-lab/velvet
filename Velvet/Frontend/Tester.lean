module

prelude
public import Velvet.Frontend.Types
public meta import Velvet.Frontend.Types
public import Velvet.Frontend.Util
public meta import Velvet.Frontend.Util
public import Velvet.Frontend.Method
public meta import Velvet.Frontend.Method
public import Velvet.Core.Testing
public meta import Velvet.Core.Testing
public import Velvet.Core.NonDet
public meta import Lean.Parser
public meta import Lean.Elab.Command

open Lean Elab Command Term Meta Lean.Parser Velvet.Testing

/-- Look up testing context for a given method identifier. -/
public meta def obtainVelvetTestingCtx (nameRaw : Ident) : CommandElabM VelvetTestingCtx := do
  let env ← getEnv
  let map := velvetTestingExt.getState env
  let resolvedName? ← try
    let n ← liftCoreM <| realizeGlobalConstNoOverload nameRaw
    pure (some n)
  catch _ =>
    pure none
  if let some n := resolvedName? then
    if let some ctx := map.get? n then
      return ctx
  if let some ctx := map.get? nameRaw.getId then
    return ctx
  throwErrorAt nameRaw s!"`{nameRaw.getId}` is not a registered Velvet method"

/-- Extract a program definition `<method>Exec` for execution.
For non-deterministic methods (`AngelicT`, `DemonicT`, `NonDetT`), runs `NonDetT.run`. -/
syntax (name := extractProgramCmd) "extract_program_for " ident : command
elab_rules : command
  | `(command| extract_program_for $nameRaw:ident ) => do
    let ctx ← obtainVelvetTestingCtx nameRaw
    let binders := ctx.binders
    let ids := ctx.ids
    let execName := mkIdent (nameRaw.getId.appendAfter "Exec")
    let isNonDet := ctx.monadStack.isSome &&
      (match ctx.monadStack.get! with
       | `(term| NonDetT $_ $_) | `(term| AngelicT $_) | `(term| DemonicT $_) => true
       | _ => false)
    let idArgs : Array (TSyntax `term) := ids.map fun id => ⟨id.raw⟩
    let callApp : TSyntax `term := ⟨Syntax.mkApp nameRaw idArgs⟩
    let body ← if isNonDet then
      `(term| NonDetT.run $callApp)
    else
      pure callApp
    let cmd ← `(command|
      public def $execName $binders* := $body)
    elabCommand cmd

/-- Automatically synthesize or prove that the precondition of a method is `Decidable`.
Generates `<method>PreDecidable`. -/
syntax (name := provePreDecidableCmd) "prove_precondition_decidable_for " ident (ppSpace "by " tacticSeq)? : command
elab_rules : command
  | `(command| prove_precondition_decidable_for $nameRaw:ident $[by $tac?]?) => do
    let ctx ← obtainVelvetTestingCtx nameRaw
    let binders := ctx.binders
    let target := ctx.pre
    let decidableName := mkIdent (nameRaw.getId.appendAfter "PreDecidable")
    let tac := tac?.getD (← `(Lean.Parser.Tactic.tacticSeq| skip))
    let cmd ← `(command|
      public def $decidableName $binders* : Decidable ($target) := by
        repeat refine @instDecidableAnd _ _ ?_ ?_
        all_goals (try (infer_aux_decidable_instance ; infer_instance))
        ($tac))
    elabCommand cmd

/-- Automatically synthesize or prove that the postcondition of a method is `Decidable`.
Generates `<method>PostDecidable`. -/
syntax (name := provePostDecidableCmd) "prove_postcondition_decidable_for " ident (ppSpace "by " tacticSeq)? : command
elab_rules : command
  | `(command| prove_postcondition_decidable_for $nameRaw:ident $[by $tac?]?) => do
    let ctx ← obtainVelvetTestingCtx nameRaw
    let retBinder ← `(Lean.Parser.Term.bracketedBinderF| ($(ctx.retId) : $(ctx.retType)))
    let binders := ctx.binders.push ⟨retBinder.raw⟩
    let target := ctx.post
    let decidableName := mkIdent (nameRaw.getId.appendAfter "PostDecidable")
    let tac := tac?.getD (← `(Lean.Parser.Tactic.tacticSeq| skip))
    let cmd ← `(command|
      public def $decidableName $binders* : Decidable ($target) := by
        repeat refine @instDecidableAnd _ _ ?_ ?_
        all_goals (try (infer_aux_decidable_instance ; infer_instance))
        ($tac))
    elabCommand cmd

/-- Derive an executable testing function `<method>Tester` from the method specification and implementation. -/
syntax (name := deriveTesterCmd) "derive_tester_for " ident : command
elab_rules : command
  | `(command| derive_tester_for $nameRaw:ident ) => do
    let ctx ← obtainVelvetTestingCtx nameRaw
    let binders := ctx.binders
    let ids := ctx.ids
    let env ← getEnv
    let execIdent :=
      let cand := nameRaw.getId.appendAfter "Exec"
      if env.contains cand then mkIdent cand else nameRaw
    let isNonDet := ctx.monadStack.isSome &&
      (match ctx.monadStack.get! with
       | `(term| NonDetT $_ $_) | `(term| AngelicT $_) | `(term| DemonicT $_) => true
       | _ => false)
    let idArgs : Array (TSyntax `term) := ids.map fun id => ⟨id.raw⟩
    let execApp : TSyntax `term := ⟨Syntax.mkApp execIdent idArgs⟩
    let callTerm ← if isNonDet && execIdent == nameRaw then
      `(term| NonDetT.run $execApp)
    else
      pure execApp
    let preCand := nameRaw.getId.appendAfter "PreDecidable"
    let preDecide ← if env.contains preCand then
      let preApp : TSyntax `term := ⟨Syntax.mkApp (mkIdent preCand) idArgs⟩
      `(term| @decide _ $preApp)
    else
      `(term| decide ($(ctx.pre)))
    let postCand := nameRaw.getId.appendAfter "PostDecidable"
    let postDecide ← if env.contains postCand then
      let postApp : TSyntax `term := ⟨Syntax.mkApp (mkIdent postCand) (idArgs.push ⟨ctx.retId.raw⟩)⟩
      `(term| @decide _ $postApp)
    else
      `(term| decide ($(ctx.post)))
    let testerName := mkIdent (nameRaw.getId.appendAfter "Tester")
    let cmd ← `(command|
      public def $testerName $binders* : Bool :=
        if $preDecide then
          match $callTerm:term with
          | some $(ctx.retId) => $postDecide
          | none => false
        else
          true)
    elabCommand cmd

/-- Run property-based tests on `<method>Tester` using randomized sample generation. -/
syntax (name := testMethodCmd) "#test_method " ident (ppSpace "(" &"numTests" " := " num ")")? : command
elab_rules : command
  | `(command| #test_method $nameRaw:ident $[(numTests := $n)]?) => do
    let numTests : Nat := n.map (·.getNat) |>.getD 100
    let numTestsTerm := quote numTests
    let testerIdent := mkIdent (nameRaw.getId.appendAfter "Tester")
    let nameStr := quote nameRaw.getId.toString
    let cmd ← `(command|
      #eval do
        let ok ← Velvet.Testing.velvetQuickCheck $nameStr $testerIdent $numTestsTerm
        unless ok do
          throw <| IO.userError s!"[Velvet PBT] Tests failed for $nameStr")
    elabCommand cmd
