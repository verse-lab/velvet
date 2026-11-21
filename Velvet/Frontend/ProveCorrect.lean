module

public import Velvet.Frontend.Method
public meta import Velvet.Frontend.Method
public import Velvet.Frontend.SyntaxDecls
public import Velvet.Core.Specs
public meta import Velvet.Core.Specs
public meta import Velvet.Frontend.VCReport
public meta import Lean.Parser
public meta import Lean.Elab.Command
public import Std.WP

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.WP

/-- `method_contract% f` is the contract of method `f`, as it was elaborated where `f` was
declared: the body of `f.spec_triple`, with its section-variable parameters as `∀` binders. -/
syntax (name := methodContract) "method_contract% " ident : term

@[term_elab methodContract]
public meta def elabMethodContract : TermElab := fun stx _ => do
  let `(method_contract% $id) := stx | throwUnsupportedSyntax
  let methodName ← realizeGlobalConstNoOverload id
  let info ← getConstInfo (methodName ++ `spec_triple)
  let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let some value := info.value? (allowOpaque := true)
    | throwError "`{methodName}.spec_triple` has no definition"
  lambdaTelescope (value.instantiateLevelParams info.levelParams us) fun xs body =>
    mkForallFVars xs body

/-- Prove a method contract with `prove_correct foo`, producing the registered theorem
`foo.spec`, whose statement is the body of `foo.spec_triple`. -/
@[incremental]
elab_rules : command
  | `(command| prove_correct $specId:ident by $proof:tacticSeq) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverload specId
    /- Fires when the target was not declared using `method`. -/
    unless (methodsExt.getState (← getEnv)).contains declName do
      throwErrorAt specId "no method contract metadata found for `{declName}`"
    let proofName := declName ++ `spec
    -- Key generated hygiene scopes by the theorem name. The default uses the whole
    -- command text, so proof edits would change generated identifiers and prevent reuse.
    withInitQuotContext (some (hash proofName)) do
      modifyEnv (·.registerNamespace declName)
      -- Generated namespace/open wrappers leave pending `end` commands that mark
      -- the whole proof as processing. Enter the scopes directly to avoid this.
      withScope ({ · with currNamespace := declName }) do
        Lean.pushScope
        try
          activateScoped declName
          activateScoped `Std.WP
          activateScoped `Lean.Order
          let proofId := mkIdentFrom specId `spec
          -- Already resolved, so names declared in `namespace declName` cannot capture it.
          let methodId := mkCIdentFrom specId declName
          -- Anchor generated syntax to the method identifier. Otherwise it inherits
          -- the whole command's range, so changing the proof's length prevents reuse.
          let thmCmd ← withRef specId `(command|
            @[spec] public theorem $proofId : method_contract% $methodId := by
              $proof)
          -- Keep the report visible throughout the proof without broadening thmCmd's ref.
          let reportRef := mkNullNode #[specId.raw, proof.raw]
          VCGen.withProofVCReport reportRef <| elabCommand thmCmd
        finally
          Lean.popScope
