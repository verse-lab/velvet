module

public import Velvet.Frontend.Method
public meta import Velvet.Frontend.Method
public import Velvet.Frontend.SyntaxDecls
public import Velvet.Core.Specs
public meta import Velvet.Core.Specs
public meta import Lean.Parser
public meta import Lean.Elab.Command
public import Std.Internal.Do

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do

/-- Prove a method contract with `prove_correct foo`, producing the registered theorem
`foo.spec`. The theorem statement is elaborated from the stored contract syntax, and
the supplied tactics prove that statement directly. -/
@[incremental]
elab_rules : command
  | `(command| prove_correct $specId:ident by $proof:tacticSeq) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverload specId
    /- Fires when the target was not declared using `method`. -/
    let some statement := methodSpecExt.getState (← getEnv) |>.get? declName
      | throwErrorAt specId "no method contract metadata found for `{declName}`"
    let statement : Term := ⟨statement⟩
    let proofId := mkIdentFrom specId (specId.getId ++ `spec)
    let thmCmd ← `(command|
      open scoped Std.Internal.Do Lean.Order in
      set_option linter.unusedVariables false in
      @[spec] public theorem $proofId : $statement := by
        ($proof))
    elabCommand thmCmd
