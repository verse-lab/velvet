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
          activateScoped `Std.Internal.Do
          activateScoped `Lean.Order
          let proofId := mkIdentFrom specId `spec
          -- Anchor generated syntax to the method identifier. Otherwise it inherits
          -- the whole command's range, so changing the proof's length prevents reuse.
          let thmCmd ← withRef specId `(command|
            @[spec] public theorem $proofId : $statement := by
              $proof)
          elabCommand thmCmd
        finally
          Lean.popScope
