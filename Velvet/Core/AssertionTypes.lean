module

public import Std.WP
public meta import Lean.Elab.Term

open Lean Meta Elab Term

/-- The assertion types of a monad, which its `WPMonad` instance computes as output parameters:
`pred` for preconditions and postconditions, `epred` for exception postconditions. For
`StateM Nat`, `pred` is `Nat → Prop`; for `ExceptT String (StateT Nat Option)`, `epred` is
`(String → Nat → Prop) × (Unit → Prop)`. -/
public structure AssertionTypes where
  pred : Expr
  epred : Expr

/-- The assertion types of the monad `m`, or `none` when `m` has no `WPMonad` instance. -/
public meta def assertionTypes? (m : Expr) : MetaM (Option AssertionTypes) := do
  let wpMonad ← mkConstWithFreshMVarLevels ``Std.WP.WPMonad
  let (args, _, _) ← forallMetaTelescope (← inferType wpMonad)
  let some m' := args[0]? | return none
  unless ← isDefEq m' m do return none
  let .some _ ← trySynthInstance (mkAppN wpMonad args) | return none
  let (some pred, some epred) := (args[1]?, args[2]?) | return none
  let pred ← instantiateMVars pred
  let epred ← instantiateMVars epred
  if pred.hasExprMVar || epred.hasExprMVar then return none
  return some { pred, epred }

/-- `assertion_type% (m α)` is the assertion type `pred` of the monad `m`. -/
syntax (name := assertionType) "assertion_type% " term:max : term

/-- `exception_assertion_type% (m α)` is the exception assertion type `epred` of the monad `m`. -/
syntax (name := exceptionAssertionType) "exception_assertion_type% " term:max : term

private meta def elabAssertionTypes (type : Syntax) : TermElabM AssertionTypes := do
  let type ← instantiateMVars (← elabType type)
  let .app m _ := type.consumeMData
    | throwError "expected a monadic type `m α`, got{indentExpr type}"
  let some info ← assertionTypes? m
    | throwError "no `WPMonad` instance for{indentExpr m}"
  return info

@[term_elab assertionType]
public meta def elabAssertionType : TermElab := fun stx _ => do
  let `(assertion_type% $type) := stx | throwUnsupportedSyntax
  return (← elabAssertionTypes type).pred

@[term_elab exceptionAssertionType]
public meta def elabExceptionAssertionType : TermElab := fun stx _ => do
  let `(exception_assertion_type% $type) := stx | throwUnsupportedSyntax
  return (← elabAssertionTypes type).epred
