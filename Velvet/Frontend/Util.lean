module

public import Velvet.Frontend.Types
public meta import Velvet.Frontend.Types
public import Velvet.Frontend.SyntaxDecls
public meta import Velvet.Frontend.SyntaxDecls
public import Velvet.Core.Named
public meta import Velvet.Core.Named
public import Velvet.Core.Specs
public meta import Velvet.Core.Specs
public meta import Lean.Parser
public meta import Lean.Elab.Command

open Lean Elab Command Term Meta Lean.Parser Lean.Macro

/-- Parse an explicit binder `(x : T)` (or `(x)`) into its identifier and optional type. -/
public meta def parseAssertionBinder (stx : TSyntax `velvBinder) : CommandElabM AssertionBinder := do
  match stx with
  | `(velvBinder| ($id:ident : $ty:term)) => pure { ident := id, type := some ty, stx }
  | `(velvBinder| ($id:ident)) => pure { ident := id, type := none, stx }
  | `(velvBinder| (_ : $ty:term)) => pure { ident := mkIdent `_, type := some ty, stx }
  | `(velvBinder| (_)) => pure { ident := mkIdent `_, type := none, stx }
  | _ =>
      /- Fires when an assertion binder is neither `(x : T)` nor `(x)`. Under the `velvBinder`
         grammar this is only reachable for hand-built syntax, e.g. `(x y : T)`. -/
      throwErrorAt stx "expected an explicit binder of the form `(x : T)` or `(x)`"

/-- Parse a `velvSpecTerm` into its explicit binders and body term, keeping the raw node. -/
public meta def parseSpecTerm (name : Option Ident) (stx : TSyntax `velvSpecTerm) : CommandElabM AssertionInfo := do
  let inner := stx.raw[0]
  if inner.getArgs.size == 3 && inner[1].isToken "=>" then
    let binders ← inner[0].getArgs.mapM fun b => parseAssertionBinder ⟨b⟩
    pure { name, binders, term := ⟨inner[2]⟩, stx }
  else
    pure { name, binders := #[], term := ⟨inner⟩, stx }

/-- Reconstruct a `fun` term from explicit binders. -/
public meta def buildFun (binders : Array AssertionBinder) (body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  if binders.isEmpty then
    return body
  let funBinders ← binders.mapM fun b => do
    let id := b.ident
    match b.type with
    | some ty => `(term| ($id : $ty))
    | none => `(term| $id)
  `(term| fun $funBinders* => $body)

/-- Build `ExceptT e₁ (ExceptT e₂ … Option) retType` from the signal exception types. -/
public meta def mkExceptTStackType (retType : TSyntax `term) (exTypes : Array (TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let mut stack : TSyntax `term ← `(term| Option)
  for t in exTypes.reverse do
    stack ← `(term| ExceptT $t $stack)
  `(term| $stack $retType)

/-- The identifiers bound by an explicit `(…)` or bare identifier binder, used to apply the definition in its spec. -/
public meta def contractBinderIdents (binder : Syntax) : Array Ident :=
  match binder with
  | `(Lean.Parser.Term.bracketedBinderF| ($ids* $[: $_]? $(_annot?)?)) =>
      ids.filterMap fun b => if b.raw.isIdent then some ⟨b.raw⟩ else none
  | _ =>
      if binder.isIdent then #[⟨binder⟩]
      else if binder.isOfKind ``Lean.binderIdent && binder[0].isIdent then #[⟨binder[0]⟩]
      else #[]

