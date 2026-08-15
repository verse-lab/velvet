import Velvet2.Elab.Types
import Velvet2.Elab.SyntaxDecls
import Lean.Parser
import Lean.Elab.Command

open Lean Elab Command Term Meta Lean.Parser Lean.Macro

/-- Parse an explicit binder `(x : T)` (or `(x)`) into its identifier and optional type. -/
def parseAssertionBinder (stx : TSyntax `velvBinder) : CommandElabM AssertionBinder := do
  match stx with
  | `(velvBinder| ($id:ident : $ty:term)) => pure { ident := id, type := some ty, stx }
  | `(velvBinder| ($id:ident)) => pure { ident := id, type := none, stx }
  | _ =>
      /- Fires when an assertion binder is neither `(x : T)` nor `(x)`. Under the `velvBinder`
         grammar this is only reachable for hand-built syntax, e.g. `(x y : T)`. -/
      throwErrorAt stx "expected an explicit binder of the form `(x : T)` or `(x)`"

/-- Parse a `velvSpecTerm` into its explicit binders and body term, keeping the raw node. -/
def parseSpecTerm (name : Option Ident) (stx : TSyntax `velvSpecTerm) : CommandElabM AssertionInfo := do
  let inner := stx.raw[0]
  if inner.getArgs.size == 3 && inner[1].isToken "," then
    let binders ← inner[0].getArgs.mapM fun b => parseAssertionBinder ⟨b⟩
    pure { name, binders, term := ⟨inner[2]⟩, stx }
  else
    pure { name, binders := #[], term := ⟨inner⟩, stx }

/-- Reconstruct a `fun` term from explicit binders. -/
def buildFun (binders : Array AssertionBinder) (body : TSyntax `term) :
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
def mkExceptTStackType (retType : TSyntax `term) (exTypes : Array (TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let mut stack : TSyntax `term ← `(term| Option)
  for t in exTypes.reverse do
    stack ← `(term| ExceptT $t $stack)
  `(term| $stack $retType)

/-- Parse a `bracketedBinder` into a `MethodParam`. Only single-identifier, explicitly typed
binders are supported. -/
def parseMethodParam (stx : TSyntax `Lean.Parser.Term.bracketedBinder) : CommandElabM MethodParam := do
  match stx with
  | `(bracketedBinder| ($id:ident : $ty:term)) => pure { ident := id, type := ty, stx }
  | `(bracketedBinder| {$id:ident : $ty:term}) => pure { ident := id, type := ty, stx }
  | _ =>
      /- Fires for unsupported method parameters, e.g. `method m [inst] ...`,
         `method m ⦃x : T⦄ ...`, or a multi-identifier binder `method m (x y : T) ...`. -/
      throwErrorAt stx "expected a method binder of the form (x : T) or an implicit binder"

/-- Fill in `requires`/`ensures`/`signals` names that were not given explicitly. -/
public def makeNameArrayFromIdents (ids : Array (Option Ident)) (pref : String) : Array Name :=
  ids.mapIdx fun i e =>
    match e with
    | some id => id.getId
    | none => Name.mkSimple s!"{pref}{i+1}"
