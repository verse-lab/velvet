module

public import Velvet.Core.Ghost
public meta import Lean.Parser
public meta import Lean.Elab.Command
public meta import Lean.Elab.Do
public meta import Lean.Elab.BuiltinDo.Let
public meta import Lean.Meta.Basic
public meta import Lean.Elab.Term

open Lean Elab Command Term Meta Lean.Parser
open Lean.Parser.Term (doReassign)
open Lean.Elab.Do

namespace GhostSyntax

scoped macro "let" "ghost" x:ident ":=" value:term : doElem =>
  `(doElem| let mut $x := _root_.Ghost.mk $value)

/-- Reassign a ghost variable, lifting ordinary expressions on the right into `Ghost`. -/
scoped syntax (name := ghostReassign) ident " *:= " term : doElem

open scoped GhostSyntax

namespace GhostUtils

private structure GhostLocal where
  source : Ident
  binder : Ident
  fvarId : FVarId

private meta def isGhostType (type : Expr) : MetaM Bool := do
  return (← whnf type).isAppOf ``Ghost

private meta def liftGhostLocals (rhs : Term) : DoElabM Term := do
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

private meta def alreadyGhost (rhs : Term) (expectedType : Expr) : DoElabM Bool :=
  Lean.Elab.withoutModifyingStateWithInfoAndMessages do
    return (← Lean.Elab.Term.commitIfNoErrors? do
      discard <| Lean.Elab.Term.elabTermEnsuringType rhs (some expectedType)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing).isSome

end GhostUtils

@[doElem_control_info ghostReassign]
public meta def controlInfoGhostReassign : ControlInfoHandler := fun stx => do
  let `(doElem| $x:ident *:= $_rhs) := stx
    | throwUnsupportedSyntax
  return { reassigns := {x.getId} }

@[doElem_elab ghostReassign]
public meta def elabGhostReassign : DoElab := fun stx cont => do
  let `(doElem| $x:ident *:= $rhs) := stx
    | throwUnsupportedSyntax
  let original ← `(doReassign| $x:ident := $rhs)
  let original : DoElem := ⟨original.raw⟩

  let some decl := (← getLCtx).findFromUserName? x.getId
    | throwUnsupportedSyntax
  unless ← GhostUtils.isGhostType decl.type do
    throwUnsupportedSyntax

  if ← GhostUtils.alreadyGhost rhs decl.type then
    Lean.Elab.Do.elabDoReassign original cont
  else
    let rhs ← GhostUtils.liftGhostLocals rhs
    let stx ← `(doReassign| $x:ident := $rhs)
    Lean.Elab.Do.elabDoReassign ⟨stx.raw⟩ cont

end GhostSyntax
