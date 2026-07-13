import Lean
open Lean Meta Elab

namespace NamedProp

@[simp, grind =]
public noncomputable def one (_name : Name) (p : Prop)
    (_stx : Option Syntax := none) : Prop := p

@[simp, grind =]
public noncomputable def cons (_name : Name) (p rest : Prop)
    (_stx : Option Syntax := none) : Prop := p ∧ rest


private def getName (name : Expr) : MetaM Name := do
  let name ← whnfR name
  let some name := name.name?
    | throwError "invalid NamedProp name: {name}"
  return name

private def getOne? (type : Expr) : MetaM (Option (Name × Expr)) := do
  let type ← instantiateMVars type
  match_expr type with
  | NamedProp.one name prop _stx =>
      return some (← getName name, prop)
  | _ => return none

private def getCons? (type : Expr) : MetaM (Option Name) := do
  let type ← instantiateMVars type
  match_expr type with
  | NamedProp.cons name _prop _rest _stx =>
      return some (← getName name)
  | _ => return none

public partial def containsNamedProp (type : Expr) : Bool :=
  if type.isAppOf ``NamedProp.one || type.isAppOf ``NamedProp.cons then
    true
  else if type.isAppOfArity ``And 2 then
    containsNamedProp (type.getArg! 0) || containsNamedProp (type.getArg! 1)
  else
    false

/--
Unwrap and name every `NamedProp` hypothesis in a goal. A `one` hypothesis is
changed to its underlying proposition and renamed. A `cons` hypothesis is
split, its head receives the encoded name, and its tail is processed
recursively.
-/
public partial def processNamedPropHyp (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      if let some (name, prop) ← getOne? localDecl.type then
        let goal ← goal.rename localDecl.fvarId name
        let goal ← goal.replaceLocalDeclDefEq localDecl.fvarId prop
        return ← processNamedPropHyp goal
      if let some name ← getCons? localDecl.type then
        let fieldNames : Array AltVarNames :=
          #[{ explicit := true, varNames := [name, `_namedPropRest] }]
        let subgoals ← goal.cases localDecl.fvarId fieldNames
        return ← subgoals.toList.flatMapM fun subgoal =>
          processNamedPropHyp subgoal.mvarId
      let type ← instantiateMVars localDecl.type
      if type.isAppOfArity ``And 2 && containsNamedProp type then
        let subgoals ← goal.cases localDecl.fvarId
        return ← subgoals.toList.flatMapM fun subgoal =>
          processNamedPropHyp subgoal.mvarId
    return [goal]

/--
Unwrap and name a `NamedProp` goal. A `one` goal is changed to its underlying
proposition and tagged with its encoded name. A `cons` goal is split into a
named head goal and a recursively processed tail.
-/
public partial def processNamedPropGoal (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    let target ← goal.getType
    if let some (name, prop) ← getOne? target then
      let goal ← goal.replaceTargetDefEq prop
      goal.setTag name
      return [goal]
    if let some name ← getCons? target then
      match ← goal.constructor with
      | [head, tail] =>
          head.setTag name
          return head :: (← processNamedPropGoal tail)
      | goals =>
          throwError "expected NamedProp.cons to produce two goals, got {goals.length}"
    return [goal]

public def mkNamedPropList (ts : Array (TSyntax `term)) (names : Array (Option Name) := #[])
    (pfx : String := "clause") : MacroM (TSyntax `term) := do
  if ts.isEmpty then
    `(term| True)
  else
    let namedPropOne := mkIdent ``NamedProp.one
    let namedPropCons := mkIdent ``NamedProp.cons
    let getName (i : Nat) : MacroM (TSyntax `term) := do
      let name := match names[i]? with
        | some (some name) => name.toString
        | _ => s!"{pfx}{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let getStx (i : Nat) : MacroM (TSyntax `term) := do
      let text := ts[i]!.raw.reprint.getD (toString (ts[i]!.raw.formatStx))
      let textStr := Lean.Syntax.mkStrLit text
      `(some (Lean.Syntax.atom Lean.SourceInfo.none $textStr))
    let lastIdx := ts.size - 1
    let mut result ← `($namedPropOne ($(← getName lastIdx)) $(ts[lastIdx]!) ($(← getStx lastIdx)))
    for i in List.range lastIdx |>.reverse do
      result ← `($namedPropCons ($(← getName i)) $(ts[i]!) $result ($(← getStx i)))
    return result

end NamedProp
