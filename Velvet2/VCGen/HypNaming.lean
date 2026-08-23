module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.Util
public import Lean.Elab.Tactic.Do.VCGen.Split
public import Lean.Meta.Sym.AbstractS
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Sym.InstantiateS
public import Velvet2.Named

open Lean Meta Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal

namespace Velvet2.VCGen

open Lean.Elab.Tactic.Do (SplitInfo)

/-
This file adds a wrapper which provides support for local hypotheses naming.

Strategy:
1. For if-then-else expressions, both branches get `if_cond` name.
2. For dependent if-then-else expressions `if h : cond then .. else ...` the name is `h`.
3. For a hypothesis which comes from a constructor equality `x = .ctor arg1 ...` the name is `h_ctor`
4. For matcher arguments the name is already given, now it is accessible.

The implementation below adds a name for universally quantified arguments at the goal's head, therefore
`introsHygienic` can correctly process them.

Examples are at `Examples/HypNaming.lean`
-/

public def defaultIfGuardName : Name := `if_cond

/-- The name if it can serve as a user-facing hypothesis name; `none` for compiler-generated
(macro-scoped), anonymous and `_` binders. -/
private def usableName? (n : Name) : Option Name :=
  if n.hasMacroScopes || n == `_ || n.isAnonymous then none else some n

/-- Reflect a `Name` as an expression that `Lean.Expr.name?` (and hence `Named.extract?`)
can decode. -/

def mkInstOfNatNatS (n : Expr) : SymM Expr := do
  mkAppS (<- mkConstS ``instOfNatNat) n

def mkNatLitCoreS (n : Expr) : SymM Expr := do
  mkAppS₃  (<- mkConstS ``OfNat.ofNat [Level.zero]) (<- mkConstS ``Nat) n (<-mkInstOfNatNatS n)

private def mkNameLit (nm: Name  ) : SymM Expr := do
   match nm with
  | .anonymous => mkConstS ``Lean.Name.anonymous
  | .str p s => mkAppS₂ (<- mkConstS ``Lean.Name.str) (<- mkNameLit p) (<- mkLitS (Literal.strVal s ))
  | .num p i => mkAppS₂ (<- mkConstS ``Lean.Name.num) (<- mkNameLit p) (<- mkNatLitCoreS (<- mkLitS (Literal.natVal i)))

/-- The guard name of an `ite`/`dite` split, shared by both branches. `none` for matchers, whose
binders name themselves. -/
private def guardName? (splitInfo : SplitInfo) : Option Name :=
  match splitInfo with
  | .ite _ => defaultIfGuardName
  | .dite e =>
      let binderName (alt : Expr) : Option Name :=
        match alt with
        | .lam n _ _ _ => usableName? n
        | _ => none
      binderName (e.getArg! 3) <|> binderName (e.getArg! 4) |>.getD defaultIfGuardName
  | .matcher _ => none

/-- Generate a name for hypothesis which comes from a constructor equation. Given a hypothesis
x = .ctor arg1 ..., return a name `h_ctor`. -/
private def ctorEqName? (dom : Expr) : SymM (Option Name) := do
  let_expr Eq _α lhs rhs := dom | return none
  for side in [rhs, lhs] do
    let .const declName _ := side.getAppFn | continue
    unless (← getEnv).find? declName matches some (.ctorInfo _) do continue
    let some ctor := declName.componentsRev.head? | continue
    return some (Name.mkSimple s!"h_{ctor}")
  return none

/-- `Named.mk name none dom`, which is definitionally `dom`. `none` when `dom` is already
annotated, or is not a type and so has no binder to name. -/
private def mkNamedDomain? (name : Name) (dom : Expr) : SymM (Option Expr) := do
  if dom.isAppOfArity ``Named.mk 4 then return none
  let .sort v ← whnf (← inferType dom) | return none
  let noneStx <- mkAppS (<- mkConstS ``Option.none [Level.zero]) (<- mkConstS ``Lean.Syntax)
  return some <| (<- mkAppS₄  (<- mkConstS ``Named.mk [.succ v]) (<- mkSortS v) (<- mkNameLit name) noneStx dom)


/-- The name for the binder `binderName : dom`, or `none` to leave it inaccessible. -/
private def nameFor : Option Name → Name → Expr → SymM (Option Name)
  | .some name, _, _ => return some name
  | .none, binderName, dom => do
      if let some name := usableName? binderName then return some name
      ctorEqName? dom

/--
Rebuild the leading `∀` telescope of `type`, annotating each binder's domain with the name `naming`.
Second argument flags whether anything changed.
-/
private partial def annotateBinders (naming : Option Name) (type : Expr) :
    SymM (Expr × Bool) := do
  let .forallE binderName dom body binderInfo := type | return (type, false)
  let dom? ← match ← nameFor naming binderName dom with
    | none => pure none
    | some name => mkNamedDomain? name dom
  withLocalDecl binderName binderInfo (dom?.getD dom) fun x => do
    let x ← mkFVarS x.fvarId!
    let body ← instantiateS body #[x]
    let (body, changed) ← match naming with
      | .some _ => pure (body, false)
      | .none => annotateBinders naming body
    if dom?.isNone && !changed then return (type, false)
    return (← mkForallFVarsS #[x] body, true)

/-- `annotateBinders` applied to `goal`'s target. `goal` is returned unchanged when no binder was
annotated, which keeps the target's sharing intact. -/
private def annotateLeadingBinders (goal : MVarId) (naming : Option Name) : VCGenM MVarId :=
  goal.withContext do
    let target ← goal.getType
    unless target.isForall do return goal
    let (target, changed) ← annotateBinders naming target
    unless changed do return goal
    goal.replaceTargetDefEqFast (← shareCommon target)

/--
Add naming of hypotheses from ite/dite/matcher to a list of goals.
Processes each goal individually using `annotateLeadingBinders`
-/
public def nameSplitBranchHyps (splitInfo : SplitInfo) (goals : List MVarId) :
    VCGenM (List MVarId) := do
  goals.mapM (annotateLeadingBinders · (guardName? splitInfo))

end Velvet2.VCGen
