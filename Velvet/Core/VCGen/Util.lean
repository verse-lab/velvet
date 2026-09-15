/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Data.Sum.Basic
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.Util
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Sym.Intro
public import Lean.Meta.Sym.Simp.ControlFlow
public import Lean.Meta.Sym.Simp.EvalGround
public import Lean.Meta.Sym.Simp.Rewrite
public import Velvet.Core.Named

open Lean Meta Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal
open Lean.Elab.Tactic.Do.Internal.VCGen

namespace VCGen

public theorem prodFstMk {α : Type u} {β : Type v} (a : α) (b : β) :
    (a, b).fst = a := rfl

public theorem prodSndMk {α : Type u} {β : Type v} (a : α) (b : β) :
    (a, b).snd = b := rfl

/-- Narrow methods for simplifying generated concrete control flow and projections. -/
public def mkGeneratedControlSimpMethods : MetaM Sym.Simp.Methods := do
  let mut thms : Sym.Simp.Theorems := {}
  for declName in #[``Sum.isRight_inl, ``Sum.isRight_inr,
      ``prodFstMk, ``prodSndMk,
      ``Lean.Order.CompleteLattice.ofProp_apply] do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
  return {
    pre := fun e => do
      if let some (_, _, structExpr) := e.app3? ``Prod.fst then
        if let some (_, _, a, _) := structExpr.app4? ``Prod.mk then
          return .step a (← mkAppM ``Eq.refl #[a]) (done := false)
      if let some (_, _, structExpr) := e.app3? ``Prod.snd then
        if let some (_, _, _, b) := structExpr.app4? ``Prod.mk then
          return .step b (← mkAppM ``Eq.refl #[b]) (done := false)
      if let .proj _ idx structExpr := e then
        if let some (_, _, a, b) := structExpr.app4? ``Prod.mk then
          let res := if idx == 0 then a else b
          return .step res (← mkAppM ``Eq.refl #[res]) (done := false)
      let e' := e.headBeta
      if isSameExpr e e' then Sym.Simp.simpControl e else
        return .step e' (← mkAppM ``Eq.refl #[e']) (done := false)
    post := thms.rewrite
  }

/-- Defeq reduction for tuple projections and simple control redexes. -/
public partial def reduceDefEqProjs (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if let some (_, _, structExpr) := e.app3? ``Prod.fst then
    let structExpr ← reduceDefEqProjs structExpr
    if let some (_, _, a, _) := structExpr.app4? ``Prod.mk then
      return ← reduceDefEqProjs a
  if let some (_, _, structExpr) := e.app3? ``Prod.snd then
    let structExpr ← reduceDefEqProjs structExpr
    if let some (_, _, _, b) := structExpr.app4? ``Prod.mk then
      return ← reduceDefEqProjs b
  if let .proj _ idx structExpr := e then
    let structExpr ← reduceDefEqProjs structExpr
    if let some (_, _, a, b) := structExpr.app4? ``Prod.mk then
      let res := if idx == 0 then a else b
      return ← reduceDefEqProjs res
  if let some (_, _, arg) := e.app3? ``Sum.isRight then
    let arg ← reduceDefEqProjs arg
    if arg.isAppOf ``Sum.inl then
      return mkConst ``Bool.false
    if arg.isAppOf ``Sum.inr then
      return mkConst ``Bool.true
  match e with
  | .app f a =>
    let f' ← reduceDefEqProjs f
    let a' ← reduceDefEqProjs a
    return e.updateApp! f' a'
  | .lam _ type body bi =>
    let type' ← reduceDefEqProjs type
    let body' ← reduceDefEqProjs body
    return e.updateLambda! bi type' body'
  | .forallE _ type body bi =>
    let type' ← reduceDefEqProjs type
    let body' ← reduceDefEqProjs body
    return e.updateForall! bi type' body'
  | .letE _ type val body nondep =>
    let type' ← reduceDefEqProjs type
    let val' ← reduceDefEqProjs val
    let body' ← reduceDefEqProjs body
    return e.updateLet! type' val' body' nondep
  | .mdata data val =>
    let val' ← reduceDefEqProjs val
    if isSameExpr val val' then pure e else pure (.mdata data val')
  | _ => pure e

/-- Count leading binders, stopping before a product that `solve` must split first.
Backported from the newer Lean VCGen alongside `splitProdBinder`. -/
public def numBindersToIntro : Expr → Nat
  | .forallE _ d b _ => if d.isAppOf ``Prod then 0 else numBindersToIntro b + 1
  | .letE _ _ _ b _ => numBindersToIntro b + 1
  | _ => 0

/--
Introduce all leading `∀`/`let` binders of `goal` in a single `Sym.intros` pass (keeping the
introduction sharing-correct and memoized), with two localisations over the upstream
`introsHygienic`:

1. **`Named` hypotheses keep their user-facing name.** Our `named[…]` machinery wraps a
   hypothesis as `Named.mk name src P`. When such a precondition is lifted into an implication and
   introduced, the upstream helper only reads the binder's syntactic name, so the hypothesis shows
   up under a generated, inaccessible name (marked `✝`) instead of `name`. We instead look inside
   the binder's *type*: `collectAndNormalizeBinders` strips the outer `Named.mk` wrapper
   (definitionally), records `name`, and introduces the hypothesis under that name. Ordinary
   (non-`Named`) binders keep Lean's default naming.

2. **Binder domains are cleaned up first.** Each binder's type is run through
   `reduceDefEqProjs`, so leftover generated control flow (branch guards, tuple
   projections) are reduced before the binder is introduced.

`collectAndNormalizeBinders` rebuilds only the binders that actually changed (`mkForallS`/`mkLetS`)
and returns the rest unchanged, to avoid rebuilds and preserve sharing. `overrides[i]`, when given,
wins over both the `Named` name and the syntactic name for the `i`-th binder. Returns `goal`
unchanged when there are no leading binders.

Vendored from `Lean.Elab.Tactic.Do.Internal.VCGen.Util` (which only reads syntactic binder names
and neither normalizes domains nor understands `Named.mk`).
-/
public def introsHygienic (goal : MVarId) (overrides : Array Name := #[]) : VCGenM MVarId :=
  goal.withContext do
    let rec collectAndNormalizeBinders (type : Expr) (acc : Array (Name × Bool)) :
        VCGenM (Expr × Array (Name × Bool)) := do
      match type with
      | .forallE binderName binderType body binderInfo =>
          if binderType.isAppOf ``Prod && acc.size ≥ overrides.size then
            return (type, acc)
          let binderTypeOrig := binderType
          let (binderType, entry) ← match ← Named.extract? binderType with
            | some (name, value) => pure (value, (name, true))
            | none => pure (binderType, (binderName, false))
          let binderType ← reduceDefEqProjs binderType
          let (body', acc) ← collectAndNormalizeBinders body (acc.push entry)
          if isSameExpr binderTypeOrig binderType && isSameExpr body body' then
            return (type, acc)
          return (← mkForallS binderName binderInfo binderType body', acc)
      | .letE binderName binderType value body nondep =>
          let (body', acc) ← collectAndNormalizeBinders body (acc.push (binderName, false))
          if isSameExpr body body' then return (type, acc)
          return (← mkLetS binderName binderType value body' nondep, acc)
      | _ => return (type, acc)
    let target ← goal.getType
    let (target', binders) ← collectAndNormalizeBinders target #[]
    if binders.isEmpty then return goal
    let goal ← if isSameExpr target target' then
      pure goal
    else
      goal.replaceTargetDefEqFast target'
    let lctx ← getLCtx
    let mut names := #[]
    for h : i in *...binders.size do
      let (binderName, isNamed) := binders[i]
      let name := overrides[i]?.getD binderName
      let name ← if isNamed && overrides[i]?.isNone then
        pure (lctx.getUnusedName name)
      else
        Meta.mkFreshBinderNameForTactic name
      names := names.push name
    let .goal _ goal ← Sym.intros goal names | return goal
    return goal

/--
Solves conjunctions whose leaves are `True` or `e₁ = e₂`, and returns a residual goal containing
exactly the conjuncts that could not be solved.
The goal is head-reduced first, so a conjunction that a `match` on a constructor or a projection
of a tuple leaves behind a redex is still recognized.
This procedure may assign metavariables in `e₁`/`e₂`, for example for `e = ?m` it will assign
`?m := e`.
-/
public partial def solveTrivialConjuncts (goal : MVarId) : VCGenM (Option MVarId) :=
    goal.withContext do
  let ctx ← read
  let ty ← instantiateMVars (← goal.getType)
  let ty := ty.consumeMData
  let (goal, ty) ← match ← reduceHead? ty with
    | some ty' => pure (← goal.replaceTargetDefEqFast ty', ty')
    | none => pure (goal, ty)
  let ty := ty.consumeMData
  if ty.isAppOf ``True then
    goal.assign (mkConst ``True.intro)
    return none
  else if ty.isAppOf ``And then
    let tag ← goal.getTag
    let .goals [g₁, g₂] ← ctx.backwardRules.andIntro.applyChecked goal
      | throwError "solveTrivialConjuncts: failed to apply {.ofConstName ``And.intro} to{indentExpr ty}"
    match ← solveTrivialConjuncts g₁, ← solveTrivialConjuncts g₂ with
    | none,    none    => return none
    | some g,  none    => do
      if (← g.getTag).isAnonymous then g.setTag tag
      return some g
    | none,    some g  => do
      if (← g.getTag).isAnonymous then g.setTag tag
      return some g
    | some g₁', some g₂' =>
      let t₁ ← g₁'.getType
      let t₂ ← g₂'.getType
      let combined ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``And) t₁ t₂)
      g₁'.assign (mkApp3 (mkConst ``And.left) t₁ t₂ combined)
      g₂'.assign (mkApp3 (mkConst ``And.right) t₁ t₂ combined)
      combined.mvarId!.setTag tag
      return some combined.mvarId!
  else if let some (ty, lhs, rhs) := ty.app3? ``Eq then
    let lhs ← reduceHead lhs
    let rhs ← reduceHead rhs
    let u ← Meta.getLevel ty
    let goal ← goal.replaceTargetDefEqFast (mkApp3 (mkConst ``Eq [u]) ty lhs rhs)
    -- Synthetic opaque metavariables (e.g. invariant holes) stay rigid; natural
    -- metavariables may be assigned (e.g. `?m := e` for `e = ?m` leaves).
    if ← isDefEqS lhs rhs then
      goal.assign (mkApp2 (mkConst ``Eq.refl [← Meta.getLevel ty]) ty lhs)
      return none
    else
      return some goal
  else
    return some goal

end VCGen
