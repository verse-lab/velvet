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
public import Velvet2.Named

open Lean Meta Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal

namespace Velvet2.VCGen

private theorem prodFstMk {α : Type u} {β : Type v} (a : α) (b : β) :
    (a, b).fst = a := rfl

private theorem prodSndMk {α : Type u} {β : Type v} (a : α) (b : β) :
    (a, b).snd = b := rfl

/-- Narrow methods for simplifying generated concrete control flow and projections. -/
public def mkGeneratedControlSimpMethods : MetaM Sym.Simp.Methods := do
  let mut thms : Sym.Simp.Theorems := {}
  for declName in #[``Sum.isRight_inl, ``Sum.isRight_inr, ``prodFstMk, ``prodSndMk] do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
  return { pre := Sym.Simp.simpControl, post := Sym.Simp.evalGround >> thms.rewrite }

/--
Introduce all leading binders of `goal` in one pass, naming the `i`-th binder `overrides[i]` when
given and the binder's own name otherwise. Accessibility is decided by `tactic.hygienic` via
`mkFreshBinderNameForTactic`. The introduction itself is a single `Sym.intros` call (which keeps
the memoized, sharing-correct intro); only the names are chosen here. Returns the goal unchanged
when there are no leading binders.

Vendored from Lean's `Lean.Elab.Tactic.Do.Internal.VCGen.Util`.
-/
public def introsHygienic (goal : MVarId) (overrides : Array Name := #[]) : VCGenM MVarId :=
  goal.withContext do
    let rec collectAndNormalizeBinders (type : Expr) (acc : Array (Name × Bool)) :
        VCGenM (Expr × Array (Name × Bool)) := do
      match type with
      | .forallE binderName binderType body binderInfo =>
          let binderTypeOrig := binderType
          let binderType ← match ← Sym.simp binderType (← mkGeneratedControlSimpMethods) with
            | .rfl .. => pure binderType
            | .step binderType _ .. => pure binderType
          let (binderType, entry) ← match ← Named.extract? binderType with
            | some (name, value) => pure (value, (name, true))
            | none => pure (binderType, (binderName, false))
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

end Velvet2.VCGen
