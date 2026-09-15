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
public import Lean.Meta.Transform
public import Lean.Meta.Sym.AbstractS
public import Lean.Meta.Sym.InstantiateS
public import Lean.Meta.Sym.Simp.ControlFlow
public import Lean.Meta.Sym.Simp.Rewrite
public import Velvet.Core.Named

open Lean Meta Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal
open Lean.Elab.Tactic.Do.Internal.VCGen

namespace VCGen

/-!
Introduction and VC cleanup follow Lean nightly-2026-08-22, with Velvet's named-clause
handling and simplification. Unchanged utilities are imported from the v4.34 toolchain.
-/

/-- Narrow methods for simplifying generated control flow and applied pure embeddings. -/
public def mkGeneratedControlSimpMethods : MetaM Sym.Simp.Methods := do
  let mut thms : Sym.Simp.Theorems := {}
  for declName in #[``Sum.isRight_inl, ``Sum.isRight_inr,
      ``Lean.Order.CompleteLattice.ofProp_apply] do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
  return {
    pre := fun e => do
      let some e' ← reduceHead? e | return ← Sym.Simp.simpControl e
      return .step e' (← mkAppM ``Eq.refl #[e']) (done := false)
    post := thms.rewrite
  }

/-- Whether `n` is a program variable's own name: no macro scopes and no implementation-detail
`__` prefix. Such a name stays accessible in a verification condition. -/
public def isProgramName (n : Name) : Bool :=
  !n.hasMacroScopes && !n.isImplementationDetail

/-- Count leading binders, stopping before a product that `solve` must split first.
Backported from the newer Lean VCGen alongside `splitProdBinder`. -/
public def numBindersToIntro : Expr → Nat
  | .forallE _ d b _ => if d.isAppOf ``Prod then 0 else numBindersToIntro b + 1
  | .letE _ _ _ b _ => numBindersToIntro b + 1
  | _ => 0

/-- Prepare the first `n` binders before `Sym.intros` introduces them into the goal.

Worked example, preparing all three binders (`Named[bound] P` abbreviates a `Named.mk`
wrapper with clause name `bound` and value `P`; `R` is any predicate on two naturals):
```
input:  ∀ (a b : Nat), ∀ (h : Named[bound] ((a, b).fst ≤ b)), R a b
output: ∀ (a b : Nat), ∀ (h : a ≤ b), R a b
names:  #[(a, false), (b, false), (bound, true)]
```
The Boolean records whether a clause supplied the name. `Sym.intros` will later introduce
the last hypothesis as `bound`; preparation itself leaves the binder named `h`.

As we descend, `withLocalDecl` gives each earlier binder a temporary local declaration.
At `h`, we have `fvars = #[a, b]`. Its domain still uses bound-variable indices: `#0`
refers to the nearest earlier binder (`b`), and `#1` to `a`. The steps for that domain are:
```
original domain:       Named[bound] ((#1, #0).fst ≤ #0)
instantiateRevS:       Named[bound] ((a, b).fst ≤ b)
Named.extract?:        (a, b).fst ≤ b       -- also save (bound, true)
transform/reduceHead:  a ≤ b
```
Reduction now sees locals whose types it can look up. We share the expressions before
using Sym operations, including each fresh local returned by `withLocalDecl`.

We next visit the body with `fvars = #[a, b, h]`. With no binders left to prepare, it
returns `R #2 #1` unchanged: the body still uses indices, with `#0` reserved for `h`.
On the way back out, `abstractFVars (a ≤ b) #[a, b]` restores the domain `#1 ≤ #0`.
`mkForallS` attaches that domain to the already rebuilt body. Repeating this for `b` and
`a` yields the output above, with no temporary locals escaping into the result.

A let binder also occupies an index. For `∀ a : Nat, let b := a + 1; P a b → Q`, the
domain `P #1 #0` opens to `P a b` using `#[a, b]`. Here `b` is a temporary local of type
`Nat`; we do not substitute `a + 1`. Rebuilding restores the original let and its value. -/
private def prepareIntroBinders (type : Expr) (n : Nat) :
    VCGenM (Expr × Array (Name × Bool)) := do
  let rec visit (n : Nat) (type : Expr) (fvars : Array Expr)
      (acc : Array (Name × Bool)) : VCGenM (Expr × Array (Name × Bool)) := do
    match n, type with
    | 0, _ => return (type, acc)
    | n+1, .forallE nm domain body bi =>
        -- Open this domain using the earlier binders, e.g. `P #0` becomes `P x`.
        let domain ← instantiateRevS domain fvars
        -- Save the clause name before removing its wrapper from the hypothesis type.
        let (domain, entry) ← match ← Named.extract? domain with
          | some (name, value) => pure (value, (name, true))
          | none => pure (domain, (nm, false))
        -- Reduce subexpressions too, e.g. `P ((x, y).fst)` becomes `P x`.
        -- Meta.transform supplies locals for nested binders; share its expressions
        -- before passing them to Sym operations, which require maximal sharing.
        let domain ← Meta.transform domain (post := fun e =>
          return .done (← reduceHead (← shareCommon e)))
        let domain ← shareCommon domain
        -- Later domains may depend on this binder and need its normalized type.
        withLocalDecl nm bi domain fun x => do
          let x ← shareCommon x
          let (body', acc) ← visit n body (fvars.push x) (acc.push entry)
          -- Restore bound-variable indices. Recursion has already rebuilt body'.
          return (← mkForallS nm bi (← Sym.abstractFVars domain fvars) body', acc)
    | n+1, .letE nm domain value body nondep =>
        -- Account for this binder in later domains, but preserve the original let.
        -- Its temporary local supplies a type; its value is not unfolded here.
        withLocalDecl nm .default (← instantiateRevS domain fvars) fun x => do
          let x ← shareCommon x
          let (body', acc) ← visit n body (fvars.push x) (acc.push (nm, false))
          return (← mkLetS nm domain value body' nondep, acc)
    | _, _ => return (type, acc)
  visit n type #[] #[]

/-- Introduce the first `n` binders hygienically, keeping named clauses accessible. -/
public def introsHygienicN (goal : MVarId) (n : Nat) : VCGenM MVarId :=
  goal.withContext do
    let target ← goal.getType
    let (target', binders) ← prepareIntroBinders target n
    if binders.isEmpty then return goal
    let goal ← if isSameExpr target target' then pure goal else goal.replaceTargetDefEqFast target'
    let lctx ← getLCtx
    let mut names := #[]
    for (nm, isNamed) in binders do
      let name ← if isNamed then pure (lctx.getUnusedName nm) else Meta.mkFreshBinderNameForTactic nm
      names := names.push name
    let .goal _ goal ← Sym.intros goal names | return goal
    return goal

/-- `introsHygienicN` for every non-`Prod` binder the goal leads with. -/
public def introsHygienic (goal : MVarId) : VCGenM MVarId := do
  introsHygienicN goal (numBindersToIntro (← goal.getType))

/--
Solves conjunctions whose leaves are `True` or `e₁ = e₂`, and returns a residual goal containing
exactly the conjuncts that could not be solved.
The goal is head-reduced first, so a conjunction that a `match` on a constructor or a projection
of a tuple leaves behind a redex is still recognized.
This procedure may assign metavariables in `e₁`/`e₂`, for example for `e = ?m` it will assign
`?m := e`.
-/
public partial def cleanupVC (goal : MVarId) : VCGenM (Option MVarId) :=
    goal.withContext do
  let ctx ← read
  let ty ← instantiateMVars (← goal.getType)
  let (goal, ty) ← match ← reduceHead? ty with
    | some ty' => pure (← goal.replaceTargetDefEqFast ty', ty')
    | none => pure (goal, ty)
  -- The reducer looks through metadata but can leave it on the returned expression.
  -- Strip outer wrappers before testing for True, And, or Eq.
  let ty := ty.consumeMData
  if ty.isAppOf ``True then
    goal.assign (mkConst ``True.intro)
    return none
  else if ty.isAppOf ``And then
    let tag ← goal.getTag
    let .goals [g₁, g₂] ← ctx.backwardRules.andIntro.applyChecked goal
      | throwError "cleanupVC: failed to apply {.ofConstName ``And.intro} to{indentExpr ty}"
    match ← cleanupVC g₁, ← cleanupVC g₂ with
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
