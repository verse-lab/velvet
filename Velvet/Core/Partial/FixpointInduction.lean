module

public import Velvet.Core.Partial.Defs
public meta import Velvet.Core.Partial.Defs
public meta import Lean.Elab.Tactic

/-!
# Fixpoint induction

`fixpoint_induction M` proves a goal about a function `M` defined by `partial_fixpoint`, by
applying the induction principle that Lean generates for it, `M.fixpoint_induct`.

## Running example

The comments in this file follow one function through the tactic:

```lean
def foo (n m acc : Nat) : Option Nat :=
  if n = 0 then pure (acc + m) else foo (n - 1) m (acc + 1)
partial_fixpoint

theorem foo_spec :
    ∀ n m acc, ⦃ True ⦄ foo n m acc ⦃ fun res => ⌜res = acc + n + m⌝ ; fun _ => ⌜True⌝ ⦄ := by
  fixpoint_induction foo
  all_goals velvet_vcgen with finish
```

The recursive call changes `n` and `acc`, but passes `m` unchanged. Lean notices this and builds the
fixpoint over `n` and `acc` only, for each `m`. So `m` is a *fixed* parameter, `n` and `acc` are
*varying* ones, and the induction principle is stated for one `m`, bound before the motive:

```
foo.fixpoint_induct : ∀ (m : Nat) (motive : (Nat → Nat → Option Nat) → Prop),
  admissible motive →
  (∀ f, motive f →
    motive (fun n acc => if n = 0 then pure (acc + m) else f (n - 1) (acc + 1))) →
  motive (fun n => foo n m)
```

`f : Nat → Nat → Option Nat` is an *approximation* of `foo` at this `m`: a function of `n` and `acc`
only, which `foo` is the limit of. The motive is a property of approximations. The second premise
is the induction step: if `f` has the property, so has the body of `foo` with its recursive call
made to `f`. The first premise, admissibility, says that the property carries over to the limit,
`foo` itself (`Lean.Order.admissible`). (Lean's lemma calls the approximation `foo`, and so does
the step goal the tactic leaves, as `foo✝`.)

## Steps

We write `post n m acc` for `fun res => ⌜res = acc + n + m⌝ ; fun _ => ⌜True⌝`. The goal is

```
⊢ ∀ (n m acc : Nat), ⦃ True ⦄ foo n m acc ⦃ post n m acc ⦄
```

and the plan is to `apply foo.fixpoint_induct m motive` for the right `motive`. That needs `m` as
a variable in the context, since the lemma takes it, and the goal to be the lemma's conclusion,
`motive (fun n => foo n m)`.

**Step 1.** Introduce all of the goal's binders, which makes `m` a variable:

```
n m acc : Nat
⊢ ⦃ True ⦄ foo n m acc ⦃ post n m acc ⦄
```

**Step 2.** Build the motive (`abstractCalls`): replace each call `foo n m acc` by `f n acc`, and
quantify over the binders other than `m`.

The tactic does not work out itself which parameters are fixed: it reads them off
`foo.fixpoint_induct`, which Lean generated knowing them. Its conclusion is about
`fun n => foo n m`, that is `fun n acc => foo n m acc`, so `m` is fixed and `n` and `acc` vary.
With the binders of `foo.fixpoint_induct` as metavariables, its conclusion is about
`fun n => foo n ?m`, which the tactic expands to `fun n acc => foo n ?m acc`. Matching the goal's
call `foo n m acc` against `foo ?n ?m ?acc` assigns `?m := m`, which shows that the goal's `m` is
the fixed one. The goal does not change.

```
motive := fun f => ∀ n acc, ⦃ True ⦄ f n acc ⦃ post n m acc ⦄
```

**Step 3.** Turn the goal into `motive (fun n => foo n m)`. Unfolded, that is
`∀ n acc, ⦃ True ⦄ foo n m acc ⦃ post n m acc ⦄`: `n` and `acc` quantified, as in the motive.
Step 1 introduced them, so put them back with `revert n acc`, keeping `m`:

```
m : Nat
⊢ ∀ (n acc : Nat), ⦃ True ⦄ foo n m acc ⦃ post n m acc ⦄
```

**Step 4.** Apply `foo.fixpoint_induct m motive`. Its two premises become the goals `adm` and
`step`. In `step`, introduce the approximation as `foo✝` and its hypothesis as `ih✝`:

```
case adm
m : Nat
⊢ admissible fun f => ∀ (n acc : Nat), ⦃ True ⦄ f n acc ⦃ post n m acc ⦄

case step
m : Nat
foo✝ : Nat → Nat → Option Nat
ih✝ : ∀ (n acc : Nat), ⦃ True ⦄ foo✝ n acc ⦃ post n m acc ⦄
⊢ ∀ (n acc : Nat),
    ⦃ True ⦄ if n = 0 then pure (acc + m) else foo✝ (n - 1) (acc + 1) ⦃ post n m acc ⦄
```

**Step 5.** Prove `adm` by the shape of the motive (`proveAdmissible`), layer by layer. The triple
leaves the condition that its `signals` allow divergence, so `adm` becomes:

```
case hdiv
m n acc : Nat
⊢ True ⊑ ⌜True⌝
```

The tactic leaves `step` and `hdiv`. `all_goals velvet_vcgen with finish` closes both, using `ih✝`
at the call `foo✝ (n - 1) (acc + 1)`.
-/

open Lean Meta Elab Tactic

namespace Velvet.FixpointInduction

/-- Step 2: replace each call of `fnName` in `goal` by `f` applied to its varying arguments.

`target` is what `M.fixpoint_induct` concludes about, with metavariables for the fixed parameters.
In the running example:
```
target:  fun n => foo n ?m
f:       Nat → Nat → Option Nat
goal:    ⦃ True ⦄ foo n m acc ⦃ post n m acc ⦄
result:  ⦃ True ⦄ f n acc ⦃ post n m acc ⦄          -- and ?m := m
```
The first call matched assigns `?m`. A call that passes another value for `m` is then left
unchanged: the induction is about one `m`. -/
meta def abstractCalls (fnName : Name) (target goal f : Expr) : MetaM Expr := do
  -- Lean eta-reduces the target: `fun n acc => foo n ?m acc` is written `fun n => foo n ?m`. Bind
  -- one variable per parameter of `f` again: `fun n acc => foo n ?m acc`. (`Meta.etaExpand` would
  -- also expand over the state of a `StateT` program, since it unfolds the type.)
  let target ← forallTelescope (← inferType f) fun xs _ => mkLambdaFVars xs (target.beta xs)
  Meta.transform goal (pre := fun e => do
    unless e.getAppFn.isConstOf fnName do return .continue
    -- `varying := #[?n, ?acc]`, `call := foo ?n ?m ?acc`.
    let (varying, _, call) ← lambdaMetaTelescope target
    -- `foo n m acc =?= foo ?n ?m ?acc` assigns `?n := n`, `?m := m` and `?acc := acc`.
    unless ← isDefEq e call do return .continue
    -- `foo n m acc` becomes `f n acc`.
    return .done (mkAppN f (← varying.mapM instantiateMVars)))

/-- Step 5, one layer: the lemma reducing `admissible (fun f => body)` to the admissibility of the
parts of `body`, chosen by the outermost shape of `body`. In the running example, each row is a
goal and the lemma applied to it, and the next row is the goal that lemma leaves:
```
admissible fun f => ∀ n acc, ⦃ True ⦄ f n acc ⦃ … ⦄    ∀ n:     admissible_pi
admissible fun f => ∀ acc, ⦃ True ⦄ f n acc ⦃ … ⦄      ∀ acc:   admissible_pi
admissible fun f => ⦃ True ⦄ f n acc ⦃ … ⦄             f n:     admissible_apply
admissible fun c => ⦃ True ⦄ c acc ⦃ … ⦄               c acc:   admissible_apply
admissible fun c => ⦃ True ⦄ c ⦃ … ⦄                   triple:  admissible_triple
True ⊑ ⌜True⌝                                          (hdiv)
```
Throws when no lemma fits. -/
meta def admissibleRule (α f body : Expr) : MetaM Expr := do
  -- `∀ y, b`: admissible if `b` is, for every `y`.
  if let .forallE n d b bi := body then
    let P ← withLocalDecl n bi d fun y => mkLambdaFVars #[f, y] (b.instantiate1 y)
    return ← mkAppOptM ``Lean.Order.admissible_pi #[none, none, none, P]
  -- `l ∧ r`: admissible if both are.
  if let some (l, r) := body.and? then
    return ← mkAppOptM ``Lean.Order.admissible_and
      #[none, none, ← mkLambdaFVars #[f] l, ← mkLambdaFVars #[f] r]
  -- `⦃ pre ⦄ f ⦃ post ; epost ⦄`: admissible if `pre ⊑ div_pre epost` (`hdiv`).
  if body.isAppOfArity ``Std.WP.Triple 11 && body.getArg! 6 == f then
    return ← mkConstWithFreshMVarLevels ``WPPartial.admissible_triple
  -- `f` is a function, called as `f a …`: replace `f a` by a variable `c`, and continue with `c`.
  -- `⦃ True ⦄ f n acc ⦃ … ⦄` becomes `fun c => ⦃ True ⦄ c acc ⦃ … ⦄`, for `a := n`.
  let .forallE x A T _ := α | throwError "no admissibility rule"
  let some call := body.find? (·.getAppFn == f) |>.filter (·.isApp)
    | throwError "no admissibility rule"
  let a := call.getArg! 0
  let P := mkLambda x .default A (mkLambda `c .default T (← kabstract body (mkApp f a)))
  mkAppOptM ``Lean.Order.admissible_apply #[A, mkLambda x .default A T, none, P, a]

/-- Step 5: prove `admissible P` by applying `admissibleRule` layer by layer, and return the goals
left. These are the `hdiv` goals of the triples, and the `admissible` goals of the parts whose
shape no lemma fits. -/
meta partial def proveAdmissible (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  -- Anything else, such as an `hdiv` goal, is left as it is.
  let_expr Lean.Order.admissible α _ P := type | return [goal]
  withLocalDeclD `f α fun f => do
    let body ← Core.betaReduce (P.beta #[f])
    let some goals ← observing? do goal.apply (← admissibleRule α f body) | return [goal]
    goals.flatMapM fun g => do
      -- `admissible_pi` leaves `∀ y, admissible (fun f => P f y)`; name `y` as `body` does (`n`).
      if (← g.getType).isForall then proveAdmissible (← g.intro body.bindingName!).2
      else proveAdmissible g

/--
`fixpoint_induction M` proves the goal by induction on the approximations of `M`, which must be
defined by `partial_fixpoint`. This proves partial correctness.

The goal may be built from `∀`, `→`, `∧` and triples about calls of `M`. The tactic leaves the
goal `step`, for the body of `M` with its recursive calls made to an approximation `M✝` that
satisfies the goal (`ih✝`). For each triple, it also leaves the goal `hdiv` that its `signals`
allow divergence. A part of the goal of another shape is left as the goal `adm` that it is
admissible.

```lean
def countdown (n : Nat) : Option Nat :=
  if n = 0 then pure 0 else countdown (n - 1)
partial_fixpoint

theorem countdown_spec :
    ∀ n, ⦃ True ⦄ countdown n ⦃ fun res => ⌜res = 0⌝ ; fun _ => ⌜True⌝ ⦄ := by
  fixpoint_induction countdown
  all_goals velvet_vcgen with finish
```
-/
elab "fixpoint_induction " id:ident : tactic => withMainContext do
  let fnName ← realizeGlobalConstNoOverloadWithInfo id
  let inductName ←
    try realizeGlobalConstNoOverload (mkIdent (fnName ++ `fixpoint_induct))
    catch _ => throwErrorAt id "fixpoint_induction: `{fnName}` is not defined by `partial_fixpoint`"
  let induct ← mkConstWithFreshMVarLevels inductName
  -- Step 1: `n m acc : Nat ⊢ ⦃ True ⦄ foo n m acc ⦃ … ⦄`.
  let goal ← getMainGoal
  let (xs, goal) ← goal.introNP (← forallTelescope (← goal.getType) fun xs _ => pure xs.size)
  goal.withContext do
  -- `foo.fixpoint_induct` with its binders as metavariables:
  -- `fixed := #[?m]`, `concl := ?motive (fun n => foo n ?m)`, and the motive's argument has
  -- type `α := Nat → Nat → Option Nat`.
  let (args, _, concl) ← forallMetaTelescope (← inferType induct)
  let fixed := args.extract 0 (args.size - 3)
  let α := (← inferType args[args.size - 3]!).bindingDomain!
  -- Step 2: `motive := fun f => ∀ n acc, ⦃ True ⦄ f n acc ⦃ … ⦄`, with `?m := m`.
  let (varying, motive) ← withLocalDeclD `f α fun f => do
    let body ← abstractCalls fnName concl.appArg! (← goal.getType) f
    unless body.containsFVar f.fvarId! do
      throwError "fixpoint_induction: the goal has no call of `{fnName}`"
    -- The binders that are not a fixed parameter: `#[n, acc]`.
    let fixedFVars ← fixed.filterMapM fun m => return (← instantiateMVars m).fvarId?
    let varying := xs.filter (!fixedFVars.contains ·)
    return (varying, ← mkLambdaFVars #[f] (← mkForallFVars (varying.map .fvar) body))
  -- Step 3: `m : Nat ⊢ ∀ n acc, ⦃ True ⦄ foo n m acc ⦃ … ⦄`.
  let (_, goal) ← goal.revert varying (preserveOrder := true)
  -- Step 4: apply `foo.fixpoint_induct m motive`.
  let [adm, step] ← goal.apply (mkAppN induct (fixed.push (← instantiateMVars motive)))
    | throwError "fixpoint_induction: unexpected type of `{inductName}`"
  -- The step is `∀ f, motive f → motive (fun n acc => …)`: beta-reduce the motive, and
  -- introduce the approximation `foo✝` and the induction hypothesis `ih✝`.
  let step ← step.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← step.getType)))
  let names ← [fnName.getString!, "ih"].mapM (mkFreshBinderNameForTactic <| .mkSimple ·)
  let (_, step) ← step.introN 2 names
  step.setTag `step
  -- Step 5.
  let side ← (← proveAdmissible adm).mapM fun g => do
    let g ← g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
    g.setTag (if (← g.getType).isAppOf ``Lean.Order.admissible then `adm else `hdiv)
    return g
  replaceMainGoal (step :: side)

end Velvet.FixpointInduction
