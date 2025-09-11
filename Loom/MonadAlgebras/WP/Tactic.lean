import Lean

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.DoNames'

open Lean Parser Meta Elab Term Command Tactic

def findSpec (prog : Expr) : TacticM (Array (Ident × Loom.SpecType)) := do
  let specs ← specAttr.find? prog
  let grts := specs.qsort (compare · · |>.isGT) |>.map
    fun ⟨specType, specName, _⟩ => (mkIdent specName, specType)
  return grts

def Lean.MVarId.isWPGenGoal : MVarId → TacticM Bool
| mvarId => do
  let goalType <- mvarId.getType
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst _ := goalType | return false
  return true

def isWPGenGoal : TacticM Bool := do
  (<- getMainGoal).isWPGenGoal

def hideNonWPGenGoals : TacticM Unit := do
  let goals <- getGoals
  let goals' <- goals.filterM (·.isWPGenGoal)
  setGoals goals'

elab "is_not_wpgen_goal" : tactic => do
  if ← isWPGenGoal then
    throwError "is a WPGen goal"
  else
    return

elab "hide_non_wpgen_goals" : tactic => do
  hideNonWPGenGoals

elab "show_all_goals" : tactic => do
  setGoals (← getUnassignedExprMVars).toList
  synthesizeSyntheticMVarsNoPostponing

macro "try_resolve_spec_goals" : tactic => `(tactic| try is_not_wpgen_goal; solve | rfl | solve_by_elim | simp)

/-- Given `e` as the `Expr` of `∀ (x₁ : t₁) ⋯ (xₙ : tₙ), ⋯`, this returns
    `[(x₁, Expr(t₁), bi₁), ⋯, (xₙ, Expr(tₙ), biₙ)]`, where `biᵢ` is the `BinderInfo` of `xᵢ`. -/
private def getForallPremises : Expr → List (Name × Expr × BinderInfo)
  | .forallE na ty body bi =>
    (na, ty, bi) :: getForallPremises body
  | _ => []

/-- If you imagine `motive` to be a meta-function, then this does the reduction.
    TODO also mention branches and independence -/
private def metaBetaReduceForMotive (metaMotive : Array Expr → Expr)
  (splitterType : Expr) (app : MatcherApp) : MetaM (List (Name × Expr)) := do
  let motivefv := .fvar (← mkFreshFVarId)
  let numDiscr := app.discrs.size
  let branchConds ← do
    let tmp ← instantiateForall splitterType #[motivefv]
    pure <| List.map (fun x => (x.1, x.2.1)) <| List.drop numDiscr <| getForallPremises tmp
  branchConds.mapM fun (nm, br) => do
    let tmp ← Core.transform br
      (pre := fun e => pure <| e.withApp (fun f args =>
        if f == motivefv
        then .done <| metaMotive args
        else .continue))
    pure (nm, tmp)

/-- If you imagine `motive` to be a meta-function, then this does the reduction.
    TODO also mention branches and independence
    TODO say this is a trick and might be removed later -/
private def metaBetaReduceForMotive' (metaMotive : Array Expr → Expr)
  (splitterType : Expr) (app : MatcherApp) : MetaM (List (Name × Expr)) := do
  let motivefv := Expr.fvar (← mkFreshFVarId)
  let numDiscr := app.discrs.size
  let branchConds ← do
    let tmp ← instantiateForall splitterType #[motivefv]
    pure <| List.map (fun x => (x.1, x.2.1)) <| List.drop numDiscr <| getForallPremises tmp
  branchConds.mapM fun (nm, br) => do
    let tmp ← Core.transform br
      (pre := fun e => pure <| e.withApp (fun f args =>
        if f == motivefv
        then .done <| metaMotive args
        else .continue))
    pure (nm, tmp)

-- private def makeEqualityProducingMotive (discrs rhss : Array Expr) (body : Expr) : MetaM Expr := do
--   let eqs ← discrs.mapIdxM fun i lhs => mkEq lhs rhss[i]!
--   mkArrowN eqs body

def WPGen.match_template.{u, v} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l] := Unit.unit

private def List.foldldM.{u, v, w} {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} (f : s → α → m s)
  (g : α → m s) (init : s) (l : List α) : m s :=
  match l with
  | [] => pure init
  | a :: l' => do
    let init' ← g a
    List.foldlM f init' l'

private partial def withinBranch (i n : Nat) (type proof : Expr) : MetaM Expr := do
  if n <= 1 then return proof
  let mv ← mkFreshExprMVar type
  let outerProof left? pf := mkAppOptM (if left? then ``inf_le_of_left_le else ``inf_le_of_right_le)
    #[.some type, .none, (if left? then .none else .some mv), (if left? then .some mv else .none), .none, .some pf]
  if i = n - 1 then return (← outerProof false proof)
  let resProof ← withinBranch i (n - 1) type proof
  outerProof true resProof

private partial def withinBranch' (i n : Nat) (type mainGoal : Expr) : TermElabM Expr := do
  if n <= 1 then return mainGoal
  -- let mv ← mkFreshExprMVar type
  -- let outerProof left? pf := mkAppOptM (if left? then ``inf_le_of_left_le else ``inf_le_of_right_le)
  --   #[.some type, .none, (if left? then .none else .some mv), (if left? then .some mv else .none), .none, .some pf]
  -- let goal ← mkFreshExprMVar none
  if i = n - 1 then
    -- let tmp ← outerProof false goal
    let tmp ← mainGoal.mvarId!.applyConst ``inf_le_of_right_le
    -- let _ ← isDefEq mainGoal tmp
    return .mvar tmp[0]!
  -- let tmp ← outerProof true goal
  -- let _ ← isDefEq mainGoal tmp
  -- withinBranch' i (n - 1) type goal
  let tmp ← mainGoal.mvarId!.applyConst ``inf_le_of_left_le
  -- let _ ← isDefEq mainGoal tmp
  withinBranch' i (n - 1) type <| .mvar tmp[0]!

/-- Construct a suitable `WPGen` term for a matcher in real time. -/
def generateWPForMatcher (matcherName : Name) : TermElabM (Option (Array Name × Expr)) := do
  -- NOTE: we rely on `MatcherInfo` here, since we do not want to generate
  -- `WPGen` only for a specific matcher; but this might not work on `casesOn`.
  -- in that case, we might rely on `MatcherApp` instead
  let some matcherInfo ← getMatcherInfo? matcherName | return none
  let constInfo ← getConstInfo matcherName
  -- use level mvars to be more flexible
  let lvlMVars ← mkFreshLevelMVars constInfo.levelParams.length

  -- make up the discriminant(s) and related (type) parameter(s)
  -- NOTE: this will also introduce a fvar for `motive`, but we do not use it TODO really?
  forallBoundedTelescope (constInfo.type.instantiateLevelParams constInfo.levelParams lvlMVars) (.some matcherInfo.getFirstAltPos) fun paramsAndDiscrs partialMatcher => do
  let discrs := paramsAndDiscrs.drop matcherInfo.getFirstDiscrPos |>.take matcherInfo.numDiscrs

  -- make up the implicit arguments of this `WPGen`
  forallTelescope (← ConstantInfo.type <$> getConstInfo ``WPGen.match_template) fun implicitArgs _ => do
  let (mExpr, monadInstExpr, lExpr, omaInstExpr) := (implicitArgs[0]!, implicitArgs[1]!, implicitArgs[3]!, implicitArgs[5]!)

  -- `α`: make up the return type of `m`
  withLocalDecl (← mkFreshUserName `α) BinderInfo.implicit (← Expr.bindingDomain! <$> inferType mExpr) fun αExpr => do

  -- make up the monadic computations in alternatives
  let wpgenTypeBuilder x : MetaM Expr :=
    -- for convenience, here leave some arguments to be resolved by typeclass resolution
    mkAppOptM ``WPGen #[.some mExpr, .some monadInstExpr, .some αExpr, .some lExpr, .none, .some omaInstExpr, .some x]
  /-
  TODO better abstraction? over `motivefv`, `input`
  let subMonadArgs ← metaBetaReduceForMotive (fun _ => mkApp mExpr αExpr) splitterType app
  -/
  let motivefv := paramsAndDiscrs[matcherInfo.getMotivePos]!
  let branchConds ← do
    pure <| List.map (fun x => (x.1, x.2.1)) <| getForallPremises partialMatcher
  let subMonadArgs ← branchConds.mapM fun (nm, br) => do
    let tmp ← Core.transform br
      (pre := fun e => pure <| e.withApp (fun f args =>
        if f == motivefv
        then .done <| mkApp mExpr αExpr
        else .continue))
    pure (nm, tmp)
  trace[Loom.debug] "subMonadArgs: {subMonadArgs}"
  withLocalDecls (← subMonadArgs.toArray.mapM fun (nm, t) => do
      let nm' ← mkFreshUserName nm
      pure (nm', BinderInfo.implicit, fun _ => pure t)) fun subMonadArgsFVars => do

  -- make up the sub `WPGen` goals
  let subWPGenArgs ← subMonadArgs.mapIdxM fun i (nm, t) => do
    let nm' := nm.appendBefore "wpg"
    let ty ← forallTelescope t fun xs _ => do
      let tmp := mkAppN subMonadArgsFVars[i]! xs
      let tmp ← wpgenTypeBuilder tmp
      mkForallFVars xs tmp
    pure (nm', ty)
  trace[Loom.debug] "subWPGenArgs: {subWPGenArgs}"
  -- TODO repeating code
  withLocalDecls (← subWPGenArgs.toArray.mapM fun (nm, t) => do
      let nm' ← mkFreshUserName nm
      pure (nm', BinderInfo.implicit, fun _ => pure t)) fun subWPGenArgsFVars => do

  -- make up the type of the target `WPGen`
  let targetMatcher ← do
    let motivefv := paramsAndDiscrs[matcherInfo.getMotivePos]!
    let ty ← inferType motivefv
    let motiveArg ← forallTelescope ty fun xs _ =>
      mkLambdaFVars xs <| mkApp mExpr αExpr
    pure <| mkAppN
      (Lean.mkConst matcherName lvlMVars)
      ((paramsAndDiscrs.set! matcherInfo.getMotivePos motiveArg) ++ subMonadArgsFVars)
  let targetWPGenTy ← wpgenTypeBuilder targetMatcher
  trace[Loom.debug] "targetWPGenTy: {targetWPGenTy}"

  -- prepare the splitter
  let (splitter, splitterType) ← do
    let matchEqns ← Match.getEquationsFor matcherName
    -- note the difference on instantiating level params
    let splitter ← mkConstWithFreshMVarLevels matchEqns.splitterName
    let splitterType ← whnfForall (← inferType <| Lean.mkConst matchEqns.splitterName lvlMVars)
    pure (splitter, splitterType)
  trace[Loom.debug] "splitter type: {splitterType}"

  -- make up the `post`
  withLocalDeclD (← mkFreshUserName `post) (← mkArrow αExpr lExpr) fun postExpr => do

  -- make up the `WPGen.get`
  -- CHECK `backup` might include unnecessary information
  let (wpgenGet, backup) ← do
    -- let fakeMotiveFv := Expr.fvar (← mkFreshFVarId)
    -- the `motive` is fake here
    let partialSplitterType ← instantiateForall splitterType paramsAndDiscrs -- (paramsAndDiscrs.set! matcherInfo.getMotivePos fakeMotiveFv)
    let branchConds ← do
      pure <| List.map (fun x => x.2.1) <| getForallPremises partialSplitterType
    let wpgenGetBranches ← branchConds.mapIdxM fun i br => do
      let subWPGen := subWPGenArgsFVars[i]!
      let br' ← forallTelescope br fun xs motiveBody => do
        -- TODO for `Unit → ...`, this will not work; fix it later
        let newBody ← do
          let numArgsRequired ← Expr.getNumHeadForalls <$> inferType subWPGen
          let subWPGenGet ← mkAppM ``WPGen.get #[mkAppN subWPGen (xs.take numArgsRequired), postExpr]
          motiveBody.withApp fun _ args => do
            -- TODO this should have an optimization; some equalities might be redundant
            let eqs ← discrs.mapIdxM fun i lhs => mkEq lhs args[i]!
            mkArrowN eqs subWPGenGet
        mkForallFVars xs newBody
      trace[Loom.debug] "branch {i} after adding equalities: {br} ==> {br'}"
      let res ← forallTelescope br' fun xs motiveBody' => do
        xs.foldrM (init := motiveBody') fun x e => do
          let xty ← inferType x
          if ← isProp xty then
            let injectedProp ← mkAppOptM ``LE.pure #[.some lExpr, .none, .none, .none, .some xty]
            mkAppOptM ``himp #[.some lExpr, .none, .some injectedProp, .some e]
          else
            let tmp ← mkLambdaFVars #[x] e
            mkAppOptM ``iInf #[.some lExpr, .some xty, .none, .some tmp]
      trace[Loom.debug] "branch {i} after transformation: {br'} ==> {res}"
      pure (br', res)
    let (wpgenGetBranchesBefore, wpgenGetBranchesAfter) := wpgenGetBranches.unzip
    -- combine the branches together; `⊓` is left-associative
    -- NOTE: this might also be changed into another encoding, e.g., `⨅ i ∈ (Fin ..), ...`
    let topAsInit ← mkAppOptM ``Top.top #[.some lExpr, .none]
    let bundled ← wpgenGetBranchesAfter.foldldM (g := pure) (init := topAsInit) fun infs e =>
      mkAppOptM ``Min.min #[.some lExpr, .none, .some infs, .some e]
    let res ← mkLambdaFVars #[postExpr] bundled
    pure (res, wpgenGetBranchesBefore.toArray)
  trace[Loom.debug] "wpgenGet: {wpgenGet}"

  -- make up the proof for `WPGen.post`
  -- NOTE: this proof might also be done using tactics
  let wpgenPost ← do
    let motive ← do
      let lhs ← instantiateLambda wpgenGet #[postExpr]
      let rhs ← mkAppOptM ``wp
        #[.some mExpr, .some monadInstExpr, .some αExpr, .some lExpr, .none,
          .some omaInstExpr, .some targetMatcher, .some postExpr]
      let le ← mkAppM ``LE.le #[lhs, rhs]
      mkLambdaFVars discrs le
    trace[Loom.debug] "motive for the splitter in proof: {motive}"
    let paramsAndDiscrs' := paramsAndDiscrs.set! matcherInfo.getMotivePos motive
    let partialSplitter := mkAppN splitter paramsAndDiscrs'
    let partialSplitterType ← inferType partialSplitter
    let numBranches := matcherInfo.numAlts    -- should be the same as `branchConds.length`
    let branchConds ← do
      pure <| List.map (fun x => x.2.1) <| List.take numBranches <| getForallPremises partialSplitterType
    let wpgenPostSubProofs ← branchConds.toArray.mapIdxM fun i br => do
      trace[Loom.debug] "subgoal {i}: {br}"
      -- `intro`
      let res ← forallTelescope br fun xs body => do
        -- instantiate the sub `WPGen` to use
        let subWPGen := subWPGenArgsFVars[i]!
        -- TODO maybe store this information ahead of recomputing since it is used twice
        let numArgsRequired ← Expr.getNumHeadForalls <$> inferType subWPGen
        let subWPGenProp ← mkAppM ``WPGen.prop #[mkAppN subWPGen (xs.take numArgsRequired), postExpr]
        -- build the proof by looking at the corresponding branch of `wpgenGet`

        let goal ← mkFreshExprMVar body

        let goal_ ← withinBranch' i numBranches lExpr goal

        -- do the prefix part
        let goal' ← xs.foldlM (init := goal_) fun mainGoal x => do
          let xty ← inferType x
          trace[Loom.debug] "xty: {xty}"
          if ← isProp xty then
            -- let goal' ← mkFreshExprMVar none
            -- let tmp ← mkAppOptM ``usefulThing #[.some lExpr, .none, .none, .none, .none, .some x, .some goal']
            -- let _ ← isDefEq mainGoal tmp
            -- pure goal'
            let tmp ← mkAppOptM ``usefulThing #[.some lExpr, .none, .some xty, .some x]
            let goals ← mainGoal.mvarId!.apply tmp
            pure <| .mvar goals[0]!
          else
            -- need to provide the function?
            -- let ety ← inferType e
            -- trace[Loom.debug] "ety: {ety}"
            -- let tmp ← match_expr ety with
            --   | LE.le _ _ lhs _ =>
            --     -- let nm ← x.fvarId!.getUserName
            --     -- pure <| some <| Expr.lam nm xty lhs BinderInfo.default
            --     mkLambdaFVars #[x] lhs
            --   | _ => pure none

            -- let goal' ← mkFreshExprMVar none
            -- let tmp ← mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none, .none /- ! -/ , .none, .some x, .some goal']
            -- let _ ← isDefEq mainGoal tmp
            -- pure goal'
            let f ← mkFreshExprMVar (← mkArrow xty lExpr)
            let a ← mkFreshExprMVar lExpr
            let tmp ← mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none, .some f /- ! -/ , .some a, .some x]
            let goals ← mainGoal.mvarId!.apply tmp
            pure <| .mvar goals[0]!

        -- try `rfl` in the trailing part
        let n := backup[i]!.getNumHeadForalls
        let goal'' ← (n - xs.size) |>.foldM (init := goal') fun _ _ mainGoal => do
          -- let mv ← mkFreshExprMVar .none
          -- let rfl ← mkEqRefl mv
          -- let goal' ← mkFreshExprMVar none
          -- let tmp ← mkAppOptM ``usefulThing #[.some lExpr, .none, .none, .none, .none, .some rfl, .some goal']
          -- let _ ← isDefEq mainGoal tmp
          -- pure goal'
          let goals ← mainGoal.mvarId!.applyConst ``usefulThingRfl
          pure <| .mvar goals[0]!
        let _ ← isDefEq subWPGenProp goal''

/-
        -- try `rfl` in the trailing part
        let n := backup[i]!.getNumHeadForalls
        let rflProof ← (n - xs.size) |>.foldM (init := subWPGenProp) fun _ _ e => do
          let mv ← mkFreshExprMVar .none
          let rfl ← mkEqRefl mv
          mkAppOptM ``usefulThing #[.some lExpr, .none, .none, .none, .none, .some rfl, .some e]
        trace[Loom.debug] "rflProof: {rflProof}"
        -- do the prefix part
        let proof ← xs.foldrM (init := rflProof) fun x e => do
          let xty ← inferType x
          trace[Loom.debug] "xty: {xty}"
          if ← isProp xty then
            mkAppOptM ``usefulThing #[.some lExpr, .none, .none, .none, .none, .some x, .some e]
          else
            -- need to provide the function?
            let ety ← inferType e
            trace[Loom.debug] "ety: {ety}"
            let tmp ← match_expr ety with
              | LE.le _ _ lhs _ =>
                -- let nm ← x.fvarId!.getUserName
                -- pure <| some <| Expr.lam nm xty lhs BinderInfo.default
                mkLambdaFVars #[x] lhs
              | _ => pure none
            mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none, tmp, .none, .some x, .some e]
        -- do the branch selection
        let res ← withinBranch i numBranches lExpr proof
-/
        let res ← instantiateMVars goal
        mkLambdaFVars xs res
      trace[Loom.debug] "sub-proof for branch {i}: {br} ==> {res}"
      pure res
    mkLambdaFVars #[postExpr] <| mkAppN partialSplitter wpgenPostSubProofs

  -- put together
  let wpgen ← mkAppM ``WPGen.mk #[wpgenGet, wpgenPost]
  check wpgen
  let wpgen ← instantiateMVars wpgen
  let arguments :=
    #[αExpr] ++
    (paramsAndDiscrs.take matcherInfo.numParams) ++
    implicitArgs ++
    subMonadArgsFVars ++
    subWPGenArgsFVars ++
    (paramsAndDiscrs.drop matcherInfo.getFirstDiscrPos)
  let wpgen ← mkLambdaFVars arguments wpgen
  trace[Loom.debug] "generated WPGen: {wpgen}"
  trace[Loom.debug] "has mvar? {wpgen.hasMVar}"

  -- NOTE: it seems that only this requires `TermElabM`; the rest can be done in `MetaM`
  let wpgen ← levelMVarToParam wpgen
  trace[Loom.debug] "has mvar? {wpgen.hasMVar}"
  let newLvls := collectLevelParams {} wpgen |>.params
  -- Option.some <$>
  pure (newLvls, wpgen)

def generateWPStep : TacticM (Bool × Expr) := withMainContext do
  let goalType <- getMainTarget
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst x := goalType | throwError "{goalType} is not a WPGen"
  if let some name := x.getAppFn.constName? then
    if ← isMatcher name then
      let targetName := name ++ `WPGen
      if (← getEnv).find? targetName matches none then
        let some (newLvls, wpgen) ← generateWPForMatcher name | throwError s!"cannot generate WPGen for matcher {name}"
        addDecl <|
          Declaration.defnDecl <|
            mkDefinitionValEx targetName newLvls.toList (← inferType wpgen) wpgen
            (Lean.ReducibilityHints.regular 0)
            (DefinitionSafety.safe) []
        enableRealizationsForConst targetName
        applyAttributes targetName (← do
          let tmp ← `(Parser.Term.attrInstance| spec)
          elabAttrs #[tmp])
    -- if let some res ← generateWPForMatcher name then
    --   withMainContext do
    --     let goal ← getMainGoal
    --     let goals ← goal.apply res
    --     replaceMainGoal goals
    --   return (true, x)
  let cs <- findSpec x
  for elem in cs do
    try
      match elem with
      | (spec, .wpgen) =>
        evalTactic $ <- `(tactic| apply $spec)
      | (spec, .triple) =>
        let info ← getConstInfo spec.getId
        let num_args := info.type.getNumHeadForalls
        let refine_part ←
          Array.foldlM
            (fun x li => `(term|$x $li))
            (←`(term| $spec))
            (Array.replicate num_args (←`(term|?_)))
        let refine_tac ← `(tactic|refine $refine_part)
        evalTactic $ <- `(tactic|
          eapply $(mkIdent ``WPGen.spec_triple);
          $refine_tac)
      return (true, x)
    catch _ => continue
  let some ⟨rsx, _⟩ := x.getAppFn.const? | return (false, x)
  let rsxCorrect := (rsx.toString ++ "_correct").toName
  let some mainName ← getDeclName? | throwError s!"no lemma name found for goal:{goalType}"
  if mainName ≠ rsxCorrect then
    return (false, x)
  let mainNameIdent := mkIdent mainName
  try
    evalTactic $ <- `(tactic|
        eapply $(mkIdent ``WPGen.spec_triple);
        apply $mainNameIdent)
    return (true, x)
  catch _ =>
    return (false, x)


elab "wpgen_app" : tactic => do
  let (found, x) ← generateWPStep
  unless found do throwError "no spec found for {x}"

macro "wpgen_step" : tactic => `(tactic| first
  | (wpgen_app <;> intros <;> try_resolve_spec_goals)
  --| (intros; split <;> intros)
  )
macro "wpgen_intro" : tactic => `(tactic| (apply WPGen.intro; rotate_right))
macro "wpgen" : tactic => `(tactic| (
  wpgen_intro
  repeat' wpgen_step
  ))
def Lean.Expr.getName (e : Expr) : MetaM Name := do
  match_expr e with
  | Name.mkStr _ n =>
    match n with
    | .lit (.strVal n) => return n.toName
    | _                => throwError "expected a string literal1"
  | _ => throwError "expected a string literal3"


partial def Lean.Expr.getNamesProp (tp : Expr) : MetaM (Option (List Name)) := do
  match_expr tp with
  | WithName _ n₁ => return some [<- n₁.getName]
  | MProdWithNames _ tr n₁ =>
    let n₁ <- n₁.getName
    let some ns <- tr.getNamesProp
      | return none
    return some $ n₁ :: ns
  | _ =>
    let .some typeWithNameExpr := tp.find? (fun e => e.isAppOf ``typeWithName)
      | return none
    let nname := typeWithNameExpr.getAppArgs[2]!
    return some [<- nname.getName]

def renameOld (n : Name) : TacticM Unit := withMainContext do
  (<- getMainGoal).modifyLCtx fun hyps => Id.run do
    let mut hypsNew := hyps
    for hyp in hyps.decls.toArray.reverse do
      if hyp.isSome then
        let n' := hyp.get!.userName
        if n' == n then
          hypsNew := hyps.renameUserName n' (n'.toString ++ "Old" |>.toName)
    return hypsNew

elab "loom_split" : tactic => do
  let goalType <- getMainTarget
  match_expr goalType with
  | WithName _ _ => throwError "Cannot split on a WithName goal"
  | _ => evalTactic $ <- `(tactic| apply And.intro)


elab "loom_intro" : tactic => withMainContext do
  let goalType <- getMainTarget
  let .forallE _ tp _ _ := goalType.consumeMData
    | evalTactic $ <- `(tactic| fail)
  let some ns <- tp.getNamesProp
    | evalTactic $ <- `(tactic| try unhygienic intro) -- because sometimes it is part of an invariant and unnamed by defualt
  let ns1 ← ns.mapM getUnusedUserName
  let names := ns1 |>.map Lean.mkIdent |>.toArray
  for name in names do renameOld name.getId
  if names.size > 1 then
    evalTactic $ <- `(tactic|
      rintro ⟨$[$names],*⟩; try simp only [MProdWithNames.snd, MProdWithNames.fst])
  else
    if names.size = 0 then
      pure () --just more robust
    else
      let name₀ := names[0]!
      evalTactic $ <- `(tactic| intro $(name₀):ident)

macro "mwp" : tactic => `(tactic| (
  wpgen
  try simp only [loomLogicSimp, loomWpSimp, invariants, List.foldr, WithName.mk', WithName.erase, typeWithName.erase]
  try unfold spec WithName at *
  try unfold spec typeWithName at *
  ))

attribute [loomSpec high, loomWpSimp] WPGen.if
attribute [loomSpec, loomWpSimp] WPGen.bind WPGen.pure WPGen.assert WPGen.forWithInvariant WPGen.map
attribute [loomWpSimp] spec WPGen.spec_triple

@[loomLogicSimp]
lemma leE (l : Type u) [PartialOrder l] (a b : α -> l) : a ≤ b ↔ ∀ x, a x ≤ b x := by
  rfl
@[loomLogicSimp]
lemma lePropE (a b : Prop) : (a ≤ b) = (a → b) := by
  rfl

@[loomLogicSimp]
lemma pureE (l : Type u) [CompleteLattice l] (a : Prop) : (⌜a⌝ : α -> l) = fun _ => ⌜a⌝ := by
  simp [LE.pure]; split <;> rfl

@[loomLogicSimp]
lemma purePropE  : (⌜a⌝ : Prop) = a := by
  simp [LE.pure]

@[loomLogicSimp]
lemma infPropE (a b : Prop) : (a ⊓ b) = (a ∧ b) := by
  rfl

@[loomLogicSimp]
lemma infE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊓ b) = fun x => a x ⊓ b x := by
  rfl

@[loomLogicSimp]
lemma supE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊔ b) = fun x => a x ⊔ b x := by
  rfl

@[loomLogicSimp]
lemma supPropE (a b : Prop) : (a ⊔ b) = (a ∨ b) := by
  rfl

@[loomLogicSimp]
lemma iInfE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨅ i, a i) = fun x => ⨅ i, a i x := by
  ext; simp

@[loomLogicSimp]
lemma iSupE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨆ i, a i) = fun x => ⨆ i, a i x := by
  ext; simp

@[loomLogicSimp]
lemma himpE  (l : Type u) [CompleteBooleanAlgebra l] (a b : α -> l) :
  (a ⇨ b) = fun x => a x ⇨ b x := by rfl

@[loomLogicSimp]
lemma himpPureE (a b : Prop) :
  (a ⇨ b) = (a -> b) := by rfl

@[loomLogicSimp]
lemma topE (l : Type u) [CompleteLattice l] : (⊤ : α -> l) = fun _ => ⊤ := by rfl

@[loomLogicSimp]
lemma topPureE : (⊤ : Prop) = True := by rfl

attribute [loomLogicSimp]
  forall_const
  implies_true and_true true_and
  iInf_Prop_eq
  and_imp
attribute [simp←] Nat.mul_add_one

attribute [loomWpSplit] iInf_inf_eq himp_inf_distrib wp_and wp_iInf
