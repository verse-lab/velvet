/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 64ea9f6e-bd40-4fc0-80d7-32de956fe5c6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.FindSingleNumber_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.FindSingleNumber_precond nums):
  VerinaSpec.FindSingleNumber_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Lean
import Mathlib.Tactic


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

namespace VerinaSpec

def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums

@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1

-- !benchmark @end precond

@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Predicate: the list has valid structure (one element once, all others twice)
def hasValidSingleNumberProperty (nums : List Int) : Prop :=
  nums.length > 0 ∧
  (∃! x, x ∈ nums ∧ nums.count x = 1) ∧
  (∀ x, x ∈ nums → nums.count x = 1 ∨ nums.count x = 2)

-- Predicate: result is the unique element appearing exactly once
def isSingleNumber (nums : List Int) (result : Int) : Prop :=
  result ∈ nums ∧ nums.count result = 1

-- Precondition: list must have valid single number property
def precondition (nums : List Int) :=
  hasValidSingleNumberProperty nums

-- Postcondition: result is the element appearing exactly once
def postcondition (nums : List Int) (result : Int) :=
  isSingleNumber nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.FindSingleNumber_precond nums ↔ LeetProofSpec.precondition nums := by
  constructor <;> intro h;
  · -- From `h`, we know that `nums.length > 0`.
    unfold VerinaSpec.FindSingleNumber_precond at h
    unfold LeetProofSpec.precondition at *;
    simp_all +decide [ List.count ];
    -- From the hypothesis h, we know that there's exactly one element in nums with a count of 1.
    obtain ⟨x, hx_unique⟩ : ∃! x, x ∈ nums ∧ List.countP (fun y => y == x) nums = 1 := by
      rw [ List.countP_eq_length_filter ] at h;
      obtain ⟨ x, hx ⟩ := List.length_eq_one_iff.mp h.2;
      replace hx := congr_arg List.toFinset hx; rw [ Finset.ext_iff ] at hx; aesop;
    use by
      exact List.length_pos_iff.mpr ( by aesop_cat )
    use by
      exact ⟨ x, by simpa using hx_unique.1, fun y hy => hx_unique.2 y <| by simpa using hy ⟩
    generalize_proofs at *;
    aesop;
  · obtain ⟨h_length, ⟨x, hx⟩, h_count⟩ := h;
    -- Since there's exactly one element x with count 1, and all others are 2, the count of 1 in the mapped list is 1.
    have h_count_one : (nums.map (fun x => nums.count x)).count 1 = 1 := by
      have h_count_one : List.count 1 (List.map (fun x => List.count x nums) nums) = List.count x nums := by
        rw [ List.count ];
        rw [ List.countP_map ];
        rw [ List.countP_congr ];
        exact?;
        grind;
      aesop;
    constructor <;> aesop

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.FindSingleNumber_precond nums):
  VerinaSpec.FindSingleNumber_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- By definition of `filterlist.aux`, the length of `filterlist result nums` is equal to the count of `result` in `nums`.
  have h_filterlist_count : ∀ (lst : List Int) (x : Int), (VerinaSpec.filterlist.aux x lst).length = lst.count x := by
    -- We can prove this by induction on the list `lst`.
    intro lst x
    induction' lst with y ys ih;
    · rfl;
    · by_cases h : y = x <;> simp_all +decide [ VerinaSpec.filterlist.aux ];
  constructor <;> intro h;
  · -- By definition of `Filterlist`, the count of `result` in `nums` is equal to the length of the list obtained by filtering `nums` with `result`.
    have h_filterlist_count : (nums.count result) = (VerinaSpec.filterlist.aux result nums).length := by
      rw [ h_filterlist_count ];
    -- By combining h_filterlist_count and h, we can conclude that the count of result in nums is 1.
    have h_count : (nums.count result) = 1 := by
      exact h_filterlist_count.trans h.2.1;
    exact ⟨ by contrapose! h_count; simp_all +decide [ List.count_eq_zero_of_not_mem ], h_count ⟩;
  · -- By definition of `LeetProofSpec.postcondition`, we know that `result ∈ nums` and `nums.count result = 1`.
    obtain ⟨h_result_in_nums, h_count⟩ := h;
    -- Since `result ∈ nums` and `nums.count result = 1`, we can conclude that the filterlist's length is 1.
    have h_filterlist_length : (VerinaSpec.filterlist result nums).length = 1 := by
      exact h_filterlist_count _ _ ▸ h_count;
    -- For any x in nums, if x is not the result, then by the preconditions, x must appear twice. Therefore, the filterlist of x will have length 2.
    have h_filterlist_length_x : ∀ x ∈ nums, x ≠ result → (VerinaSpec.filterlist x nums).length = 2 := by
      intros x hx hx_ne_result
      have h_count_x : nums.count x = 2 := by
        -- Since x is in nums and x is not the result, by the preconditions, x must appear twice. Therefore, the count of x in nums is 2.
        have h_count_x : nums.count x = 1 ∨ nums.count x = 2 := by
          exact h_precond.1 |> fun h => by simpa using List.all_eq_true.mp h |> fun h => by aesop;
        cases h_count_x <;> simp_all +decide [ List.count_eq_of_nodup ];
        have h_unique : ∃! x, x ∈ nums ∧ nums.count x = 1 := by
          have h_precond_equiv : VerinaSpec.FindSingleNumber_precond nums ↔ LeetProofSpec.precondition nums := by
            exact?
          exact h_precond_equiv.mp h_precond |>.2.1;
        exact hx_ne_result <| h_unique.unique ⟨ hx, by assumption ⟩ ⟨ h_result_in_nums, h_count ⟩;
      exact h_filterlist_count nums x ▸ h_count_x;
    exact ⟨ List.length_pos_of_mem h_result_in_nums, h_filterlist_length, fun x hx => Classical.or_iff_not_imp_left.2 fun hx' => h_filterlist_length_x x hx ( by aesop ) ⟩