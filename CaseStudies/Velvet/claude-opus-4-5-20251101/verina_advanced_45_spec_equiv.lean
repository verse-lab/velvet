/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cd25d122-5f51-4170-b81b-1c4751ad821a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int):
  VerinaSpec.maxSubarraySum_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Int) (h_precond : VerinaSpec.maxSubarraySum_precond xs):
  VerinaSpec.maxSubarraySum_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result

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

def maxSubarraySum_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def maxSubarraySum_postcond (xs : List Int) (result: Int) (h_precond : maxSubarraySum_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  -- Find all possible subarrays and their sums
  let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start =>
    List.range' 1 (xs.length - start) |>.map (fun len =>
      ((xs.drop start).take len).sum
    ))

  -- Check if there exists a subarray with sum equal to result
  let has_result_subarray := subarray_sums.any (fun sum => sum == result)


  -- Check if result is the maximum among all subarray sums
  let is_maximum := subarray_sums.all (· ≤ result)

  match xs with
  | [] => result == 0
  | _ => has_result_subarray ∧ is_maximum

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to compute sum of a sublist from index i to j (inclusive)
def subarraySum (xs : List Int) (i : Nat) (j : Nat) : Int :=
  (xs.drop i).take (j - i + 1) |>.foldl (· + ·) 0

-- Check if (i, j) is a valid subarray range
def isValidSubarrayRange (xs : List Int) (i : Nat) (j : Nat) : Prop :=
  i ≤ j ∧ j < xs.length

-- The result is achievable: there exists a subarray with this sum
def isAchievableSum (xs : List Int) (sum : Int) : Prop :=
  xs = [] ∧ sum = 0 ∨
  xs ≠ [] ∧ ∃ i j, isValidSubarrayRange xs i j ∧ subarraySum xs i j = sum

-- The result is maximal: no subarray has a larger sum
def isMaximalSum (xs : List Int) (sum : Int) : Prop :=
  ∀ i j, isValidSubarrayRange xs i j → subarraySum xs i j ≤ sum

def precondition (xs : List Int) :=
  True

-- no preconditions needed

def postcondition (xs : List Int) (result : Int) :=
  isAchievableSum xs result ∧ isMaximalSum xs result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int):
  VerinaSpec.maxSubarraySum_precond xs ↔ LeetProofSpec.precondition xs := by
  exact?

theorem postcondition_equiv (xs : List Int) (result : Int) (h_precond : VerinaSpec.maxSubarraySum_precond xs):
  VerinaSpec.maxSubarraySum_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  -- If the LeetProofSpec condition holds, then either `xs` is empty and `result` is zero, or `xs` is non-empty and there exists a subarray with sum `result`.
  cases' xs with x xs' <;> simp_all +decide [ LeetProofSpec.postcondition, LeetProofSpec.isAchievableSum, LeetProofSpec.isMaximalSum ];
  · unfold VerinaSpec.maxSubarraySum_postcond LeetProofSpec.isValidSubarrayRange LeetProofSpec.subarraySum; aesop;
  · -- By definition of `maxSubarraySum_postcond`, we know that if `xs` is non-empty, then `result` is the maximum subarray sum if and only if there exists a subarray with sum `result` and all other subarray sums are less than or equal to `result`.
    simp [VerinaSpec.maxSubarraySum_postcond] at *;
    -- By definition of `isValidSubarrayRange` and `subarraySum`, we can rewrite the postconditions to match each other.
    apply Iff.intro;
    · -- By definition of `LeetProofSpec.subarraySum`, we know that `subarraySum (x :: xs') i j` is equal to `List.sum (List.take (j - i + 1) (List.drop i (x :: xs')))`.
      have h_subarraySum_eq : ∀ i j, LeetProofSpec.isValidSubarrayRange (x :: xs') i j → LeetProofSpec.subarraySum (x :: xs') i j = List.sum (List.take (j - i + 1) (List.drop i (x :: xs'))) := by
        -- By definition of `List.foldl`, we can rewrite the left-hand side as the sum of the list.
        have h_foldl_sum : ∀ (l : List ℤ), List.foldl (· + ·) 0 l = List.sum l := by
          exact?;
        exact?;
      simp_all +decide [ LeetProofSpec.isValidSubarrayRange ];
      exact fun i hi j hj₁ hj₂ hj₃ hj₄ => ⟨ ⟨ i, i + j - 1, ⟨ by omega, by omega ⟩, by rw [ h_subarraySum_eq i ( i + j - 1 ) ( by omega ) ( by omega ) ] ; cases j <;> aesop ⟩, fun i j hij hj => by have := hj₄ i ( by omega ) ( j - i + 1 ) ( by omega ) ( by omega ) ; aesop ⟩;
    · intro h
      obtain ⟨⟨i, j, h_range, h_sum⟩, h_max⟩ := h
      use by
        use i, by
          -- Since $j < \text{length}(x :: xs')$ and $i \leq j$, we have $i < \text{length}(x :: xs')$.
          have h_i_lt_length : i < List.length (x :: xs') := by
            exact lt_of_le_of_lt h_range.1 ( Nat.lt_of_succ_le h_range.2 )
          generalize_proofs at *;
          exact h_i_lt_length.trans_le (by simp), j - i + 1, by
          -- Since $i \leq j$ and $j < 1 + xs'.length$, we have $1 \leq j - i + 1$ and $j - i + 1 < 1 + (xs'.length + 1 - i)$.
          have h_bounds : 1 ≤ j - i + 1 ∧ j - i + 1 < 1 + (xs'.length + 1 - i) := by
            have h1 : 1 ≤ j - i + 1 := by
              exact Nat.succ_pos _
            have h2 : j - i + 1 < 1 + (xs'.length + 1 - i) := by
              -- Since $j < xs'.length + 1$, we have $j - i + 1 < xs'.length + 1 - i + 1$.
              have h_j_lt : j < xs'.length + 1 := by
                exact h_range.2.trans_le ( by simp +arith +decide )
              have h_j_minus_i_lt : j - i < xs'.length + 1 - i := by
                exact tsub_lt_tsub_iff_right ( h_range.left ) |>.2 h_j_lt
              linarith [Nat.sub_add_cancel (show i ≤ j from h_range.left)]
            exact ⟨h1, h2⟩
          generalize_proofs at *;
          exact h_bounds
        generalize_proofs at *;
        convert h_sum using 1;
        -- By definition of `subarraySum`, we have `subarraySum (x :: xs') i j = (List.drop i (x :: xs')).take (j - i + 1) |>.foldl (· + ·) 0`.
        simp [LeetProofSpec.subarraySum];
        rw [ List.sum_eq_foldl ]
      generalize_proofs at *;
      intro i hi j hj₁ hj₂; specialize h_max i ( i + j - 1 ) ; simp_all +decide [ LeetProofSpec.isValidSubarrayRange, LeetProofSpec.subarraySum ] ;
      convert h_max ( Nat.le_sub_one_of_lt ( by omega ) ) ( by omega ) using 1 ; simp +decide [ add_assoc, add_tsub_assoc_of_le hj₁ ];
      rw [ Nat.sub_add_cancel hj₁, List.sum_eq_foldl ]