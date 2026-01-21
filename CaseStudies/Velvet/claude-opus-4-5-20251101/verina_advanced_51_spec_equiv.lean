/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8735526f-b16a-4cd9-9c32-fae6b6ea76cf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : List Int) (b : List Int):
  VerinaSpec.mergeSorted_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : List Int) (b : List Int) (result : List Int) (h_precond : VerinaSpec.mergeSorted_precond a b):
  VerinaSpec.mergeSorted_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result

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

def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b

-- !benchmark @end precond

def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged

def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) (h_precond : mergeSorted_precond (a) (b)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to check if a list of integers is sorted in non-decreasing order
def isSortedInt (lst : List Int) : Prop :=
  ∀ i : Nat, i + 1 < lst.length → lst[i]! ≤ lst[i + 1]!

-- Precondition: both input lists must be sorted in non-decreasing order
def precondition (a : List Int) (b : List Int) : Prop :=
  isSortedInt a ∧ isSortedInt b

-- Postcondition clause 1: result is sorted in non-decreasing order
def ensures1 (a : List Int) (b : List Int) (result : List Int) : Prop :=
  isSortedInt result

-- Postcondition clause 2: result is a permutation of the concatenation of a and b
-- This ensures all elements from both lists are in the result with correct multiplicity
def ensures2 (a : List Int) (b : List Int) (result : List Int) : Prop :=
  result.Perm (a ++ b)

-- Combined postcondition
def postcondition (a : List Int) (b : List Int) (result : List Int) : Prop :=
  ensures1 a b result ∧ ensures2 a b result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : List Int) (b : List Int):
  VerinaSpec.mergeSorted_precond a b ↔ LeetProofSpec.precondition a b := by
  -- The pairwise condition in VerinaSpec is equivalent to the sorted condition in LeetProofSpec.
  have h_pairwise_sorted : ∀ (l : List ℤ), List.Pairwise (· ≤ ·) l ↔ LeetProofSpec.isSortedInt l := by
    -- To prove the equivalence, we can use the fact that the pairwise condition is equivalent to the sorted condition.
    intros l
    constructor;
    · intro h i hi;
      have := List.pairwise_iff_get.mp h;
      convert this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self i ) using 1;
      · grind;
      · grind;
    · intro h_sorted
      have h_pairwise : ∀ (i j : ℕ), i < j → i < l.length → j < l.length → l[i]! ≤ l[j]! := by
        -- By induction on $j - i$, we can show that $l[i]! \leq l[j]!$ for any $i < j$.
        intro i j hij hi hj
        induction' hij with k hk ih
        generalize_proofs at *; (
        exact h_sorted i ( by linarith ));
        exact le_trans ( ih ( Nat.lt_of_succ_lt hj ) ) ( h_sorted _ ( by simpa using by linarith ) )
      generalize_proofs at *;
      rw [ List.pairwise_iff_get ] ; aesop;
  unfold VerinaSpec.mergeSorted_precond LeetProofSpec.precondition; aesop;

theorem postcondition_equiv (a : List Int) (b : List Int) (result : List Int) (h_precond : VerinaSpec.mergeSorted_precond a b):
  VerinaSpec.mergeSorted_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- The key is that pairwise ≤ is equivalent to being sorted in non-decreasing order.
  have h_pairwise_le_eq_sorted : ∀ (l : List ℤ), List.Pairwise (· ≤ ·) l ↔ LeetProofSpec.isSortedInt l := by
    intro l;
    constructor <;> intro hl;
    · intro i hi;
      have := List.pairwise_iff_get.mp hl;
      simpa [ List.getElem?_eq_getElem ( by linarith : i < l.length ), List.getElem?_eq_getElem ( by linarith : i + 1 < l.length ) ] using this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self _ );
    · -- By definition of pairwise sorted, we need to show that for all i < length l - 1, l[i]! ≤ l[i + 1]!.
      have h_pairwise : ∀ i j : ℕ, i < j → j < l.length → l[i]! ≤ l[j]! := by
        -- We can prove this by induction on $j - i$.
        intro i j hij hjl
        induction' hij with j hj ih;
        · exact hl i ( by simpa using hjl );
        · exact le_trans ( ih ( Nat.lt_of_succ_lt hjl ) ) ( hl _ ( by simpa using hjl ) );
      rw [ List.pairwise_iff_get ];
      exact fun i j hij => by simpa using h_pairwise i j hij ( by simp ) ;
  -- Apply the equivalence of pairwise ≤ and isSortedInt to each part of the conjunction.
  simp [VerinaSpec.mergeSorted_postcond, LeetProofSpec.postcondition, h_pairwise_le_eq_sorted];
  simp +decide [ LeetProofSpec.ensures1, LeetProofSpec.ensures2 ];
  simp +decide [ List.isPerm_iff ]