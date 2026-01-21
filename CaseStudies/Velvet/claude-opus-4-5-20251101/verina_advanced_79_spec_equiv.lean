/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4fdf0204-31b5-4286-8465-418e7efc99a5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target

- theorem postcondition_equiv (nums : List Int) (target : Int) (result : Option (Nat × Nat)) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result

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

@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- !benchmark @start postcond
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        -- Lexicographically first: no valid pair (i', j') with i' < i exists
        (nums.take i).zipIdx.all (fun ⟨a, i'⟩ =>
          (nums.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
        -- For this i, j is the smallest valid partner
        ((nums.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- A valid pair is one where i < j, both in bounds, and elements sum to target
def isValidPair (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

-- Lexicographic ordering on pairs: (i1, j1) < (i2, j2) iff i1 < i2, or i1 = i2 and j1 < j2
def lexLt (p1 : Nat × Nat) (p2 : Nat × Nat) : Prop :=
  p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)

-- Postcondition for when result is some (i, j)
def ensuresSome (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  isValidPair nums target i j ∧
  (∀ i' j', isValidPair nums target i' j' → ¬lexLt (i', j') (i, j))

-- Postcondition for when result is none
def ensuresNone (nums : List Int) (target : Int) : Prop :=
  ∀ i j, ¬isValidPair nums target i j

def precondition (nums : List Int) (target : Int) :=
  True

-- no preconditions

def postcondition (nums : List Int) (target : Int) (result : Option (Nat × Nat)) :=
  match result with
  | none => ensuresNone nums target
  | some (i, j) => ensuresSome nums target i j

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (nums : List Int) (target : Int) (result : Option (Nat × Nat)) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result := by
  -- We'll use the fact that if the result is `some (i, j)`, then the conditions for `VerinaSpec.twoSum_postcond` and `LeetProofSpec.postcondition` are equivalent.
  cases' result with i j;
  · -- To prove the equivalence, we show that if there are no valid pairs in the list, then there are no valid pairs in the list.
    apply Iff.intro;
    · intro h_none
      intro i j h_valid
      have h_pairwise : List.Pairwise (· + · ≠ target) nums := by
        exact h_none;
      -- By definition of `isValidPair`, we know that `nums[i]! + nums[j]! = target`.
      obtain ⟨h_lt, h_in_bounds, h_sum⟩ := h_valid;
      have := List.pairwise_iff_get.mp h_pairwise;
      exact this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ h_lt ( by simpa [ List.getElem?_eq_getElem ( by linarith : i < nums.length ), List.getElem?_eq_getElem ( by linarith : j < nums.length ) ] using h_sum );
    · -- If there are no valid pairs in the list, then the pairwise condition holds because there are no elements to compare.
      intros h_no_pairs
      simp [VerinaSpec.twoSum_postcond, h_no_pairs];
      rw [ List.pairwise_iff_get ];
      exact fun i j hij => fun h => h_no_pairs i j |> fun h' => h' ( by exact ⟨ hij, by simp +decide [ Fin.is_lt ], by simpa [ Fin.cast_val_eq_self ] using h ⟩ );
  · -- By definition of `twoSum_postcond`, we know that if `some (i, j)` is returned, then `i < j`, `j < nums.length`, `nums[i]! + nums[j]! = target`, and there are no smaller valid pairs than `(i, j)`.
    unfold VerinaSpec.twoSum_postcond LeetProofSpec.postcondition;
    simp +decide [ LeetProofSpec.ensuresSome, LeetProofSpec.isValidPair ];
    constructor;
    · intro h;
      refine' ⟨ ⟨ h.1, h.2.1, h.2.2.1 ⟩, fun i' j' hij' hj' h_eq h_lex => _ ⟩;
      -- If $i' < i.1$, then the first part of the conjunction in $h$ would apply.
      by_cases h_cases : i' < i.1;
      · have := h.2.2.2.1 ( nums[i']! ) i' ?_ ( nums[j']! ) ?_ <;> simp_all +decide [ List.mem_iff_get ];
        · use ⟨ i', by
            simp +arith +decide [ h_cases ];
            linarith ⟩
          generalize_proofs at *;
          grind;
        · use ⟨ j' - ( i' + 1 ), by
            grind ⟩
          generalize_proofs at *;
          simp +arith +decide [ add_tsub_cancel_of_le ( by linarith : i' + 1 ≤ j' ) ];
      · cases h_lex <;> simp_all +decide [ List.getElem?_eq_none ];
        convert h.2.2.2.2 _ _ _;
        exact nums[j'];
        · rw [ List.mem_iff_get ];
          use ⟨ j' - ( i.1 + 1 ), by
            simp +arith +decide [ *, Nat.sub_sub ];
            omega ⟩
          generalize_proofs at *;
          grind;
        · exact h_eq;
    · rintro ⟨ ⟨ hij, hlt, heq ⟩, h ⟩ ; refine ⟨ hij, hlt, heq, ?_, ?_ ⟩ ; all_goals simp_all +decide [ List.mem_iff_get ] ;
      · -- By definition of `lexLt`, if `a_1 < i.1`, then `(a_1, a_1 + 1 + a_3)` would be less than `(i.1, i.2)`, contradicting `h`.
        intros a a_1 ha a_3 ha_3
        by_contra h_contra
        have h_lex : LeetProofSpec.lexLt (a_1, a_1 + 1 + a_3) (i.1, i.2) := by
          -- Since $a_1 < i.1$, the first element of the pair $(a_1, a_1 + 1 + a_3)$ is less than the first element of $(i.1, i.2)$, which means the pair is less in lexicographic order.
          left; exact (by
          exact lt_of_lt_of_le a_1.2 ( by simp ));
        grind;
      · intro a ha; specialize h i.1 ( i.1 + 1 + a ) ; simp_all +decide [ LeetProofSpec.lexLt ] ;
        grind