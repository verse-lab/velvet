/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6401d7e7-0c75-40d8-8ac7-e3a181efe5d4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int):
  VerinaSpec.MoveZeroesToEnd_precond arr ↔ LeetProofSpec.precondition arr

- theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.MoveZeroesToEnd_precond arr):
  VerinaSpec.MoveZeroesToEnd_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result

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

def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  -- !benchmark @start postcond
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: extract non-zero elements preserving order
def nonZeroElements (arr : Array Int) : List Int :=
  (arr.toList).filter (· ≠ 0)

-- Helper: count zeros in an array
def countZeros (arr : Array Int) : Nat :=
  arr.toList.count 0

-- Helper: check if all elements from index i onwards are zero
def allZerosFrom (arr : Array Int) (i : Nat) : Prop :=
  ∀ j : Nat, i ≤ j → j < arr.size → arr[j]! = 0

-- Helper: check if all elements before index i are non-zero
def allNonZerosBefore (arr : Array Int) (i : Nat) : Prop :=
  ∀ j : Nat, j < i → j < arr.size → arr[j]! ≠ 0

-- Precondition: no restrictions on input
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: characterizes the result
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- Length is preserved
  result.size = arr.size ∧
  -- The count of zeros is preserved
  countZeros result = countZeros arr ∧
  -- Non-zero elements preserve their relative order
  nonZeroElements result = nonZeroElements arr ∧
  -- There exists a boundary index such that:
  -- all elements before it are non-zero and all elements from it onwards are zero
  (∃ k : Nat, k ≤ result.size ∧ allNonZerosBefore result k ∧ allZerosFrom result k)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int):
  VerinaSpec.MoveZeroesToEnd_precond arr ↔ LeetProofSpec.precondition arr := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.MoveZeroesToEnd_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.MoveZeroesToEnd_precond arr):
  VerinaSpec.MoveZeroesToEnd_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  constructor <;> intro h;
  · -- Let's obtain the indices and properties from the hypothesis.
    obtain ⟨h_perm, h_take, h_drop⟩ := h;
    refine' ⟨ _, _, _, _ ⟩;
    · -- Since the lists are permutations of each other, their lengths are equal by definition of permutation.
      apply List.Perm.length_eq; exact (by
      exact?);
    · apply_rules [ List.Perm.count_eq ];
      exact?;
    · unfold LeetProofSpec.nonZeroElements;
      have h_filter_eq : ∀ {l : List ℤ}, List.filter (fun x => x ≠ 0) l = List.filter (fun x => x ≠ 0) (List.take (List.idxOf 0 l) l ++ List.drop (List.idxOf 0 l) l) := by
        aesop;
      rw [ h_filter_eq, List.filter_append, h_take, h_drop ];
      simp +decide [ List.filter_eq, List.filter_cons ];
    · refine' ⟨ List.idxOf 0 result.toList, _, _, _ ⟩;
      · -- The index of the first zero in the result's list is less than or equal to the size of the result because the index is a valid position in the list.
        apply Nat.le_of_lt_succ;
        by_cases h_zero : 0 ∈ result.toList;
        · exact Nat.lt_succ_of_le ( List.idxOf_lt_length_iff.mpr h_zero |> le_of_lt );
        · simp_all +decide [ List.idxOf_eq_length ];
      · intro j hj₁ hj₂;
        -- Since $j < \text{idxOf } 0 \text{ result.toList}$, the element at $j$ in the result list is in the take part, which is the non-zero elements.
        have h_take_part : result[j]! ∈ List.take (List.idxOf 0 result.toList) result.toList := by
          rw [ List.mem_iff_get ];
          use ⟨ j, by
            grind ⟩
          generalize_proofs at *;
          simp +decide [ List.getElem?_take, hj₂ ];
        aesop;
      · intro j hj₁ hj₂;
        -- Since $j \geq \text{idxOf } 0 \text{ result.toList}$, we have $result[j]! \in \text{drop } (\text{idxOf } 0 \text{ result.toList}) \text{ result.toList}$.
        have h_drop_j : result[j]! ∈ List.drop (List.idxOf 0 result.toList) result.toList := by
          rw [ List.mem_iff_get ];
          -- Since $j \geq \text{idxOf } 0 \text{ result.toList}$, we can set $n = j - \text{idxOf } 0 \text{ result.toList}$.
          use ⟨j - List.idxOf 0 result.toList, by
            grind⟩
          generalize_proofs at *;
          grind;
        aesop;
  · -- By definition of `nonZeroElements`, we know that `result.toList.filter (· ≠ 0) = arr.toList.filter (· ≠ 0)`.
    have h_nonzero : result.toList.filter (· ≠ 0) = arr.toList.filter (· ≠ 0) := by
      exact h.2.2.1;
    -- By definition of `allNonZerosBefore` and `allZerosFrom`, we know that `result.toList` can be split into two parts: the non-zero elements before `k` and the zeros from `k` onwards.
    have h_split : result.toList.take h.right.right.right.choose = result.toList.filter (· ≠ 0) ∧ result.toList.drop h.right.right.right.choose = result.toList.filter (· = 0) := by
      have h_split : ∀ (l : List ℤ) (k : Nat), (∀ j, j < k → j < l.length → l.get! j ≠ 0) → (∀ j, k ≤ j → j < l.length → l.get! j = 0) → List.take k l = List.filter (· ≠ 0) l ∧ List.drop k l = List.filter (· = 0) l := by
        intros l k hk_nonzero hk_zero
        induction' l with x l ih generalizing k;
        · simp;
        · -- Consider two cases: $k = 0$ and $k > 0$.
          by_cases hk : k = 0;
          · cases x <;> simp_all +decide;
            · -- Since $k = 0$, the hypothesis $hk_zero$ implies that every element in the list $(a :: l)$ is zero.
              have h_all_zero : ∀ x ∈ (↑‹ℕ› : ℤ) :: l, x = 0 := by
                intro x hx; rw [ List.mem_iff_get ] at hx; aesop;
              rw [ List.filter_eq_self.mpr ] <;> aesop;
            · specialize hk_zero 0 ; simp_all +decide;
          · specialize ih ( k - 1 ) ; rcases k with ( _ | k ) <;> simp_all +decide [ List.get! ] ;
            specialize ih ( fun j hj a => hk_nonzero ( j + 1 ) ( by linarith ) ( by simpa using a ) ) ( fun j hj a => hk_zero ( j + 1 ) ( by linarith ) ( by simpa using a ) ) ; simp_all +decide [ List.filter_cons ] ;
            simpa using hk_nonzero 0 ( Nat.zero_lt_succ _ ) ( Nat.zero_lt_succ _ );
      apply h_split;
      · intro j hj₁ hj₂; have := h.2.2.2.choose_spec.2.1 j hj₁; aesop;
      · intro j hj₁ hj₂; have := h.2.2.2.choose_spec.2.2 j hj₁; aesop;
    -- By combining the results from h_nonzero and h_split, we can conclude that the result.toList is a permutation of arr.toList.
    have h_perm : result.toList = arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0) := by
      rw [ ← h_nonzero, ← List.take_append_drop ( h.right.right.right.choose ) result.toList, h_split.1, h_split.2 ];
      simp +decide [ List.filter_eq, List.filter_eq_nil_iff ];
      convert h.2.1 using 1;
      · -- By definition of `countZeros`, we know that `countZeros result = result.toList.count 0`.
        simp [LeetProofSpec.countZeros];
      · -- By definition of `countZeros`, we know that `countZeros arr` is equal to `arr.toList.count 0`.
        simp [LeetProofSpec.countZeros];
    refine' ⟨ _, _, _ ⟩;
    · rw [ h_perm ];
      -- The concatenation of the filtered lists is a permutation of the original list because the filters are complementary and cover all elements.
      have h_perm : List.Perm (List.filter (fun x => x ≠ 0) arr.toList ++ List.filter (fun x => x = 0) arr.toList) arr.toList := by
        rw [ List.perm_iff_count ];
        intro x; by_cases hx : x = 0 <;> simp +decide [ hx ] ;
        · rw [ List.count_eq_zero ] ; aesop;
        · rw [ List.count_eq_zero ] ; aesop;
      exact?;
    · simp +decide [ h_perm, List.idxOf_append ];
      -- Since the filtered list consists only of zeros, the first element is 0, and thus the index is 0.
      have h_first_zero : List.filter (fun x => x = 0) arr.toList = List.replicate (List.count 0 arr.toList) 0 := by
        exact?;
      rcases n : List.count 0 arr.toList with ( _ | _ | n ) <;> simp +decide [ n, h_first_zero ] at h ⊢;
      simp +decide [ List.replicate ];
    · by_cases h : 0 ∈ arr.toList <;> simp_all +decide [ List.idxOf_append ];
      · have h_idx_zero : ∀ {l : List ℤ}, (∀ x ∈ l, x = 0) → l ≠ [] → List.idxOf 0 l = 0 := by
          intros l hl hl_nonempty; induction l <;> aesop;
        simp_all +decide [ List.filter_eq ];
        rw [ Array.count ] ; aesop;
      · exact fun x hx => fun hx' => h <| hx'.symm ▸ hx