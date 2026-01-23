/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cb897525-45fc-493c-9c22-e8bfef31f6e4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : Array Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target

- theorem postcondition_equiv (nums : Array Int) (target : Int) (result : (Nat × Nat)) (h_precond : VerinaSpec.twoSum_precond nums target):
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

def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList

-- !benchmark @end precond

def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  -- !benchmark @start postcond
  let (i, j) := result
  -- Basic validity: i < j, in bounds, and sum equals target
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  -- Lexicographically first: no valid pair (i', j') with i' < i exists
  (nums.toList.take i).zipIdx.all (fun ⟨a, i'⟩ =>
    (nums.toList.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
  -- For our i, j is the smallest valid partner
  ((nums.toList.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a pair (i, j) is a valid pair summing to target
def isValidPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- Helper: Check if pair (i1, j1) is lexicographically smaller than or equal to (i2, j2)
def lexLE (i1 : Nat) (j1 : Nat) (i2 : Nat) (j2 : Nat) : Prop :=
  i1 < i2 ∨ (i1 = i2 ∧ j1 ≤ j2)

-- Helper: There exists at least one valid pair
def existsValidPair (nums : Array Int) (target : Int) : Prop :=
  ∃ i j, isValidPair nums target i j

-- Precondition: array has at least 2 elements and a valid pair exists
def precondition (nums : Array Int) (target : Int) :=
  nums.size ≥ 2 ∧ existsValidPair nums target

-- Postcondition: result is a valid pair and is lexicographically smallest
def postcondition (nums : Array Int) (target : Int) (result : Nat × Nat) :=
  let (i, j) := result
  -- The result is a valid pair
  isValidPair nums target i j ∧
  -- The result is lexicographically smallest among all valid pairs
  (∀ i' j', isValidPair nums target i' j' → lexLE i j i' j')

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : Array Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target := by
  constructor <;> intro H;
  · rcases H with ⟨ h₁, h₂ ⟩;
    refine' ⟨ h₁, _ ⟩;
    -- Since `h₂` states that the list of `nums` is not pairwise distinct with respect to the sum `target`, there must exist two elements in the list that sum to `target`.
    obtain ⟨i, j, hij, hsum⟩ : ∃ i j, i < j ∧ i < nums.size ∧ j < nums.size ∧ nums[i]! + nums[j]! = target := by
      rw [ List.pairwise_iff_get ] at h₂;
      aesop;
    exact ⟨ i, j, ⟨ hij, hsum.2.1, hsum.2.2 ⟩ ⟩;
  · rcases H with ⟨ H₁, ⟨ i, j, H₂ ⟩ ⟩;
    refine' ⟨ H₁, _ ⟩;
    unfold LeetProofSpec.isValidPair at H₂;
    rw [ List.pairwise_iff_get ];
    norm_num +zetaDelta at *;
    use ⟨ i, by
      simpa using by linarith ⟩, ⟨ j, by
      simpa using H₂.2.1 ⟩
    generalize_proofs at *;
    aesop

theorem postcondition_equiv (nums : Array Int) (target : Int) (result : (Nat × Nat)) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result := by
  -- To prove the equivalence, we need to show that the conditions in the postconditions are equivalent.
  apply Iff.intro;
  · -- If the VerinaSpec.postcondition holds, then the LeetProofSpec.postcondition must also hold because the lexicographic condition in LeetProofSpec is exactly what's being checked in the VerinaSpec's postcondition.
    intros h_postcond
    apply And.intro;
    · exact ⟨ h_postcond.1, h_postcond.2.1, h_postcond.2.2.1 ⟩;
    · intro i' j' h_pair
      obtain ⟨h_valid, h_lex⟩ := h_postcond;
      by_cases h_cases : i' < result.1;
      · have h_contra : ∀ (i : ℕ), i < result.1 → ∀ (j : ℕ), j > i → j < nums.size → nums[i]! + nums[j]! = target → False := by
          intros i hi j hj₁ hj₂ hj₃; have := h_lex.2.2.1; simp_all +decide [ List.zipIdx, List.take ] ;
          specialize this ( nums[i]! ) i ; simp_all +decide [ List.mem_iff_get ] ;
          contrapose! this; simp_all +decide [ Fin.exists_iff ] ;
          exact ⟨ by linarith, j - ( i + 1 ), by omega, by simpa [ add_assoc, Nat.add_sub_of_le ( by linarith : i + 1 ≤ j ) ] using hj₃ ⟩;
        exact False.elim <| h_contra i' h_cases j' h_pair.1 h_pair.2.1 h_pair.2.2;
      · -- Since $i' \geq result.1$ and $i' \neq result.1$, we have $i' > result.1$.
        by_cases h_eq : i' = result.1;
        · simp_all +decide [ LeetProofSpec.isValidPair ];
          refine Or.inr ⟨ rfl, ?_ ⟩;
          contrapose! h_lex;
          intro h₁ h₂ h₃; use nums[j']!; simp_all +decide [ List.mem_iff_get ] ;
          refine' ⟨ ⟨ ⟨ j' - result.1 - 1, _ ⟩, _ ⟩, _ ⟩ <;> norm_num [ Nat.sub_sub ] at * <;> try omega;
          · grind;
          · grind;
        · exact Or.inl ( lt_of_le_of_ne ( le_of_not_gt h_cases ) ( Ne.symm h_eq ) );
  · intro h;
    rcases h with ⟨ ⟨ h₁, h₂, h₃ ⟩, h₄ ⟩;
    unfold VerinaSpec.twoSum_postcond;
    simp_all +decide [ LeetProofSpec.isValidPair, LeetProofSpec.lexLE ];
    constructor <;> intros <;> contrapose! h₄;
    · rw [ List.mem_iff_get ] at *;
      simp +zetaDelta at *;
      rename_i k hk₁ hk₂ hk₃;
      obtain ⟨ n, hn₁, rfl ⟩ := hk₂;
      obtain ⟨ m, hm₁, hm₂ ⟩ := hk₃;
      refine' ⟨ n, n + 1 + m, _, _, _, _ ⟩;
      · linarith;
      · grind;
      · exact Nat.le_of_lt ( Nat.lt_of_lt_of_le n.2 ( by simp ) );
      · intro h; have := Fin.is_lt n; have := Fin.is_lt m; simp_all +decide [ List.length_take, List.length_drop ] ;
    · rename_i x hx;
      obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hx;
      use result.1, result.1 + 1 + k.val;
      grind