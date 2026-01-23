/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3421e95e-e382-4260-809c-a79b47ec13e0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array (Array Int)) (key : Int):
  VerinaSpec.SlopeSearch_precond a key ↔ LeetProofSpec.precondition a key

- theorem postcondition_equiv (a : Array (Array Int)) (key : Int) (result : (Int × Int)) (h_precond : VerinaSpec.SlopeSearch_precond a key):
  VerinaSpec.SlopeSearch_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result

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

@[reducible, simp]
def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!

def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧
  (a[0]!).size > 0 ∧  -- non-empty inner arrays
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (List.range (a[0]!.size)).all (fun i =>
    List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
  )

-- !benchmark @end precond

def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) (h_precond : SlopeSearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to access 2D array element
def get2d (a : Array (Array Int)) (row : Nat) (col : Nat) : Int :=
  let rowArr := a[row]!
  rowArr[col]!

-- Helper: check if all rows have the same length
def allRowsSameLength (a : Array (Array Int)) : Prop :=
  ∀ i : Nat, i < a.size → a[i]!.size = a[0]!.size

-- Helper: check if all rows are non-empty
def allRowsNonEmpty (a : Array (Array Int)) : Prop :=
  a[0]!.size > 0

-- Helper: check if a single row is sorted in non-decreasing order
def rowSorted (row : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < row.size → row[i]! ≤ row[j]!

-- Helper: check if all rows are sorted
def allRowsSorted (a : Array (Array Int)) : Prop :=
  ∀ i : Nat, i < a.size → rowSorted a[i]!

-- Helper: check if columns are sorted in non-decreasing order
def columnsSorted (a : Array (Array Int)) : Prop :=
  ∀ col : Nat, col < a[0]!.size →
    ∀ i j : Nat, i < j → j < a.size → get2d a i col ≤ get2d a j col

-- Helper: check if key exists in the array
def keyExists (a : Array (Array Int)) (key : Int) : Prop :=
  ∃ row col : Nat, row < a.size ∧ col < a[0]!.size ∧ get2d a row col = key

-- Precondition: valid sorted 2D array
def precondition (a : Array (Array Int)) (key : Int) : Prop :=
  a.size > 0 ∧
  allRowsNonEmpty a ∧
  allRowsSameLength a ∧
  allRowsSorted a ∧
  columnsSorted a

-- Postcondition: result is valid position of key or (-1, -1) if not found
def postcondition (a : Array (Array Int)) (key : Int) (result : Int × Int) : Prop :=
  let (row, col) := result
  (row ≥ 0 ∧ col ≥ 0 →
    row.toNat < a.size ∧
    col.toNat < a[0]!.size ∧
    get2d a row.toNat col.toNat = key) ∧
  (row = -1 ∧ col = -1 →
    ¬keyExists a key) ∧
  ((row ≥ 0 ∧ col ≥ 0) ∨ (row = -1 ∧ col = -1))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array (Array Int)) (key : Int):
  VerinaSpec.SlopeSearch_precond a key ↔ LeetProofSpec.precondition a key := by
  constructor <;> intro h;
  · rcases h with ⟨ h1, h2, h3, h4, h5 ⟩;
    refine' ⟨ h1, h2, _, _, _ ⟩;
    · intro i hi;
      induction' i with i ih;
      · field_simp;
      · have := List.pairwise_iff_get.mp h3;
        specialize this ⟨ 0, by simpa using h1 ⟩ ⟨ i + 1, by simpa using hi ⟩ ; aesop;
    · intro i hi
      have h_row_sorted : List.Pairwise (· ≤ ·) (a[i]!.toList) := by
        rw [ Array.all_eq_true ] at h4 ; aesop;
      intro j k hjk hk;
      have := List.pairwise_iff_get.mp h_row_sorted;
      convert this ⟨ j, by simpa using by linarith ⟩ ⟨ k, by simpa using by linarith ⟩ hjk;
      · grind;
      · grind;
    · intro col hcol i j hij hj; have := h5; simp_all +decide [ List.all_eq_true ] ;
      have := List.pairwise_iff_get.mp ( h5 col hcol );
      convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij using 1;
      · simp +decide [ LeetProofSpec.get2d ];
        grind;
      · unfold LeetProofSpec.get2d; aesop;
  · rcases h with ⟨h1, h2, h3, h4, h5⟩;
    refine' ⟨ h1, h2, _, _, _ ⟩;
    · have h_pairwise : ∀ i j : Nat, i < j → i < a.size → j < a.size → (a[i]!).size = (a[j]!).size := by
        intros i j hij hi hj; have := h3 i hi; have := h3 j hj; aesop;
      rw [ List.pairwise_iff_get ];
      aesop;
    · simp_all +decide [ Array.all_eq ];
      intro i hi; specialize h4 i hi;
      rw [ List.pairwise_iff_get ];
      intro i j hij; specialize h4 i j; aesop;
    · -- By definition of `columnsSorted`, each column is sorted in non-decreasing order.
      have h_col_sorted : ∀ col : ℕ, col < a[0]!.size → List.Pairwise (· ≤ ·) (List.map (fun row => row[col]!) (Array.toList a)) := by
        intro col hcol
        have h_col_sorted : ∀ i j : ℕ, i < j → j < a.size → (a.toList.get! i)[col]! ≤ (a.toList.get! j)[col]! := by
          intro i j hij hj; convert h5 col hcol i j hij hj using 1;
          · simp +decide [ LeetProofSpec.get2d ];
            cases a ; aesop;
          · unfold LeetProofSpec.get2d; aesop;
        rw [ List.pairwise_iff_get ];
        exact fun i j hij => by simpa [ Array.getElem?_eq_getElem ( show i.val < a.size from by simpa using i.2 ), Array.getElem?_eq_getElem ( show j.val < a.size from by simpa using j.2 ) ] using h_col_sorted i j hij ( by simpa using j.2 ) ;
      aesop

theorem postcondition_equiv (a : Array (Array Int)) (key : Int) (result : (Int × Int)) (h_precond : VerinaSpec.SlopeSearch_precond a key):
  VerinaSpec.SlopeSearch_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  unfold VerinaSpec.SlopeSearch_postcond LeetProofSpec.postcondition;
  constructor <;> intro h;
  · rcases h with ( h | h ) <;> simp_all +decide;
    · unfold LeetProofSpec.get2d; aesop;
    · simp_all +decide [ LeetProofSpec.keyExists ];
      intro i hi j hj; specialize h; have := h.2.2 i hi j; simp_all +decide [ LeetProofSpec.get2d ] ;
      have := h_precond.2.2.1;
      rw [ List.pairwise_iff_get ] at this;
      -- Since all rows have the same size, we can conclude that the size of the i-th row is equal to the size of the 0-th row.
      have h_row_size : ∀ i : Fin a.size, (a.toList.get i).size = (a.toList.get ⟨0, by
        grind⟩).size := by
        grind
      generalize_proofs at *;
      convert h_row_size ⟨ i, hi ⟩;
      grind;
  · rcases x : result.1 with ( _ | m ) <;> rcases y : result.2 with ( _ | n ) <;> simp_all +decide;
    · unfold LeetProofSpec.get2d at h; aesop;
    · -- Since `Int.negSucc m = -1` and `Int.negSucc n = -1`, we have `m = 0` and `n = 0`.
      have hm : m = 0 := by
        grind
      have hn : n = 0 := by
        grind;
      -- Since the negation of the key existing in the array implies that for any row and column, the element at that position is not equal to the key, we can conclude the proof.
      intros i hi j hj
      by_contra h_contra;
      exact h.1 ( by simp +decide [ hm ] ) ( by simp +decide [ hn ] ) ⟨ i, j, hi, by
        have h_row_size : ∀ i : Nat, i < a.size → a[i]!.size = a[0]!.size := by
          intro i hi
          have h_row_size : List.Pairwise (·.size = ·.size) a.toList := by
            exact h_precond.2.2.1
          have h_row_size : ∀ i : Nat, i < a.size → a[i]!.size = a[0]!.size := by
            intro i hi
            have h_row_size : ∀ j : Nat, j < a.size → a[j]!.size = a[0]!.size := by
              intro j hj;
              induction' j with j ih;
              · rfl;
              · have := List.pairwise_iff_get.mp h_row_size;
                specialize this ⟨ j, by simpa using by linarith ⟩ ⟨ j + 1, by simpa using by linarith ⟩ ; aesop
            exact h_row_size i hi;
          exact h_row_size i hi;
        grind, by
        unfold LeetProofSpec.get2d; aesop; ⟩