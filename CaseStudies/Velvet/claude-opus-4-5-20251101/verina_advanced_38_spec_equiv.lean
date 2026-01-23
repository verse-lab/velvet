/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3eaa8f52-e6c6-4f2a-839c-1e42cd92839e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- def precondition_equiv (intervals : List (Prod Nat Nat)):
  VerinaSpec.maxCoverageAfterRemovingOne_precond intervals ↔ LeetProofSpec.precondition intervals

- def postcondition_equiv (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : VerinaSpec.maxCoverageAfterRemovingOne_precond (intervals)) :
  VerinaSpec.maxCoverageAfterRemovingOne_postcond intervals result h_precond ↔ LeetProofSpec.postcondition intervals result

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

def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  -- !benchmark @start precond
  intervals.length > 0

-- !benchmark @end precond

def maxCoverageAfterRemovingOne_postcond (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Prop :=
  -- !benchmark @start postcond
  ∃ i < intervals.length,
    let remaining := List.eraseIdx intervals i
    let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
    let merged := sorted.foldl (fun acc curr =>
      match acc with
      | [] => [curr]
      | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
    ) []
    let cov := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
    result = cov ∧
    ∀ j < intervals.length,
      let rem_j := List.eraseIdx intervals j
      let sort_j := List.mergeSort rem_j (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged_j := sort_j.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let cov_j := merged_j.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      cov ≥ cov_j

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Define the set of points covered by a list of intervals
def coveredSet (intervals : List (Nat × Nat)) : Set Nat :=
  {x | ∃ interval ∈ intervals, interval.1 ≤ x ∧ x < interval.2}

-- Remove element at index i from a list
def removeAt (l : List α) (i : Nat) : List α :=
  l.take i ++ l.drop (i + 1)

-- Precondition: at least one interval
def precondition (intervals : List (Nat × Nat)) :=
  intervals.length ≥ 1

-- Postcondition clauses:
-- 1. The result equals the coverage (cardinality of covered set) obtainable by removing some interval
def ensures1 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∃ i : Nat, i < intervals.length ∧ result = Nat.card (coveredSet (removeAt intervals i))

-- 2. The result is at least as large as any coverage after removing any single interval
def ensures2 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∀ i : Nat, i < intervals.length → Nat.card (coveredSet (removeAt intervals i)) ≤ result

def postcondition (intervals : List (Nat × Nat)) (result : Nat) :=
  ensures1 intervals result ∧ ensures2 intervals result

end LeetProofSpec

def precondition_equiv (intervals : List (Prod Nat Nat)):
  VerinaSpec.maxCoverageAfterRemovingOne_precond intervals ↔ LeetProofSpec.precondition intervals := by
  -- The preconditions are equivalent because they both require the list to have at least one element.
  simp [VerinaSpec.maxCoverageAfterRemovingOne_precond, LeetProofSpec.precondition];
  grind

noncomputable section AristotleLemmas

/-
The step function used in the foldl of the merge algorithm. It takes the accumulator (list of merged intervals so far, in reverse order) and the current interval, and merges them if they overlap, or adds the current interval to the accumulator if they don't.
-/
def VerinaSpec.mergeStep (acc : List (Nat × Nat)) (curr : Nat × Nat) : List (Nat × Nat) :=
  match acc with
  | [] => [curr]
  | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc

/-
`VerinaSpec.merge` merges a list of intervals using `mergeStep`.
`VerinaSpec.sumLengths` calculates the sum of lengths of a list of intervals.
-/
def VerinaSpec.merge (intervals : List (Nat × Nat)) : List (Nat × Nat) :=
  intervals.foldl VerinaSpec.mergeStep []

def VerinaSpec.sumLengths (intervals : List (Nat × Nat)) : Nat :=
  intervals.foldl (fun acc (s, e) => acc + (e - s)) 0

/-
`List.eraseIdx` is equivalent to `LeetProofSpec.removeAt`.
-/
lemma VerinaSpec.eraseIdx_eq_removeAt {α} (l : List α) (i : Nat) : l.eraseIdx i = LeetProofSpec.removeAt l i := by
  -- By definition of `List.take` and `List.drop`, we can split the list into the first `i` elements and the rest.
  induction' i with i ih generalizing l;
  · unfold LeetProofSpec.removeAt; aesop;
  · cases l <;> aesop

/-
The set of covered points is invariant under permutation of the input list of intervals. Using `List.Perm` explicitly to avoid notation issues.
-/
lemma VerinaSpec.coveredSet_perm {l1 l2 : List (Nat × Nat)} (h : List.Perm l1 l2) : LeetProofSpec.coveredSet l1 = LeetProofSpec.coveredSet l2 := by
  ext xProofSpec.coveredSet;
  exact ⟨ fun ⟨ interval, h_interval_mem, h_lower, h_upper ⟩ ↦ h.subset h_interval_mem |> fun h_interval_mem' ↦ ⟨ interval, h_interval_mem', h_lower, h_upper ⟩, fun ⟨ interval, h_interval_mem, h_lower, h_upper ⟩ ↦ h.symm.subset h_interval_mem |> fun h_interval_mem' ↦ ⟨ interval, h_interval_mem', h_lower, h_upper ⟩ ⟩

/-
The `mergeStep` function preserves the covered set, provided that the current interval starts after or at the same time as all intervals in the accumulator. This condition holds because the input list is sorted.
If `acc` is empty, it's trivial.
If `acc` is `(s, e) :: rest`, and `curr.1 <= e`:
  We merge to `(s, max e curr.2) :: rest`.
  We need to show `[s, max e curr.2) = [s, e) ∪ [curr.1, curr.2)`.
  We know `s <= curr.1` (from `h_start`) and `curr.1 <= e` (from condition).
  This implies the union equality.
If `curr.1 > e`, we just cons, so it's trivial.
-/
lemma VerinaSpec.coveredSet_mergeStep (acc : List (Nat × Nat)) (curr : Nat × Nat)
  (h_start : ∀ i ∈ acc, i.1 ≤ curr.1) :
  LeetProofSpec.coveredSet (VerinaSpec.mergeStep acc curr) = LeetProofSpec.coveredSet (curr :: acc) := by
  -- By definition of `mergeStep`, we know that the covered set of the merged list is the same as the covered set of the original list.
  by_cases h : curr.1 ≤ (acc.head?.getD (0, 0)).2;
  · rcases acc <;> simp_all +decide [ VerinaSpec.mergeStep ];
    ext x;
    simp +decide [ LeetProofSpec.coveredSet ];
    grind;
  · exact by rw [ show VerinaSpec.mergeStep acc curr = curr :: acc from by unfold VerinaSpec.mergeStep; cases acc <;> aesop ] ;

/-
The covered set of a list with a head and tail is the union of the covered set of the head (as a singleton list) and the covered set of the tail.
-/
lemma VerinaSpec.coveredSet_cons (x : Nat × Nat) (xs : List (Nat × Nat)) :
  LeetProofSpec.coveredSet (x :: xs) = LeetProofSpec.coveredSet [x] ∪ LeetProofSpec.coveredSet xs := by
  unfold LeetProofSpec.coveredSet; ext; aesop;

/-
If all intervals in `acc` start before or at `Y`, and `curr` starts before or at `Y`, then all intervals in `mergeStep acc curr` start before or at `Y`.
-/
lemma VerinaSpec.mergeStep_start_le (acc : List (Nat × Nat)) (curr : Nat × Nat) (Y : Nat)
  (h_acc : ∀ z ∈ acc, z.1 ≤ Y) (h_curr : curr.1 ≤ Y) :
  ∀ x ∈ VerinaSpec.mergeStep acc curr, x.1 ≤ Y := by
  unfold VerinaSpec.mergeStep at * ; aesop

/-
The covered set of the result of folding `mergeStep` over a sorted list `l` with accumulator `acc` is the union of the covered sets of `l` and `acc`, provided that all elements in `acc` start before or at the same time as all elements in `l`.
-/
lemma VerinaSpec.coveredSet_foldl_mergeStep (l : List (Nat × Nat)) (acc : List (Nat × Nat))
  (h_sorted : List.Sorted (fun a b => a.1 ≤ b.1) l)
  (h_le : ∀ x ∈ acc, ∀ y ∈ l, x.1 ≤ y.1) :
  LeetProofSpec.coveredSet (l.foldl VerinaSpec.mergeStep acc) = LeetProofSpec.coveredSet l ∪ LeetProofSpec.coveredSet acc := by
    -- We'll use induction on the list `l`.
    induction' l with y l ih generalizing acc;
    · unfold LeetProofSpec.coveredSet; aesop;
    · convert ih ( VerinaSpec.mergeStep acc y ) _ _ using 1;
      · rw [ VerinaSpec.coveredSet_mergeStep ];
        · simp +decide [ LeetProofSpec.coveredSet, Set.union_comm, Set.union_left_comm, Set.union_assoc ];
          ext; simp +decide [ or_assoc, or_comm, or_left_comm ] ;
        · exact fun x hx => h_le x hx y ( by simp +decide );
      · exact h_sorted.tail;
      · simp_all +decide [ VerinaSpec.mergeStep ];
        rcases acc with ( _ | ⟨ x, acc ⟩ ) <;> simp_all +decide;
        · grind;
        · grind

/-
The covered set of the merged intervals is the same as the covered set of the original sorted intervals.
-/
lemma VerinaSpec.coveredSet_merge (intervals : List (Nat × Nat)) (h_sorted : List.Sorted (fun a b => a.1 ≤ b.1) intervals) :
  LeetProofSpec.coveredSet (VerinaSpec.merge intervals) = LeetProofSpec.coveredSet intervals := by
  convert VerinaSpec.coveredSet_foldl_mergeStep intervals [] h_sorted _ using 1;
  · unfold LeetProofSpec.coveredSet; aesop;
  · aesop

/-
`ReverseSortedDisjoint` implies pairwise disjointness of the intervals.
-/
def VerinaSpec.ReverseSortedDisjoint (l : List (Nat × Nat)) : Prop :=
  List.Pairwise (fun a b => b.2 ≤ a.1) l

lemma VerinaSpec.ReverseSortedDisjoint_cons (x : Nat × Nat) (xs : List (Nat × Nat)) :
  VerinaSpec.ReverseSortedDisjoint (x :: xs) ↔ (∀ y ∈ xs, y.2 ≤ x.1) ∧ VerinaSpec.ReverseSortedDisjoint xs := by
  simp [VerinaSpec.ReverseSortedDisjoint]

lemma VerinaSpec.disjoint_of_ReverseSortedDisjoint (l : List (Nat × Nat))
  (h : VerinaSpec.ReverseSortedDisjoint l) :
  List.Pairwise (fun a b => Disjoint (Set.Ico a.1 a.2) (Set.Ico b.1 b.2)) l := by
  induction' l with a l ih;
  · tauto;
  · unfold VerinaSpec.ReverseSortedDisjoint at h; aesop;

/-
`mergeStep` preserves the `ReverseSortedDisjoint` property, provided that the current interval starts after or at the same time as all intervals in the accumulator.
-/
lemma VerinaSpec.ReverseSortedDisjoint_mergeStep (acc : List (Nat × Nat)) (curr : Nat × Nat)
  (h_acc : VerinaSpec.ReverseSortedDisjoint acc)
  (h_sorted : ∀ x ∈ acc, x.1 ≤ curr.1) :
  VerinaSpec.ReverseSortedDisjoint (VerinaSpec.mergeStep acc curr) := by
  -- We'll use the fact that if the accumulator is empty, then the result is trivially true.
  by_cases h_empty : acc = [];
  · exact h_empty.symm ▸ by unfold VerinaSpec.mergeStep; simp +decide [ VerinaSpec.ReverseSortedDisjoint ] ;
  · rcases acc with ⟨ ⟨ s, e ⟩, acc ⟩ <;> simp_all +decide [ VerinaSpec.mergeStep ];
    split_ifs <;> simp_all +decide [ VerinaSpec.ReverseSortedDisjoint ];
    · tauto;
    · grind

/-
Folding `mergeStep` over a sorted list preserves the `ReverseSortedDisjoint` property of the accumulator, provided the accumulator's elements precede the list's elements.
-/
lemma VerinaSpec.ReverseSortedDisjoint_foldl_mergeStep (l : List (Nat × Nat)) (acc : List (Nat × Nat))
  (h_sorted : List.Sorted (fun a b => a.1 ≤ b.1) l)
  (h_acc : VerinaSpec.ReverseSortedDisjoint acc)
  (h_le : ∀ x ∈ acc, ∀ y ∈ l, x.1 ≤ y.1) :
  VerinaSpec.ReverseSortedDisjoint (l.foldl VerinaSpec.mergeStep acc) := by
  -- By induction on the list `l`.
  induction' l with curr l ih generalizing acc;
  · assumption;
  · apply ih; simp_all +decide [ List.Sorted ] ;
    · exact VerinaSpec.ReverseSortedDisjoint_mergeStep acc curr h_acc fun x hx => h_le x hx _ ( List.mem_cons_self );
    · intros x hx y hy; cases acc <;> simp_all +decide [ VerinaSpec.mergeStep ] ;
      · exact h_sorted.1 _ _ hy;
      · grind +ring

/-
The merged intervals are reverse sorted and disjoint.
-/
lemma VerinaSpec.merge_ReverseSortedDisjoint (intervals : List (Nat × Nat))
  (h_sorted : List.Sorted (fun a b => a.1 ≤ b.1) intervals) :
  VerinaSpec.ReverseSortedDisjoint (VerinaSpec.merge intervals) := by
  -- Apply the lemma that states the merged intervals are reverse sorted and disjoint.
  apply VerinaSpec.ReverseSortedDisjoint_foldl_mergeStep intervals [] h_sorted (by simp [VerinaSpec.ReverseSortedDisjoint]) (by simp [VerinaSpec.ReverseSortedDisjoint])

/-
The covered set of a list of intervals is finite.
-/
lemma VerinaSpec.coveredSet_finite (intervals : List (Nat × Nat)) : Set.Finite (LeetProofSpec.coveredSet intervals) := by
  -- The covered set is defined as the union of all intervals in the list.
  have h_covered_def : LeetProofSpec.coveredSet intervals = ⋃ interval ∈ intervals.toFinset, Set.Ico interval.1 interval.2 := by
    ext; simp [LeetProofSpec.coveredSet];
    exact ⟨ fun ⟨ a, b, h₁, h₂, h₃ ⟩ => ⟨ a, h₂, b, h₁, h₃ ⟩, fun ⟨ a, h₂, b, h₁, h₃ ⟩ => ⟨ a, b, h₁, h₂, h₃ ⟩ ⟩;
  exact h_covered_def ▸ Set.Finite.biUnion ( intervals.toFinset.finite_toSet ) fun x hx => Set.finite_Ico _ _

/-
For a list of pairwise disjoint intervals, the sum of their lengths equals the cardinality of their union (the covered set).
-/
lemma VerinaSpec.sumLengths_eq_card_coveredSet_of_disjoint (intervals : List (Nat × Nat))
  (h_disjoint : List.Pairwise (fun a b => Disjoint (Set.Ico a.1 a.2) (Set.Ico b.1 b.2)) intervals) :
  VerinaSpec.sumLengths intervals = Nat.card (LeetProofSpec.coveredSet intervals) := by
  unfold VerinaSpec.sumLengths;
  induction' intervals using List.reverseRecOn with intervals ih;
  · simp +decide [ LeetProofSpec.coveredSet ];
  · simp_all +decide [ Set.disjoint_iff_inter_eq_empty, Set.Ico_inter_Ico ];
    have h_union : (LeetProofSpec.coveredSet (intervals ++ [ih])).ncard = (LeetProofSpec.coveredSet intervals).ncard + (LeetProofSpec.coveredSet [ih]).ncard := by
      rw [ ← @Set.ncard_union_eq ];
      · congr;
        ext; simp [LeetProofSpec.coveredSet];
        grind;
      · simp_all +decide [ List.pairwise_append, Set.disjoint_left ];
        simp_all +decide [ Set.ext_iff, LeetProofSpec.coveredSet ];
        exact fun a x y hx hy hxy ha => h_disjoint.2 x y hx a hy ha hxy;
      · exact?;
      · exact?;
    rw [ h_union, ‹List.Pairwise ( fun a b => Set.Ico ( Max.max a.1 b.1 ) ( Min.min a.2 b.2 ) = ∅ ) intervals → List.foldl ( fun acc x => acc + ( x.2 - x.1 ) ) 0 intervals = Set.ncard ( LeetProofSpec.coveredSet intervals ) › ( List.pairwise_append.mp h_disjoint |>.1 ) ];
    simp +decide [ LeetProofSpec.coveredSet ];
    erw [ Set.ncard_eq_toFinset_card ( Set.Ico _ _ ) ] ; aesop

/-
`sumLengths` is equivalent to summing the lengths of the intervals using `List.map` and `List.sum`.
-/
lemma VerinaSpec.sumLengths_eq_sum_map (intervals : List (Nat × Nat)) :
  VerinaSpec.sumLengths intervals = (intervals.map (fun x => x.2 - x.1)).sum := by
  unfold VerinaSpec.sumLengths ; simp +arith +decide [ *, List.sum ];
  induction' intervals using List.reverseRecOn with intervals ih <;> simp_all +arith +decide;
  induction ( List.map ( fun x => x.2 - x.1 ) intervals ) <;> simp +arith +decide [ * ]

/-
The sum of lengths of intervals is invariant under reversing the list of intervals.
-/
lemma VerinaSpec.sumLengths_reverse (intervals : List (Nat × Nat)) :
  VerinaSpec.sumLengths intervals.reverse = VerinaSpec.sumLengths intervals := by
  -- By definition of `sumLengths`, we can rewrite it as the sum of the lengths of the intervals.
  have h_sumLengths_eq_sum_map : ∀ (intervals : List (Nat × Nat)), VerinaSpec.sumLengths intervals = (intervals.map (fun x => x.2 - x.1)).sum := by
    exact?;
  rw [ h_sumLengths_eq_sum_map, h_sumLengths_eq_sum_map, List.map_reverse, List.sum_reverse ]

/-
`mergeSort` produces a permutation of the input list.
-/
lemma VerinaSpec.perm_mergeSort (l : List (Nat × Nat)) :
  List.Perm (List.mergeSort l (fun a b => a.1 ≤ b.1)) l := by
  exact?

/-
The result of `mergeSort` is sorted with respect to the start times of the intervals.
-/
lemma VerinaSpec.sorted_mergeSort (l : List (Nat × Nat)) :
  List.Sorted (fun a b => a.1 ≤ b.1) (List.mergeSort l (fun a b => decide (a.1 ≤ b.1))) := by
  convert List.sorted_mergeSort' _ _;
  · exact ⟨ fun a b => le_total a.1 b.1 ⟩;
  · constructor ; intros ; exact le_trans ‹_› ‹_›

/-
For sorted intervals, the sum of lengths of the merged intervals equals the cardinality of the covered set.
-/
lemma VerinaSpec.sumLengths_merge_eq_card_coveredSet (intervals : List (Nat × Nat))
  (h_sorted : List.Sorted (fun a b => a.1 ≤ b.1) intervals) :
  VerinaSpec.sumLengths (VerinaSpec.merge intervals) = Nat.card (LeetProofSpec.coveredSet intervals) := by
  have := @VerinaSpec.sumLengths_eq_card_coveredSet_of_disjoint;
  convert this ( VerinaSpec.merge intervals ) _ using 1;
  · rw [ VerinaSpec.coveredSet_merge intervals h_sorted ];
  · apply VerinaSpec.disjoint_of_ReverseSortedDisjoint;
    exact?

end AristotleLemmas

def postcondition_equiv (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : VerinaSpec.maxCoverageAfterRemovingOne_precond (intervals)) :
  VerinaSpec.maxCoverageAfterRemovingOne_postcond intervals result h_precond ↔ LeetProofSpec.postcondition intervals result := by
  constructor <;> intro h;
  · obtain ⟨ i, hi, hr ⟩ := h;
    -- By definition of `mergeStep`, we know that the sum of the lengths of the merged intervals is equal to the cardinality of the covered set.
    have h_sum_length : ∀ (intervals : List (Nat × Nat)), VerinaSpec.sumLengths (VerinaSpec.merge (List.mergeSort intervals (fun a b => a.1 ≤ b.1))) = Nat.card (LeetProofSpec.coveredSet intervals) := by
      intros intervals
      have h_sorted : List.Sorted (fun a b => a.1 ≤ b.1) (List.mergeSort intervals (fun a b => a.1 ≤ b.1)) := by
        exact?;
      convert VerinaSpec.sumLengths_merge_eq_card_coveredSet ( List.mergeSort intervals ( fun a b => a.1 ≤ b.1 ) ) h_sorted using 1;
      rw [ VerinaSpec.coveredSet_perm ( VerinaSpec.perm_mergeSort intervals ) ];
    have h_sum_length_eq : ∀ (intervals : List (Nat × Nat)), VerinaSpec.sumLengths (VerinaSpec.merge (List.mergeSort intervals (fun a b => a.1 ≤ b.1))).reverse = Nat.card (LeetProofSpec.coveredSet intervals) := by
      exact fun intervals => by rw [ ← h_sum_length intervals, VerinaSpec.sumLengths_reverse ] ;
    constructor;
    · use i;
      convert hr.1 using 1;
      rw [ ← h_sum_length_eq ];
      unfold LeetProofSpec.removeAt; simp +decide [ hi ] ;
      rw [ List.eraseIdx_eq_take_drop_succ ];
      unfold VerinaSpec.sumLengths; simp +decide [ List.foldr_reverse ] ;
      congr! 2;
    · intro j hj;
      convert hr.2 j hj using 1;
      · convert h_sum_length_eq ( intervals.eraseIdx j ) |> Eq.symm using 1;
        rw [ VerinaSpec.eraseIdx_eq_removeAt ];
      · convert hr.1 using 1;
  · rcases h with ⟨ h₁, h₂ ⟩;
    obtain ⟨ i, hi, rfl ⟩ := h₁;
    -- By definition of `VerinaSpec`, we know that the coverage of the remaining intervals is the same as the coverage of the sorted and merged intervals.
    have h_coveredSet_eq : ∀ (l : List (Prod Nat Nat)), Nat.card (LeetProofSpec.coveredSet l) = VerinaSpec.sumLengths (VerinaSpec.merge (List.mergeSort l (fun a b => a.1 ≤ b.1))) := by
      intro l
      have h_coveredSet_eq : Nat.card (LeetProofSpec.coveredSet l) = Nat.card (LeetProofSpec.coveredSet (List.mergeSort l (fun a b => a.1 ≤ b.1))) := by
        have h_coveredSet_eq : List.Perm (List.mergeSort l (fun a b => a.1 ≤ b.1)) l := by
          exact?
        generalize_proofs at *;
        rw [ VerinaSpec.coveredSet_perm h_coveredSet_eq ]
      generalize_proofs at *;
      rw [ h_coveredSet_eq, VerinaSpec.sumLengths_merge_eq_card_coveredSet ];
      exact?;
    refine' ⟨ i, hi, _, _ ⟩;
    · convert h_coveredSet_eq ( intervals.eraseIdx i ) using 1;
      · rw [ VerinaSpec.eraseIdx_eq_removeAt ];
      · convert VerinaSpec.sumLengths_reverse _ using 1;
    · intro j hj;
      convert h₂ j hj using 1;
      · convert h_coveredSet_eq ( LeetProofSpec.removeAt intervals j ) |> Eq.symm using 1;
        convert VerinaSpec.sumLengths_reverse _ using 1;
        congr;
        exact?;
      · convert h_coveredSet_eq ( LeetProofSpec.removeAt intervals i ) |> Eq.symm using 1;
        convert VerinaSpec.sumLengths_reverse _ using 1;
        congr;
        exact?
