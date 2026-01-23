/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1ea58088-73d2-4d8f-b357-4936e1fdeafe

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.findFirstRepeatedChar_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Option Char) (h_precond : VerinaSpec.findFirstRepeatedChar_precond s):
  VerinaSpec.findFirstRepeatedChar_postcond s result h_precond ↔ LeetProofSpec.postcondition s result

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Lean
import Mathlib.Tactic
import Std.Data.HashSet


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

def findFirstRepeatedChar_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    -- Exists repeated char
    cs.count c ≥ 2 ∧
    -- There is no other repeated char before the found one
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    -- There is no repeated char
    List.Pairwise (· ≠ ·) cs

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if character c appears in the list before position i
def appearsBeforePos (chars : List Char) (c : Char) (i : Nat) : Prop :=
  ∃ j : Nat, j < i ∧ j < chars.length ∧ chars[j]! = c

-- Helper: Position i is where we first see a repeated character
-- (chars[i] appeared somewhere before position i, and no earlier position has this property)
def isFirstRepeatPos (chars : List Char) (i : Nat) : Prop :=
  i < chars.length ∧
  appearsBeforePos chars chars[i]! i ∧
  ∀ k : Nat, k < i → ¬appearsBeforePos chars chars[k]! k

-- Helper: Check if any character in the string is repeated
def hasRepeatedChar (chars : List Char) : Prop :=
  ∃ i : Nat, i < chars.length ∧ appearsBeforePos chars chars[i]! i

-- Postcondition clause 1: If result is some c, then c is a repeated character found at the first repeat position
def ensures1 (s : String) (result : Option Char) :=
  ∀ c : Char, result = some c →
    ∃ i : Nat, isFirstRepeatPos s.toList i ∧ s.toList[i]! = c

-- Postcondition clause 2: If result is none, then no character repeats in the string
def ensures2 (s : String) (result : Option Char) :=
  result = none → ¬hasRepeatedChar s.toList

-- Postcondition clause 3: If there is a repeated character, result must be some
def ensures3 (s : String) (result : Option Char) :=
  hasRepeatedChar s.toList → result.isSome

def precondition (s : String) :=
  True

-- no preconditions

def postcondition (s : String) (result : Option Char) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.findFirstRepeatedChar_precond s ↔ LeetProofSpec.precondition s := by
  -- Both preconditions are defined as True, so the equivalence is immediate.
  simp [VerinaSpec.findFirstRepeatedChar_precond, LeetProofSpec.precondition]

noncomputable section AristotleLemmas

/-
`hasRepeatedChar` is equivalent to the list not being `Nodup` (having no duplicates).
-/
theorem LeetProofSpec.hasRepeatedChar_iff_not_nodup (l : List Char) :
  LeetProofSpec.hasRepeatedChar l ↔ ¬ l.Nodup := by
    rw [ List.nodup_iff_injective_get ];
    constructor;
    · rintro ⟨ i, hi, j, hj, hij ⟩ h; have := @h ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ ; aesop;
    · norm_num [ Function.Injective ] at *;
      intro x y hxy hne;
      cases lt_or_gt_of_ne ( by simpa [ Fin.ext_iff ] using hne : ( x : ℕ ) ≠ y ) <;> [ exact ⟨ y, by aesop, x, by aesop ⟩ ; exact ⟨ x, by aesop, y, by aesop ⟩ ]

/-
`appearsBeforePos l c i` is equivalent to `c` being a member of `l.take i`.
-/
theorem LeetProofSpec.appearsBeforePos_iff_mem_take (l : List Char) (c : Char) (i : Nat) :
  LeetProofSpec.appearsBeforePos l c i ↔ c ∈ l.take i := by
    constructor;
    · rintro ⟨ j, hj₁, hj₂, hj₃ ⟩;
      rw [ List.mem_iff_get ];
      refine' ⟨ ⟨ j, _ ⟩, _ ⟩ <;> aesop;
    · intro h;
      obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp h;
      use j.val;
      grind

/-
A list has no duplicates if and only if for every index `k`, the element at `k` is not present in the prefix of the list of length `k`.
-/
theorem List.nodup_iff_forall_get_not_mem_take {α} [DecidableEq α] [Inhabited α] (l : List α) :
  l.Nodup ↔ ∀ k : Nat, k < l.length → l[k]! ∉ l.take k := by
    constructor;
    · intro hl k hk h; have := List.nodup_iff_injective_get.mp hl;
      rw [ List.mem_iff_get ] at h;
      obtain ⟨ n, hn ⟩ := h;
      simp_all +decide [ Fin.ext_iff, List.get ];
      exact absurd ( this hn ) ( ne_of_lt ( Nat.lt_of_lt_of_le n.2 ( by simp ) ) );
    · intro h;
      rw [ List.nodup_iff_getElem?_ne_getElem? ];
      intro i j hij hjl
      by_contra h_eq;
      specialize h j hjl ; simp_all +decide [ List.take, List.getElem?_eq_getElem ];
      rw [ List.mem_iff_getElem? ] at h;
      exact h ⟨ i, by rw [ List.getElem?_take ] ; aesop ⟩

/-
`l.take i` has no duplicates if and only if for all `k < i`, the character at `k` does not appear before `k` in `l`.
Assumes `i <= l.length`.
Uses `List.nodup_iff_forall_get_not_mem_take` and `LeetProofSpec.appearsBeforePos_iff_mem_take`.
-/
theorem LeetProofSpec.nodup_take_iff (l : List Char) (i : Nat) (hi : i ≤ l.length) :
  List.Nodup (l.take i) ↔ ∀ k, k < i → ¬ LeetProofSpec.appearsBeforePos l l[k]! k := by
    -- Apply the `List.nodup_iff_forall_get_not_mem_take` to `l.take i`.
    rw [List.nodup_iff_forall_get_not_mem_take];
    simp +decide [ List.take_take, LeetProofSpec.appearsBeforePos_iff_mem_take ];
    grind

/-
`isFirstRepeatPos l i` is equivalent to: `i` is a valid index, the character at `i` appears in the prefix `l.take i`, and the prefix `l.take i` has no duplicates.
Uses `LeetProofSpec.appearsBeforePos_iff_mem_take` and `LeetProofSpec.nodup_take_iff`.
-/
theorem LeetProofSpec.isFirstRepeatPos_iff (l : List Char) (i : Nat) :
  LeetProofSpec.isFirstRepeatPos l i ↔
  i < l.length ∧ l[i]! ∈ l.take i ∧ List.Nodup (l.take i) := by
  unfold LeetProofSpec.isFirstRepeatPos
  constructor
  · rintro ⟨h_len, h_appears, h_forall⟩
    refine ⟨h_len, ?_, ?_⟩
    · rwa [LeetProofSpec.appearsBeforePos_iff_mem_take] at h_appears
    · rw [LeetProofSpec.nodup_take_iff l i (le_of_lt h_len)]
      exact h_forall
  · rintro ⟨h_len, h_mem, h_nodup⟩
    refine ⟨h_len, ?_, ?_⟩
    · rwa [LeetProofSpec.appearsBeforePos_iff_mem_take]
    · rw [←LeetProofSpec.nodup_take_iff l i (le_of_lt h_len)]
      exact h_nodup

/-
Properties of the `secondIdx` calculated in VerinaSpec:
If `c` appears at least twice, then `secondIdx` is a valid index, points to `c`, is not the first index of `c`, `c` appears before it, and any occurrence of `c` before `secondIdx` must be the first index.
-/
theorem LeetProofSpec.secondIdx_spec (cs : List Char) (c : Char) (h_count : cs.count c ≥ 2) :
  let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
  secondIdx < cs.length ∧
  cs[secondIdx]! = c ∧
  secondIdx ≠ cs.idxOf c ∧
  c ∈ cs.take secondIdx ∧
  ∀ k < secondIdx, cs[k]! = c → k = cs.idxOf c := by
    have h_secondIdx_def : ∃ secondIdx, secondIdx < cs.length ∧ cs[secondIdx]! = c ∧ secondIdx ≠ cs.idxOf c ∧ ∀ k < secondIdx, cs[k]! = c → k = cs.idxOf c := by
      have h_exists : ∃ secondIdx, secondIdx < cs.length ∧ cs[secondIdx]! = c ∧ secondIdx ≠ cs.idxOf c := by
        contrapose! h_count;
        have h_count_eq : List.count c cs = Finset.card (Finset.filter (fun x => cs[x]! = c) (Finset.range cs.length)) := by
          have h_count_eq : List.count c cs = Finset.sum (Finset.range cs.length) (fun i => if cs[i]! = c then 1 else 0) := by
            have h_count_eq : ∀ (l : List Char), List.count c l = Finset.sum (Finset.range l.length) (fun i => if l[i]! = c then 1 else 0) := by
              intro l; induction l <;> simp_all +decide [ Finset.sum_range_succ' ] ;
              rw [ Finset.card_filter ];
              rw [ Finset.sum_range_succ' ] ; aesop;
            apply h_count_eq;
          rw [ h_count_eq, Finset.card_filter ];
        exact h_count_eq.symm ▸ lt_of_le_of_lt ( Finset.card_le_one.mpr ( by intros x hx y hy; linarith [ h_count x ( Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ) ( Finset.mem_filter.mp hx |>.2 ), h_count y ( Finset.mem_range.mp ( Finset.mem_filter.mp hy |>.1 ) ) ( Finset.mem_filter.mp hy |>.2 ) ] ) ) ( by norm_num )
      exact ⟨ Nat.find h_exists, Nat.find_spec h_exists |>.1, Nat.find_spec h_exists |>.2.1, Nat.find_spec h_exists |>.2.2, fun k hk₁ hk₂ => Classical.not_not.1 fun hk₃ => Nat.find_min h_exists hk₁ ⟨ by linarith [ Nat.find_spec h_exists |>.1 ], by simp [ hk₂ ], by simp [ hk₃ ] ⟩ ⟩;
    -- By definition of findIdx, it finds the smallest index where the predicate holds.
    obtain ⟨secondIdx, h_secondIdx⟩ := h_secondIdx_def;
    have h_findIdx : List.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c) (cs.zipIdx) = secondIdx := by
      have h_findIdx : ∀ {l : List (Char × ℕ)} {p : Char × ℕ → Bool} {i : ℕ}, (∀ k < i, ¬(p (l.get! k))) → p (l.get! i) → List.findIdx p l = i := by
        intros l p i hi hp; induction' l with hd tl hl generalizing i <;> simp_all +decide [ List.findIdx_cons ] ;
        · linarith [ hi 0 ];
        · rcases i with ( _ | i ) <;> simp_all +decide [ List.getElem?_cons ];
          specialize hl ( fun k hk => ?_ ) hp;
          · grind;
          · specialize hi 0 ; aesop;
      apply h_findIdx;
      · simp +zetaDelta at *;
        grind;
      · simp_all +decide [ List.get! ];
        grind;
    simp_all +decide [ List.idxOf ];
    have h_exists : ∃ k : ℕ, k < secondIdx ∧ cs[k]! = c := by
      have h_exists : List.findIdx (fun x => x == c) cs < secondIdx := by
        grind;
      grind;
    obtain ⟨ k, hk₁, hk₂ ⟩ := h_exists;
    have h_take : c ∈ List.take secondIdx cs := by
      rw [ List.mem_iff_get ];
      use ⟨ k, by
        grind ⟩
      generalize_proofs at *;
      grind;
    grind

end AristotleLemmas

theorem postcondition_equiv (s : String) (result : Option Char) (h_precond : VerinaSpec.findFirstRepeatedChar_precond s):
  VerinaSpec.findFirstRepeatedChar_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- Let's unfold the definitions of `VerinaSpec.findFirstRepeatedChar_postcond` and `LeetProofSpec.postcondition`.
  unfold VerinaSpec.findFirstRepeatedChar_postcond LeetProofSpec.postcondition;
  constructor;
  · intro h;
    refine' ⟨ _, _, _ ⟩;
    · rintro c rfl;
      have := LeetProofSpec.secondIdx_spec s.toList c h.1;
      refine' ⟨ _, _, this.2.1 ⟩;
      rw [ LeetProofSpec.isFirstRepeatPos_iff ];
      grind;
    · intro h_none;
      rw [ LeetProofSpec.hasRepeatedChar_iff_not_nodup ];
      aesop;
    · cases result <;> simp_all +decide [ LeetProofSpec.ensures3 ];
      rw [ LeetProofSpec.hasRepeatedChar_iff_not_nodup ];
      exact Classical.not_not.2 ( List.Pairwise.imp_of_mem ( by aesop ) h );
  · intro h;
    rcases result with ( _ | c ) <;> simp_all +decide;
    · unfold LeetProofSpec.ensures2 at h;
      unfold LeetProofSpec.hasRepeatedChar at h;
      rw [ List.pairwise_iff_get ];
      norm_num +zetaDelta at *;
      intro i j hij; specialize h; have := h.2.1 j; simp_all +decide [ LeetProofSpec.appearsBeforePos ] ;
    · -- By definition of `ensures1`, there exists an index `i` such that `isFirstRepeatPos s.data i` and `s.data[i]! = c`.
      obtain ⟨i, hi⟩ : ∃ i, LeetProofSpec.isFirstRepeatPos s.data i ∧ s.data[i]! = c := by
        exact h.1 c rfl;
      -- Since $c$ appears at least twice in $s.data$, we have $s.data.count c ≥ 2$.
      have h_count : s.data.count c ≥ 2 := by
        have h_count : c ∈ s.data.take i := by
          have := hi.1.2.1;
          rw [ hi.2 ] at this; exact?;
        have h_count : c ∈ s.data.drop i := by
          rw [ List.mem_iff_get ] at *;
          use ⟨ 0, by
            simp +zetaDelta at *;
            exact hi.1.1 ⟩
          generalize_proofs at *;
          grind;
        rw [ ← List.take_append_drop i s.data, List.count_append ];
        exact le_trans ( by norm_num ) ( add_le_add ( List.count_pos_iff.mpr ‹_› ) ( List.count_pos_iff.mpr ‹_› ) );
      have h_secondIdx : let secondIdx := s.data.zipIdx.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c); secondIdx < s.data.length ∧ s.data[secondIdx]! = c ∧ secondIdx ≠ s.data.idxOf c ∧ c ∈ s.data.take secondIdx ∧ ∀ k < secondIdx, s.data[k]! = c → k = s.data.idxOf c := by
        exact?;
      have h_secondIdx_eq_i : i = s.data.zipIdx.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c) := by
        have h_secondIdx_eq_i : i < s.data.zipIdx.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c) → False := by
          have := hi.1.2.1; simp_all +decide [ LeetProofSpec.appearsBeforePos ] ;
          grind;
        refine' le_antisymm _ _ <;> contrapose! h_secondIdx_eq_i;
        · have := hi.1.2.2;
          specialize this ( List.findIdx ( fun x => Decidable.decide ( x.1 = c ) && Decidable.decide ( x.2 ≠ List.idxOf c s.data ) ) s.data.zipIdx ) h_secondIdx_eq_i ; simp_all +decide [ LeetProofSpec.appearsBeforePos_iff_mem_take ];
          grind;
        · exact ⟨ h_secondIdx_eq_i, trivial ⟩;
      have := hi.1; simp_all +decide [ LeetProofSpec.isFirstRepeatPos_iff ] ;
      exact hi.1.2.2