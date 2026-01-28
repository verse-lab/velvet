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

-- Helper Functions

-- Postcondition clauses
def ensures1 (n : Nat) (result : Nat) :=
  ∀ i < n.size,
    if i % 2 = 0 then
      result.testBit i = true
    else
      result.testBit i = n.testBit i

def ensures2 (n : Nat) (result : Nat) :=
  ∀ i ≥ n.size, result.testBit i = false

def precondition (n: Nat) :=
  True

def postcondition (n: Nat) (result: Nat) :=
  ensures1 n result ∧ ensures2 n result

-- Test Cases
def test1_n : Nat := 10

def test1_Expected : Nat := 15

def test2_n : Nat := 4

def test2_Expected : Nat := 5

def test3_n : Nat := 0

def test3_Expected : Nat := 0

def test4_n : Nat := 255

def test4_Expected : Nat := 255

def test5_n : Nat := 85

def test5_Expected : Nat := 85

def test6_n : Nat := 1

def test6_Expected : Nat := 1

def test7_n : Nat := 8

def test7_Expected : Nat := 13

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_n := by
  exact?

lemma test1_postcondition :
  postcondition test1_n test1_Expected := by
  -- Let's verify the postcondition for test1.
  unfold postcondition ensures1 ensures2 test1_n test1_Expected
  skip
  generalize_proofs at *;
  -- Let's verify the postcondition for the test case where n = 10.
  simp [Nat.size, Nat.testBit];
  -- Let's verify the postcondition for the test case where n = 10 by checking each bit position.
  simp [Nat.binaryRec] at *;
  -- Let's verify the postcondition for the test case where n = 10 by checking each bit position and ensuring the conditions hold.
  apply And.intro;
  · native_decide +revert;
  · intro i hi; rcases i with ( _ | _ | _ | _ | _ | i ) <;> norm_num [ Nat.shiftRight_eq_div_pow ] at *;
    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_n := by
  exact?

lemma test2_postcondition :
  postcondition test2_n test2_Expected := by
  -- Let's verify the postcondition for test2_n and test2_Expected.
  apply And.intro
  intro i hi
  by_cases h : i % 2 = 0
  all_goals generalize_proofs at *;
  · native_decide +revert;
  · native_decide +revert;
  · -- For i ≥ 3, the result's testBit i is 0, which matches false.
    intros i hi
    simp [ensures2, test2_n, test2_Expected];
    rcases i with ( _ | _ | _ | _ | _ | _ | i ) <;> simp_all +arith +decide [ Nat.testBit ];
    · exact absurd hi ( by native_decide );
    · exact absurd hi ( by native_decide );
    · norm_num [ Nat.shiftRight_eq_div_pow ];
      rw [ Nat.div_eq_of_lt ] ; norm_num [ Nat.pow_succ' ];
      linarith [ Nat.one_le_pow i 2 zero_lt_two ]

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_n := by
  exact?

lemma test3_postcondition :
  postcondition test3_n test3_Expected := by
  -- For the case when n = 0, the result is 0. We need to verify that 0 satisfies the postcondition.
  simp [postcondition, test3_n, test3_Expected];
  -- Since `n = 0`, its binary representation is empty, so there are no bits to check. Therefore, `ensures1` and `ensures2` are trivially satisfied.
  simp [ensures1, ensures2];
  -- Since the size of 0 is 0, there are no natural numbers i less than 0. Therefore, the statement is vacuously true.
  simp [Nat.size]

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_n := by
  exact?

lemma test4_postcondition :
  postcondition test4_n test4_Expected := by
  -- For the postcondition, we need to show that for all i < test4_n.size, the i-th bit of test4_Expected is 1 if i is even and 0 if i is odd.
  apply And.intro;
  · -- By definition of `test4_n` and `test4_Expected`, we need to show that for all `i < 8`, if `i` is even, then `test4_Expected.testBit i` is true, and if `i` is odd, then `test4_n.testBit i` is true.
    intro i hi
    simp [test4_n, test4_Expected] at hi ⊢
    skip
    skip
    generalize_proofs at *;
    native_decide +revert;
  · -- For i ≥ 8, the i-th bit of 255 is false.
    intro i hi
    simp [Nat.testBit] at *;
    -- Since $test4\_Expected = 255$, we can replace it in the goal.
    have h_test4_Expected : test4_Expected = 255 := by
      rfl
    rw [h_test4_Expected] at *; (
    norm_num [ Nat.shiftRight_eq_div_pow ] at *;
    rw [ Nat.div_eq_of_lt ] ; linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show i ≥ 8 by exact le_trans ( by native_decide ) hi ) ] ;);

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_n := by
  exact?

lemma test5_postcondition :
  postcondition test5_n test5_Expected := by
  -- Let's verify the postcondition for test5.
  constructor;
  · -- Let's verify the postcondition for test5_n.
    unfold ensures1;
    native_decide +revert;
  · -- Since test5_n is 85, which is 1010101 in binary, it has 7 bits. Therefore, for any i ≥ 7, test5_n.testBit i is false.
    have h_test5_n_size : test5_n.size = 7 := by
      native_decide;
    intro i hi; rcases i with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i ) <;> simp_all +arith +decide [ Nat.shiftRight_eq_div_pow ] ;
    -- Since test5_Expected is 85, which is 1010101 in binary, it has 7 bits. Therefore, for any i ≥ 7, test5_Expected.testBit i is false.
    have h_test5_Expected_size : test5_Expected < 2 ^ (i + 10) := by
      exact lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_add_left _ _ ) );
    simp_all +decide [ Nat.testBit ];
    simp_all +decide [ Nat.shiftRight_eq_div_pow ];
    rw [ Nat.div_eq_of_lt h_test5_Expected_size, Nat.zero_mod ]

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_n := by
  exact?

lemma test6_postcondition :
  postcondition test6_n test6_Expected := by
  -- For the test case n = 1, the result is 1, which is correct because the least significant bit is already 1.
  simp [postcondition, test6_n, test6_Expected];
  -- Let's unfold the definitions of `ensures1` and `ensures2`.
  unfold ensures1 ensures2;
  -- For the first part, since the size of 1 is 1, the only possible value for i is 0. We need to check if 0 is even, which it is, and then verify that the testBit of 1 at position 0 is true.
  simp [Nat.size];
  -- For any $i \geq 1$, the $i$-th bit of $1$ is $0$ because $1$ in binary is $0b1$.
  intros i hi
  simp [Nat.testBit, hi];
  -- Since $1 \leq i$, we have $1 >>> i = 0$.
  have h_shift : 1 >>> i = 0 := by
    cases i <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
  rw [ h_shift, Nat.zero_mod ]

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_n := by
  exact?

lemma test7_postcondition :
  postcondition test7_n test7_Expected := by
  unfold postcondition;
  -- Let's verify the postcondition for test7.
  simp [ensures1, ensures2];
  constructor;
  · native_decide;
  · intro i hi;
    rcases i with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | i ) <;> simp_all +arith +decide [ Nat.testBit ];
    · exact absurd hi ( by native_decide );
    · exact absurd hi ( by native_decide );
    · exact absurd hi ( by native_decide );
    · norm_num [ test7_n, test7_Expected, Nat.shiftRight_eq_div_pow ] at *;
      norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  rintro - ret1 ret2 ⟨ h1, h2 ⟩ ⟨ h3, h4 ⟩;
  refine' Nat.eq_of_testBit_eq _;
  intro i; by_cases hi : i < n.size;
  · have := h1 i hi; have := h3 i hi; aesop;
  · rw [ h2 i ( le_of_not_gt hi ), h4 i ( le_of_not_gt hi ) ]
