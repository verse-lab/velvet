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

def isPermutation (s1 s2: String) : Prop :=
  ∀ c, s1.toList.count c = s2.toList.count c

def noAdjacentSame (s: String) : Prop :=
  let chars := s.toList
  ∀ i, i + 1 < chars.length → chars[i]! ≠ chars[i + 1]!

def charCount (s: String) (c: Char) : Nat :=
  s.toList.count c

def maxCharFrequency (s: String) : Nat :=
  let chars := s.toList
  let uniqueChars := chars.eraseDups
  uniqueChars.foldl (fun max c => Nat.max max (charCount s c)) 0

def canRearrange (s: String) : Prop :=
  let n := s.length
  let maxFreq := maxCharFrequency s
  if n = 0 then True
  else maxFreq ≤ (n + 1) / 2

def ensures1 (s : String) (result : String) :=
  isPermutation s result

def ensures2 (s : String) (result : String) :=
  canRearrange s → noAdjacentSame result

def ensures3 (s : String) (result : String) :=
  canRearrange s → (∀ r, (isPermutation s r ∧ noAdjacentSame r) → result ≤ r)

def ensures4 (s : String) (result : String) :=
  ¬canRearrange s → result = s

def precondition (s: String) :=
  True

def postcondition (s: String) (result: String) :=
  ensures1 s result ∧ ensures2 s result ∧ ensures3 s result ∧ ensures4 s result

-- Test Cases
def test1_s : String := "aab"

def test1_Expected : String := "aba"

def test3_s : String := "abc"

def test3_Expected : String := "abc"

def test5_s : String := "aabb"

def test5_Expected : String := "abab"

def test6_s : String := ""

def test6_Expected : String := ""

def test8_s : String := "aaabbc"

def test8_Expected : String := "ababac"

def test11_s : String := "aaabbb"

def test11_Expected : String := "ababab"

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_s := by
  exact?

lemma test1_postcondition :
  postcondition test1_s test1_Expected := by
  -- Let's verify each part of the postcondition for the test case.
  apply And.intro;
  · intro c;
    simp [test1_s, test1_Expected]
    grind
  · aesop;
    · rintro h i hi; rcases i with ( _ | _ | i ) <;> trivial;
    · -- To prove that "aba" is the lexicographically minimal valid rearrangement of "aab", we need to show that among all permutations of "aab", "aba" is the smallest.
      have h_min : ∀ p : List Char, p.Perm ['a', 'a', 'b'] → (noAdjacentSame (String.mk p)) → String.mk p ≥ "aba" := by
        intros p hp hp'; have := hp.length_eq; aesop;
        rw [ List.length_eq_three ] at this; aesop;
        have := hp.subset ; aesop ( simp_config := { decide := true } ) ;
        exact absurd ( hp' 0 ) ( by decide );
      intro h;
      intro r hr;
      -- Since r is a permutation of "aab", its data must be a permutation of ['a', 'a', 'b'].
      have hr_perm : r.data.Perm ['a', 'a', 'b'] := by
        -- By definition of `isPermutation`, we know that `r.data` is a permutation of `test1_s.data` because the counts of each character are equal.
        apply List.perm_iff_count.mpr;
        exact fun a => hr.1 a ▸ rfl;
      exact h_min _ hr_perm hr.2;
    · -- Since `canRearrange test1_s` is true, the implication `¬canRearrange test1_s → result = test1_s` is trivially true.
      simp [ensures4, canRearrange];
      native_decide

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_s := by
  exact?

lemma test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition test3_s test3_Expected
  generalize_proofs at *;
  -- Let's verify each part of the postcondition for the input "abc" and the result "abc".
  constructor;
  · -- To prove that "abc" is a permutation of itself, we can use the fact that any string is a permutation of itself.
    intro c
    simp [List.count_cons, List.count_nil];
  · -- Since "abc" is already in lexicographic order and has no adjacent same characters, it is the smallest possible rearrangement.
    simp [ensures3, ensures4];
    -- Since "abc" is already in lexicographic order, any permutation of "abc" that has no adjacent same characters must be "abc" itself. Therefore, "abc" is the smallest possible rearrangement.
    have h_abc_min : ∀ r : String, isPermutation "abc" r → noAdjacentSame r → "abc" ≤ r := by
      -- Since "abc" is the smallest permutation of its characters, any other permutation that meets the conditions must be greater than or equal to "abc".
      intros r hr_perm hr_adj
      have h_le : r.toList ≥ ['a', 'b', 'c'] := by
        -- Since "abc" is the smallest permutation of its characters, any other permutation that meets the conditions must be greater than or equal to "abc". Therefore, we can conclude that r.toList ≥ ['a', 'b', 'c'].
        have h_min : ∀ r : List Char, r ∈ List.permutations ['a', 'b', 'c'] → noAdjacentSame (String.mk r) → ['a', 'b', 'c'] ≤ r := by
          simp +decide [ List.permutations ];
        apply h_min;
        · simp_all +decide [ isPermutation ];
          rw [ List.perm_iff_count ] ; aesop;
        · convert hr_adj using 1;
      cases r ; aesop;
    exact ⟨ fun _ i hi => by rcases i with ( _ | _ | i ) <;> trivial, fun _ r hr hr' => h_abc_min r hr hr' ⟩

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_s := by
  exact?

lemma test5_postcondition :
  postcondition test5_s test5_Expected := by
  refine' ⟨ _, _, _, _ ⟩;
  · -- To prove that "abab" is a permutation of "aabb", we need to show that for every character `c`, the count of `c` in "aabb" is equal to the count of `c` in "abab".
    have h_perm : ∀ c, charCount "aabb" c = charCount "abab" c := by
      intro c; unfold charCount; aesop;
      rw [ List.count_cons, List.count_cons, List.count_cons, List.count_cons ] ; aesop;
    exact h_perm;
  · exact fun h => by
      exact fun i hi => by rcases i with ( _ | _ | _ | _ | i ) <;> trivial;
  · -- We need to show that "abab" is the lexicographically smallest permutation of "aabb" with no adjacent duplicates.
    have h_lex_min : ∀ r : String, (isPermutation "aabb" r ∧ noAdjacentSame r) → "abab" ≤ r := by
      -- Since "abab" is the lexicographically smallest permutation of "aabb", any valid rearrangement r must satisfy "abab" ≤ r. We can prove this by considering the possible permutations of "aabb" and showing that "abab" is the smallest.
      have h_permutations : ∀ r : String, isPermutation "aabb" r → r = "aabb" ∨ r = "abab" ∨ r = "abba" ∨ r = "baab" ∨ r = "baba" ∨ r = "bbaa" := by
        intro r hr
        have h_perm : r.toList.Perm ['a', 'a', 'b', 'b'] := by
          -- By definition of isPermutation, we know that for every character c, the count of c in r is equal to the count of c in "aabb".
          have h_count : ∀ c, r.toList.count c = ['a', 'a', 'b', 'b'].count c := by
            exact?;
          rw [ List.perm_iff_count ] ; aesop;
        have h_perm_cases : ∀ l : List Char, l.Perm ['a', 'a', 'b', 'b'] → l = ['a', 'a', 'b', 'b'] ∨ l = ['a', 'b', 'a', 'b'] ∨ l = ['a', 'b', 'b', 'a'] ∨ l = ['b', 'a', 'a', 'b'] ∨ l = ['b', 'a', 'b', 'a'] ∨ l = ['b', 'b', 'a', 'a'] := by
          intro l hl; have := hl.length_eq; aesop;
          rcases l with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | l ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide;
          have := hl.subset; aesop;
          all_goals contradiction;
        rcases h_perm_cases _ h_perm with ( h | h | h | h | h | h ) <;> simp_all +decide [ String.ext_iff ];
      rintro r ⟨ hr₁, hr₂ ⟩ ; rcases h_permutations r hr₁ with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +decide at hr₂ ⊢;
      exact absurd ( hr₂ 0 ( by decide ) ) ( by decide );
    -- Apply the hypothesis `h_lex_min` to conclude that "abab" is the lexicographically smallest permutation of "aabb" with no adjacent duplicates.
    apply fun h => h_lex_min;
  · -- Since canRearrange test5_s is true, we need to show that test5_Expected is a permutation of test5_s and that it has no adjacent duplicates.
    simp [ensures4, test5_s, test5_Expected];
    simp +decide [ canRearrange ]

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_s := by
  exact?

lemma test6_postcondition :
  postcondition test6_s test6_Expected := by
  constructor;
  · exact fun _ => rfl;
  · -- Since the input string is empty, the function returns the empty string, and thus the postcondition holds trivially.
    simp [test6_s, test6_Expected, ensures2, ensures3, ensures4];
    -- Since the empty string is a permutation of any string, and the only permutation of the empty string is the empty string itself, we have `isPermutation "" r → r = ""`.
    have h_empty_perm : ∀ r : String, isPermutation "" r → r = "" := by
      -- If `isPermutation "" r` holds, then for every character `c`, the count of `c` in `""` is equal to the count in `r`.
      intro r hr
      have h_count : ∀ c, ("" : String).toList.count c = r.toList.count c := by
        exact hr;
      -- Since the count of every character in the empty string is zero, this implies that the count of every character in r must also be zero.
      have h_zero_count : ∀ c, r.toList.count c = 0 := by
        exact fun c => h_count c ▸ rfl;
      -- Since the count of every character in r is zero, r must be empty.
      have h_empty : r.toList = [] := by
        exact List.eq_nil_iff_forall_not_mem.mpr fun c hc => by have := h_zero_count c; rw [ List.count_eq_zero ] at this; aesop;
      cases r ; aesop;
    -- Since the empty string is a permutation of any string, and the only permutation of the empty string is the empty string itself, we have `isPermutation "" r → r = ""`. Therefore, `noAdjacentSame ""` holds.
    simp [noAdjacentSame, h_empty_perm];
    -- Since the empty string is a permutation of any string, and the only permutation of the empty string is the empty string itself, we have `isPermutation "" r → r = ""`. Therefore, `"" ≤ r` holds trivially because the empty string is less than or equal to any string.
    intros h_rearrange r hr_perm hr_adjacent
    simp [h_empty_perm r hr_perm]

----------------------------
-- Verification: test8
----------------------------
lemma test8_precondition :
  precondition test8_s := by
  exact?

lemma test8_postcondition :
  postcondition test8_s test8_Expected := by
  constructor;
  · -- To prove the permutation condition, we need to show that for every character, the count in the input string is equal to the count in the expected result.
    intro c
    simp [test8_s, test8_Expected];
    rw [ List.count_cons, List.count_cons, List.count_cons, List.count_cons, List.count_cons, List.count_cons ] ; aesop;
  · unfold test8_s test8_Expected;
    unfold ensures2 ensures3 ensures4;
    aesop;
    · rintro ( _ | _ | _ | _ | _ | _ | i ) hi <;> trivial;
    · -- Since $r$ is a permutation of "aaabbc", its data must be a permutation of the list ['a', 'a', 'a', 'b', 'b', 'c'].
      have h_perm : r.data.Perm ['a', 'a', 'a', 'b', 'b', 'c'] := by
        -- By definition of `isPermutation`, we know that the count of each character in `r` is the same as in `"aaabbc"`.
        have h_count : ∀ c, r.data.count c = "aaabbc".data.count c := by
          exact?;
        grind;
      have := h_perm.length_eq; simp_all +decide ;
      rcases r with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | r ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide;
      have := h_perm.subset; simp_all +decide ;
      rcases this with ⟨ rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp +decide at h_perm ⊢;
      all_goals have := a_2 0; have := a_2 1; have := a_2 2; have := a_2 3; have := a_2 4; have := a_2 5; simp_all +decide ;
    · -- Let's calculate the maximum frequency of any character in "aaabbc".
      simp [canRearrange, maxCharFrequency];
      native_decide

----------------------------
-- Verification: test11
----------------------------
lemma test11_precondition :
  precondition test11_s := by
  exact?

lemma test11_postcondition :
  postcondition test11_s test11_Expected := by
  -- Let's verify each part of the postcondition for the test case.
  constructor;
  · -- Let's choose any character `c`.
    intro c
    simp [test11_s, test11_Expected];
    grind +ring;
  · unfold ensures2; unfold ensures3; unfold ensures4; aesop;
    · intro i hi; rcases i with ( _ | _ | _ | _ | _ | _ | i ) <;> trivial;
    · -- Since $r$ is a permutation of $test11_s$, its data must be a permutation of the list $['a', 'a', 'a', 'b', 'b', 'b']$.
      have h_perm : r.data.Perm ['a', 'a', 'a', 'b', 'b', 'b'] := by
        -- Since `r` is a permutation of `test11_s`, and `test11_s` has the data `['a', 'a', 'a', 'b', 'b', 'b']`, we can conclude that `r.data` is also a permutation of `['a', 'a', 'a', 'b', 'b', 'b']`.
        have h_perm : List.Perm (test11_s.toList) (r.toList) := by
          exact?;
        exact h_perm.symm.trans ( by native_decide );
      have := h_perm.length_eq; simp_all +decide ;
      rcases r with ⟨ ⟨ l, hl ⟩ ⟩ <;> aesop;
      rcases tail with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | tail ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide ;
      have := h_perm.subset; simp_all +decide ;
      rcases this with ⟨ rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl, rfl | rfl ⟩ <;> simp_all +decide;
      · exact absurd ( a_2 0 ) ( by decide );
      · exact absurd ( a_2 0 ) ( by decide );
      · exact absurd ( a_2 0 ( by decide ) ) ( by decide );
      · exact absurd ( a_2 0 ) ( by decide );
      · exact absurd ( a_2 2 ( by decide ) ) ( by decide );
    · contrapose! a; aesop;
      unfold canRearrange; simp +decide ;

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (s: String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro h1
  intro ret1 ret2
  intro hret1 hret2
  obtain ⟨hret11, hret12, hret13, hret14⟩ := hret1
  obtain ⟨hret21, hret22, hret23, hret24⟩ := hret2;
  by_cases h : canRearrange s <;> simp_all +decide [ ensures3 ];
  · exact?;
  · unfold ensures4 at *; aesop;
