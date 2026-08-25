module

public import Velvet.Core.Named
public meta import Velvet.Core.Named
public import Velvet.Core.Specs
public meta import Velvet.Core.Specs
public import Velvet.Core.Loop.Gadgets
public import Lean.Data.KVMap
public meta import Lean.Parser
public meta import Lean.Elab.Do
public meta import Lean.Elab.BuiltinDo.Let
public meta import Lean.Elab.Command
public meta import Lean.Meta.ProdN
public meta import Lean.Elab.Do.Control
public meta import Lean.Elab.BuiltinDo.For
public meta import Lean.Meta.Basic
public meta import Lean.Elab.Term
public import Std.WP

syntax (name := doWhilePrime) "while' " (atomic(ident " : "))? termBeforeDo
  (" invariant " (atomic(ident " : "))? velvSpecTerm)*
  (" decreasing " (atomic(ident " : "))? velvSpecTerm)?
  (" done_with " (atomic(ident " : "))? velvSpecTerm (" by " tacticSeq)?)?
  " do " doSeq : doElem

/--
A finite range loop with inline state invariants. Like Lean's built-in `for`,
the collection controls termination; the initial version supports one binder
and one collection, including closed-open ranges such as `start...stop`.
-/
syntax (name := doForPrime) "for' " (atomic(ident " : "))? term " in " termBeforeDo
  (" invariant " (atomic(ident " : "))? velvSpecTerm)*
  (" done_with " (atomic(ident " : "))? velvSpecTerm)?
  " do " doSeq : doElem


open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.WP Named
open Lean Meta Elab
open Lean.Parser.Term
open Lean.Elab.Do

public meta partial def checkWhileTermination (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(doElem| while' $[$_hcond : ]? $_cond $[ invariant $[$_ns : ]? $_invs]* $[decreasing $[$_hm : ]? $m]? $[done_with $[$_h_done : ]? $_d]? do $_body) =>
      if m.isNone then
        /- Fires when a `while'` loop in a total-correctness method has no `decreasing` clause,
           e.g. `while' i < n invariant True do ...` without `decreasing remaining : n - i`. -/
        throwErrorAt stx "`while'` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness"
  | _ => pure ()
  for a in stx.getArgs do
    checkWhileTermination a

/-- Recursively checks whether a syntax tree contains an identifier matching or prefixed by `name`. -/
public meta partial def syntaxContainsIdent (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then
    stx.getId == name || name.isPrefixOf stx.getId
  else
    stx.getArgs.any (syntaxContainsIdent name)

/-- Classification of `for'` loop invariants.
* `pureState`: Invariants depend only on mutable loop state (do not mention cursor `x`, `__pref`, or `__rest`),
  and no `done_with` was specified. The invariant is used as both step invariant and exit condition.
* `invAndDone`: Invariants depend on traversal cursor / `__rest`, or an explicit `done_with` was provided. -/
public inductive ForLoopInvKind where
  | /-- Pure state invariants: invariant holds at entry, step, and exit. -/
    pureState
  | /-- Step invariants with explicit exit condition (`done_with`), or cursor-dependent invariants. -/
    invAndDone (doneTerm : Term) (doneName : Name)

/-- Classifies whether a `for'` loop can use the streamlined pure state-invariant gadget
or requires the full step-and-done traversal gadget.
Uses speculative elaboration in the pure-state scope to correctly handle shadowed binders
(e.g., quantifiers `∀ i : Nat, ...` where `i` shadows the loop cursor).
If an invariant actually references the cursor variable or progress variables without specifying `done_with`,
a clear diagnostic error is thrown with suggestions for fixing it. -/
public meta def classifyForLoopInvariants (cursorId : Name) (invs : Array Term) (ns : Array (Option Ident))
    (stateInvLam : Term) (done? : Option Term) (hDone? : Option (Option Ident)) : TermElabM ForLoopInvKind := do
  match done? with
  | some doneStx =>
    let doneName := hDone?.join.map (fun (id : Ident) => id.getId) |>.getD `h_done_with
    return .invAndDone doneStx doneName
  | none =>
    -- Speculatively elaborate the state invariant closure in state-only context
    let canElabPureState ← withoutModifyingState do
      try
        withoutErrToSorry do
          let _ ← Term.elabTerm stateInvLam none
          Term.synthesizeSyntheticMVars (postpone := .no)
          pure true
      catch _ =>
        pure false
    if canElabPureState then
      return .pureState

    -- If state-only elaboration failed, inspect which invariant caused the failure
    for inv in invs, n? in ns do
      if syntaxContainsIdent cursorId inv.raw then
        let nameStr := match n? with
          | some id => s!"'{id.getId}' "
          | none => ""
        throwErrorAt inv
          m!"Loop invariant {nameStr}references loop cursor variable '{cursorId}'.\n\
             Cursor-dependent invariants require an explicit 'done_with' clause because '{cursorId}' is not in scope after the loop terminates.\n\
             Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes."
      if syntaxContainsIdent `__rest inv.raw then
        let nameStr := match n? with
          | some id => s!"'{id.getId}' "
          | none => ""
        throwErrorAt inv
          m!"Loop invariant {nameStr}references '__rest'.\n\
             Suffix-dependent invariants require an explicit 'done_with' clause because there are no remaining elements after the loop terminates.\n\
             Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes."
      if syntaxContainsIdent `__pref inv.raw then
        let nameStr := match n? with
          | some id => s!"'{id.getId}' "
          | none => ""
        throwErrorAt inv
          m!"Loop invariant {nameStr}references '__pref'.\n\
             Prefix-dependent invariants require an explicit 'done_with' clause specifying what holds when the loop finishes.\n\
             Hint: Add 'done_with <tag>: <exit_condition>' specifying what holds when the loop finishes."

    -- If none of cursorId / __rest / __pref was found, re-elaborate to surface the real error (e.g. type mismatch)
    let _ ← Term.elabTerm stateInvLam none
    return .pureState

private meta def mkStatePat (loopMutVars : Array MutVar) (returnsEarly : Bool) : DoElabM Term := do
  let hole ← `(_)
  let mut binders : Array Term := #[]
  if returnsEarly then binders := binders.push hole
  for mv in loopMutVars do binders := binders.push ⟨mv.ident.raw⟩
  if returnsEarly && loopMutVars.isEmpty then binders := binders.push hole
  match binders with
    | #[]  => `(_)
    | #[b] => pure b
    | _    => `(⟨$binders,*⟩)

@[doElem_control_info doForPrime]
public meta def controlInfoDoForPrime : ControlInfoHandler := fun stx => do
  let `(doElem| for' $[$_h? : ]? $_pat in $_xs $[ invariant $[$_ns : ]? $_invs]* $[done_with $[$_hDone : ]? $_done]? do $body) := stx
    | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  return { reassigns := bodyInfo.reassigns, returnsEarly := bodyInfo.returnsEarly }

@[doElem_elab doForPrime]
public meta def elabDoForPrime : DoElab := fun stx dec => do
  let `(doElem| for' $[$h? : ]? $pat in $xs $[ invariant $[$ns : ]? $invs]* $[done_with $[$hDone : ]? $done]? do $body) := stx
    | throwUnsupportedSyntax
  let invs ← liftMacroM <| invs.mapM specTermToTerm
  let done ← liftMacroM <| done.mapM specTermToTerm
  let dec ← dec.ensureUnitAt stx
  let (x, body) ←
    if pat.raw.isIdent then
      pure (⟨pat.raw⟩, body)
    else if pat.raw.isOfKind ``Lean.Parser.Term.hole then
      let x ← mkFreshIdent pat
      pure (x, body)
    else
      let x ← mkFreshIdent pat
      let newBody ← `(doSeq| match $x:term with | $pat => $body)
      pure (x, newBody)
  checkMutVarsForShadowing #[x]
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (uα.succ)) (userName := `α)
  let ρ ← mkFreshExprMVar (mkSort (uρ.succ)) (userName := `ρ)
  let xs ← Term.elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let mutVars := (← read).mutVars

  let info ← inferControlInfoSeq body
  let oldReturnCont ← getReturnCont
  let returnVarName ← mkFreshUserName `__r
  let loopMutVars := mutVars.filter fun x => info.reassigns.contains x.getId
  let loopMutVarNames :=
    if info.returnsEarly then
      returnVarName :: (loopMutVars.map (·.getId)).toList
    else
      (loopMutVars.map (·.getId)).toList
  let useLoopMutVars (e : Option Expr) : TermElabM (Array Expr) := do
    let mut defs := #[]
    unless e.isNone || info.returnsEarly do
      throwError "Early returning {e} but the info said there is no early return"
    if info.returnsEarly then
      let returnVar ←
        match e with
        | none => mkNone oldReturnCont.resultType
        | some e => mkSome oldReturnCont.resultType e
      defs := defs.push returnVar
    for x in loopMutVars do
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x.ident defn.toExpr
      let u ← getDecLevel defn.type
      discard <| isLevelDefEq u mi.u
      defs := defs.push defn.toExpr
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs

  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u

  let s ← mkFreshUserName `__s
  let (_p?, xh) : Option Expr × Array (Name × (Array Expr → DoElabM Expr)) ← match h? with
    | none =>
      pure (none, #[(x.getId, fun _ => pure α)])
    | some h =>
      let d ← mkFreshExprMVar (mkApp2 (mkConst ``Membership [uα, uρ]) α ρ) (userName := `d)
      pure (some d, #[(x.getId, fun _ => pure α),
        (h.getId, fun x => pure (mkApp5 (mkConst ``Membership.mem [uα, uρ]) α ρ d xs x[0]!))])

  let body ←
    withLocalDeclsD xh fun xh => do
    Term.addLocalVarInfo x xh[0]!
    if let some h := h? then
      Term.addLocalVarInfo h xh[1]!
    withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
    mkLambdaFVars (xh.push loopS) <| ← do
    bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
    let newDoBlockResultType := mkApp (mkConst ``ForInStep [mi.u]) σ
    withDoBlockResultType newDoBlockResultType do
    let continueCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let yield := mkApp2 (mkConst ``ForInStep.yield [mi.u]) σ tuple
      mkPureApp newDoBlockResultType yield
    let breakCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
      mkPureApp newDoBlockResultType done
    let returnCont := { oldReturnCont with k := fun e => do
        let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars (some e)) mi.u
        let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
        mkPureApp newDoBlockResultType done
      }
    enterLoopBody breakCont continueCont returnCont do
    elabDoSeq body { dec with k := continueCont, kind := .duplicable }

  let statePat ← mkStatePat loopMutVars info.returnsEarly
  let invs' ← liftMacroM <| mkAssertionList invs (makeNameArrayFromIdents ns "invariant")
  let stateInvLam ← `(fun $statePat => $invs')
  let forIn ← match ← classifyForLoopInvariants x.getId invs ns stateInvLam done hDone with
    | .pureState =>
      let gadget := if h?.isSome then ``Loop.Gadget.forInPureWithStateInv'
        else ``Loop.Gadget.forInPureWithStateInv
      let call ← `($(mkIdent gadget) $(← Term.exprToSyntax xs) $(← Term.exprToSyntax preS)
        $(← Term.exprToSyntax body) $stateInvLam)
      Term.elabTermEnsuringType call (mkApp mi.m σ)
    | .invAndDone doneTerm doneName =>
      let done' ← liftMacroM <| mkAssertionList #[doneTerm] #[doneName]
      let pref := mkIdent `__pref
      let rest := mkIdent `__rest
      let invLam ← `(fun $pref:ident $x:ident $rest:ident $statePat => $invs')
      let doneLam ← `(fun $pref:ident $statePat => $done')
      let gadget := if h?.isSome then ``Loop.Gadget.forInPureWithInvAndDone'
        else ``Loop.Gadget.forInPureWithInvAndDone
      let call ← `($(mkIdent gadget) $(← Term.exprToSyntax xs) $(← Term.exprToSyntax preS)
        $(← Term.exprToSyntax body) $invLam $doneLam)
      Term.elabTermEnsuringType call (mkApp mi.m σ)

  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
        if info.returnsEarly then
          let ret ← getFVarFromUserName returnVarName
          let ret ← if loopMutVars.isEmpty then mkAppM ``Prod.fst #[ret] else pure ret
          let motive := mkLambda `_ .default (← inferType ret) (← mkMonadApp γ)
          let app := mkApp3 (mkConst ``Break.runK.match_1 [mi.u, mi.v.succ]) oldReturnCont.resultType motive ret
          let none := mkSimpleThunk (← dec.continueWithUnit)
          let some ← withLocalDeclD (← mkFreshUserName `r) oldReturnCont.resultType fun r => do
            mkLambdaFVars #[r] (← oldReturnCont.k r)
          return mkApp2 app some none
        else
          dec.continueWithUnit

  mkBindApp σ γ forIn rest

@[doElem_control_info doWhilePrime]
public meta def controlInfoDoWhilePrime : ControlInfoHandler := fun stx => do
  let `(doElem| while' $[$_hcond : ]? $_cond $[ invariant $[$_ns : ]? $_invs]* $[decreasing $[$_hm : ]? $_m]? $[done_with $[$_h_done : ]? $_d]? do $body) := stx
    | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  return { reassigns := bodyInfo.reassigns, returnsEarly := bodyInfo.returnsEarly }

@[doElem_elab doWhilePrime]
public meta def elabDoWhilePrime : DoElab := fun stx dec => do
  let `(doElem| while' $[$hcond : ]? $cond $[ invariant $[$ns : ]? $invs]* $[decreasing $[$hm : ]? $m]? $[done_with $[$h_done : ]? $d]? do $body) := stx
    | throwUnsupportedSyntax
  let invs ← liftMacroM <| invs.mapM specTermToTerm
  let d ← liftMacroM <| d.mapM specTermToTerm
  let m ← liftMacroM <| m.mapM specTermToTerm
  let dec ← dec.ensureUnitAt stx
  let defaultLoopIdent := mkIdent `h_loop
  let loopIdent := hcond.getD defaultLoopIdent
  let loopBody ← `(doSeq|
    if $loopIdent:ident : $cond then
      do $body
    else
      break)

  let mi := (← read).monadInfo
  let mutVars := (← read).mutVars

  let info ← inferControlInfoSeq loopBody
  let oldReturnCont ← getReturnCont
  let returnVarName ← mkFreshUserName `__r
  let loopMutVars := mutVars.filter fun x => info.reassigns.contains x.getId
  let loopMutVarNames :=
    if info.returnsEarly then
      returnVarName :: (loopMutVars.map (·.getId)).toList
    else
      (loopMutVars.map (·.getId)).toList
  let useLoopMutVars (e : Option Expr) : TermElabM (Array Expr) := do
    let mut defs := #[]
    unless e.isNone || info.returnsEarly do
      throwError "Early returning {e} but the info said there is no early return"
    if info.returnsEarly then
      let returnVar ←
        match e with
        | none => mkNone oldReturnCont.resultType
        | some e => mkSome oldReturnCont.resultType e
      defs := defs.push returnVar
    for x in loopMutVars do
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x.ident defn.toExpr
      let u ← getDecLevel defn.type
      discard <| isLevelDefEq u mi.u
      defs := defs.push defn.toExpr
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs

  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u

  let s ← mkFreshUserName `__s
  let uVar ← mkFreshUserName `__u
  let α := Lean.mkConst ``Unit
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := #[(uVar, fun _ => pure α)]

  let body ←
    withLocalDeclsD xh fun xh => do
    withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
    mkLambdaFVars (xh.push loopS) <| ← do
    bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
    let newDoBlockResultType := mkApp (mkConst ``ForInStep [mi.u]) σ
    withDoBlockResultType newDoBlockResultType do
    let continueCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let yield := mkApp2 (mkConst ``ForInStep.yield [mi.u]) σ tuple
      mkPureApp newDoBlockResultType yield
    let breakCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
      mkPureApp newDoBlockResultType done
    let returnCont := { oldReturnCont with k := fun e => do
        let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars (some e)) mi.u
        let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
        mkPureApp newDoBlockResultType done
      }
    enterLoopBody breakCont continueCont returnCont do
    elabDoSeq loopBody { dec with k := continueCont, kind := .duplicable }

  let statePat ← mkStatePat loopMutVars info.returnsEarly
  let invNames := makeNameArrayFromIdents ns "invariant"
  let invs' ← liftMacroM <| mkAssertionList invs invNames
  let defaultDoneWith ← withRef cond do `(¬ $cond)
  let doneWith := d.getD defaultDoneWith
  let doneName := h_done.join.map (fun (id : Ident) => id.getId) |>.getD `h_done_with
  let exitedInvs ← liftMacroM <| mkAssertionList (invs.push doneWith) (invNames.push doneName)
  let invLam ← `(fun $statePat => $invs')
  let doneLam ← `(fun $statePat => $exitedInvs)

  let forIn ← match m with
    | none =>
      let opts ← getOptions
      let isPartial : Bool := match opts.get? `velvet.semantics.termination with
        | some (Lean.DataValue.ofString s) => s == "partial"
        | _ => false
      if isPartial == true then
        let gadget := ``Loop.Gadget.whileLoopPartial
        let call ← `($(mkIdent gadget) $(← Term.exprToSyntax preS) $(← Term.exprToSyntax body) $invLam $doneLam)
        Term.elabTermEnsuringType call (mkApp mi.m σ)
      else
        throwError "`while'` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness"
    | some m =>
      let measureName := hm.join.map (fun (id : Ident) => id.getId) |>.getD `termination
      let measureNameStr := Lean.Syntax.mkStrLit measureName.toString
      let measureNameTerm : TSyntax `term ← `(Lean.Name.mkSimple $measureNameStr)
      let measureStx ← liftMacroM <| Named.sourceRefTerm m.raw
      let measureTerm ← `(Named.Measure.mk $measureNameTerm $measureStx $m)
      let measureLam ← `(fun $statePat => $measureTerm)
      let gadget := ``Loop.Gadget.whileLoopTotal
      let call ← `($(mkIdent gadget) $(← Term.exprToSyntax preS) $(← Term.exprToSyntax body) $invLam $doneLam $measureLam)
      Term.elabTermEnsuringType call (mkApp mi.m σ)

  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
        if info.returnsEarly then
          let ret ← getFVarFromUserName returnVarName
          let ret ← if loopMutVars.isEmpty then mkAppM ``Prod.fst #[ret] else pure ret
          let motive := mkLambda `_ .default (← inferType ret) (← mkMonadApp γ)
          let app := mkApp3 (mkConst ``Break.runK.match_1 [mi.u, mi.v.succ]) oldReturnCont.resultType motive ret
          let none := mkSimpleThunk (← dec.continueWithUnit)
          let some ← withLocalDeclD (← mkFreshUserName `r) oldReturnCont.resultType fun r => do
            mkLambdaFVars #[r] (← oldReturnCont.k r)
          return mkApp2 app some none
        else
          dec.continueWithUnit

  mkBindApp σ γ forIn rest
