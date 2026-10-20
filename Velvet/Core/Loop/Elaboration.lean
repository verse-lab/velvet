module

public import Velvet.Core.Named
public meta import Velvet.Core.Named
public import Velvet.Core.Specs
public meta import Velvet.Core.Specs
public meta import Velvet.Core.AssertionTypes
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
public meta import Init.Data.Erased

/-- A `while` loop with Velvet clauses. Without any clause it elaborates as Lean's own `while`,
except under partial correctness, where Velvet's fixed-point loop verifies it. -/
syntax (name := doWhileVelvet) (priority := high) "while " (atomic(ident " : "))? termBeforeDo
  (" invariant " (atomic(ident " : "))? velvSpecTerm)*
  (" decreasing " (atomic(ident " : "))? velvSpecTerm)?
  (" done_with " (atomic(ident " : "))? velvSpecTerm)?
  " do " doSeq : doElem

/--
A finite range loop with inline state invariants. Like Lean's built-in `for`,
the collection controls termination; the initial version supports one binder
and one collection, including closed-open ranges such as `start...stop`.
Without any clause it elaborates as Lean's own `for`.
-/
syntax (name := doForVelvet) (priority := high) "for " (atomic(ident " : "))? term " in " termBeforeDo
  (" invariant " (atomic(ident " : "))? velvSpecTerm)*
  (" done_with " (atomic(ident " : "))? velvSpecTerm)?
  " do " doSeq : doElem

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.WP Named
open Lean Meta Elab
open Lean.Parser.Term
open Lean.Elab.Do

public meta partial def checkWhileTermination (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(doElem| while $[$_hcond : ]? $_cond $[ invariant $[$_ns : ]? $_invs]* $[decreasing $[$_hm : ]? $m]? $[done_with $[$_h_done : ]? $_d]? do $_body) =>
      if m.isNone then
        /- Fires when a `while` loop in a total-correctness method has no `decreasing` clause,
           e.g. `while i < n invariant True do ...` without `decreasing remaining : n - i`. -/
        throwErrorAt stx "`while` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness"
  | _ => pure ()
  stx.getArgs.forM checkWhileTermination

/-- Recursively checks whether a syntax tree contains an identifier matching or prefixed by `name`. -/
public meta partial def syntaxContainsIdent (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then
    stx.getId == name || name.isPrefixOf stx.getId
  else
    stx.getArgs.any (syntaxContainsIdent name)

/-- Classification of `for` loop invariants.
* `pureState`: Invariants depend only on mutable loop state (do not mention cursor `x`, `__pref`, or `__rest`),
  and no `done_with` was specified. The invariant is used as both step invariant and exit condition.
* `invAndDone`: Invariants depend on traversal cursor / `__rest`, or an explicit `done_with` was provided. -/
public inductive ForLoopInvKind where
  | /-- Pure state invariants: invariant holds at entry, step, and exit. -/
    pureState
  | /-- Step invariants with explicit exit condition (`done_with`), or cursor-dependent invariants. -/
    invAndDone (doneTerm : Term) (doneName : Name)

/-- Classifies whether a `for` loop can use the streamlined pure state-invariant gadget
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


/-- The pattern that names the loop's mutable variables. When the body can `return`, the state
tuple is `(return slot, mutable variables)`, and annotations range over the mutable variables
only: the loop only continues from states that have not returned. -/
private meta def mkStatePat (loopMutVars : Array MutVar) : DoElabM Term := do
  -- Velvet's `for` syntax, declared above, shadows Lean's in this file; map instead.
  let binders : Array Term := loopMutVars.map (fun mv => ⟨mv.ident.raw⟩)
  match binders with
    | #[]  => `(_)
    | #[b] => pure b
    | _    => `(⟨$binders,*⟩)

/-- The already-elaborated pieces of a loop that a Velvet loop gadget is built from. This is
`Lean.Elab.Do.ForInApp` without the collection, which only `for` loops pass to their gadget. -/
meta structure LoopApp where
  /-- The initial state tuple. -/
  init : Expr
  /-- The loop body, a function from the per-iteration binders and the state tuple to a
  `ForInStep`. -/
  body : Expr
  /-- The type of the state tuple. -/
  σ : Expr
  /-- The pattern naming the loop's mutable variables, over which annotations range. -/
  statePat : Term
  /-- The erased variables among the loop's mutable variables; annotations bind their `.out`
  projections over the state tuple. -/
  erasedMutVars : Array MutVar := #[]
  /-- Whether the body can `return`, so that the state tuple starts with the return slot. -/
  returnsEarly : Bool := false

/-- Bind the `.out` projection of each erased variable over `e`, so that an annotation names erased
variables at their underlying type. The `+zeta` substitutes the binding away at elaboration, so
annotation goals carry the projection inline like the compiled body does. -/
private meta def LoopApp.wrapErasedProjs (g : LoopApp) (e : Term) : DoElabM Term := do
  g.erasedMutVars.foldlM (init := e) fun e mv =>
    `(let +zeta $(mv.ident):ident := Erased.out $(⟨mv.ident.raw⟩); $e)

/-- Abstract `e` over the loop's mutable variables, so that `e` may name them. -/
private meta def LoopApp.mkStateFun (g : LoopApp) (e : Term) : DoElabM Term := do
  `(fun $(g.statePat) => $(← g.wrapErasedProjs e))

/-- Elaborate the gadget application `gadget args*` that replaces the loop. -/
private meta def LoopApp.mkCall (g : LoopApp) (gadget : Name) (args : Array Term) : DoElabM Expr := do
  -- Fix the assertion type up front. Left to unification, it can stay pending until an enclosing
  -- loop body abstracts over its binders, leaving an unreduced redex where `vcgen` expects `Prop`.
  let call ← match ← assertionTypes? (← read).monadInfo.m with
    | some info => `($(mkIdent gadget) (Pred := $(← Term.exprToSyntax info.pred)) $args*)
    | none => `($(mkIdent gadget) $args*)
  Term.elabTermEnsuringType call (mkApp (← read).monadInfo.m g.σ)

/--
Elaborate a Velvet loop whose body is `body`, following `Lean.Elab.Do.elabDoFor`: the body runs
over a tuple of the mutable variables it reassigns (plus the early-return slot), and `mkLoop` builds
the gadget application that iterates it. `binders` are the per-iteration binders that precede the
state tuple in the body: the element and its membership proof for `for`, a `Unit` for `while`.
-/
private meta def elabLoop (dec : DoElemCont) (body : TSyntax ``Lean.Parser.Term.doSeq)
    (binders : Array (Name × (Array Expr → DoElabM Expr)))
    (addBinderInfo : Array Expr → DoElabM Unit) (mkLoop : LoopApp → DoElabM Expr) :
    DoElabM Expr := do
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
    defs ← loopMutVars.foldlM (init := defs) fun defs x => do
      Term.addTermInfo' x.ident (← getFVarFromUserName x.getId)
      let v ← x.stateValue
      -- ForIn forces the mut tuple into the universe mi.u: that of the do block result type.
      -- See `Lean.Elab.Do.elabDoFor` for why this is a separate `isLevelDefEq` check.
      let u ← getDecLevel (← inferType v)
      discard <| isLevelDefEq u mi.u
      return defs.push v
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs

  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u

  let s ← mkFreshUserName `__s
  let body ←
    withLocalDeclsD binders fun xh => do
    addBinderInfo xh
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
    -- Elaborate the loop body, which must have result type `PUnit`, just like the whole loop.
    elabDoSeq body { dec with k := continueCont, kind := .duplicable }

  let forIn ← mkLoop
    { init := preS, body, σ, statePat := ← mkStatePat loopMutVars,
      erasedMutVars := loopMutVars.filter (·.erased), returnsEarly := info.returnsEarly }

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

@[doElem_control_info doForVelvet]
public meta def controlInfoDoForVelvet : ControlInfoHandler := fun stx => do
  let `(doElem| for $[$_h? : ]? $_pat in $_xs $[ invariant $[$_ns : ]? $_invs]* $[done_with $[$_hDone : ]? $_done]? do $body) := stx
    | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  return { reassigns := bodyInfo.reassigns, returnsEarly := bodyInfo.returnsEarly }

@[doElem_elab doForVelvet]
public meta def elabDoForVelvet : DoElab := fun stx dec => do
  let `(doElem| for $[$h? : ]? $pat in $xs $[ invariant $[$ns : ]? $invs]* $[done_with $[$hDone : ]? $done]? do $body) := stx
    | throwUnsupportedSyntax
  -- A loop without Velvet clauses is Lean's own `for`. The `doFor` quotation is Lean's parser, so
  -- the expansion does not come back here.
  if invs.isEmpty && done.isNone then
    let expanded ← `(doFor| for $[$h? : ]? $pat:term in $xs:term do $body)
    return ← Term.withMacroExpansion stx expanded <| withRef expanded <|
      elabDoElem ⟨expanded⟩ dec
  let invs ← liftMacroM <| invs.mapM specTermToTerm
  let done ← liftMacroM <| done.mapM specTermToTerm
  let dec ← dec.ensureUnitAt stx
  -- Expand `pat` into an `Ident` `x`, matching on it only when it is a proper pattern.
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
  -- The body always takes the membership proof, named `h_mem` unless the loop names it.
  let d ← mkFreshExprMVar (mkApp2 (mkConst ``Membership [uα, uρ]) α ρ) (userName := `d)
  let hName := (h?.map (·.getId)).getD `h_mem
  let binders : Array (Name × (Array Expr → DoElabM Expr)) := #[(x.getId, fun _ => pure α),
    (hName, fun x => pure (mkApp5 (mkConst ``Membership.mem [uα, uρ]) α ρ d xs x[0]!))]
  let addBinderInfo (xh : Array Expr) : DoElabM Unit := do
    Term.addLocalVarInfo x xh[0]!
    if let some h := h? then
      Term.addLocalVarInfo h xh[1]!
  elabLoop dec body binders addBinderInfo fun g => do
    let invs' ← liftMacroM <| mkAssertionList invs (clauseNames ns "invariant")
    let stateInvLam ← g.mkStateFun invs'
    let loopArgs := #[← Term.exprToSyntax xs, ← Term.exprToSyntax g.init, ← Term.exprToSyntax g.body]
    match ← classifyForLoopInvariants x.getId invs ns stateInvLam done hDone with
    | .pureState =>
      let gadget := if g.returnsEarly then ``Loop.Gadget.forLoopWithInvariantReturning
        else ``Loop.Gadget.forLoopWithInvariant
      g.mkCall gadget (loopArgs.push stateInvLam)
    | .invAndDone doneTerm doneName =>
      let done' ← liftMacroM <| mkAssertionList #[doneTerm] #[doneName]
      let pref := mkIdent `__pref
      let rest := mkIdent `__rest
      let invLam ← `(fun $pref:ident $x:ident $rest:ident => $(← g.mkStateFun invs'))
      let doneLam ← `(fun $pref:ident => $(← g.mkStateFun done'))
      let gadget := if g.returnsEarly then ``Loop.Gadget.forLoopWithInvariantAndDoneReturning
        else ``Loop.Gadget.forLoopWithInvariantAndDone
      g.mkCall gadget (loopArgs ++ #[invLam, doneLam])

@[doElem_control_info doWhileVelvet]
public meta def controlInfoDoWhileVelvet : ControlInfoHandler := fun stx => do
  let `(doElem| while $[$_hcond : ]? $_cond $[ invariant $[$_ns : ]? $_invs]* $[decreasing $[$_hm : ]? $_m]? $[done_with $[$_h_done : ]? $_d]? do $body) := stx
    | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  return { reassigns := bodyInfo.reassigns, returnsEarly := bodyInfo.returnsEarly }

@[doElem_elab doWhileVelvet]
public meta def elabDoWhileVelvet : DoElab := fun stx dec => do
  let `(doElem| while $[$hcond : ]? $cond $[ invariant $[$ns : ]? $invs]* $[decreasing $[$hm : ]? $m]? $[done_with $[$h_done : ]? $d]? do $body) := stx
    | throwUnsupportedSyntax
  let isPartial : Bool := match (← getOptions).get? `velvet.semantics.termination with
    | some (Lean.DataValue.ofString s) => s == "partial"
    | _ => false
  -- A loop without Velvet clauses is Lean's own `while`, which expands to `repeat`. Partial
  -- correctness keeps it, since its fixed-point loop is what makes the loop verifiable.
  if invs.isEmpty && m.isNone && d.isNone && isPartial == false then
    let ifElem ← match hcond with
      | some h => `(doElem| if $h:ident : $cond then $body else break)
      | none => `(doElem| if $cond then $body else break)
    let expanded ← `(doElem| repeat $ifElem:doElem)
    return ← Term.withMacroExpansion stx expanded <| withRef expanded <|
      elabDoElem ⟨expanded⟩ dec
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
  let binders : Array (Name × (Array Expr → DoElabM Expr)) :=
    #[(← mkFreshUserName `__u, fun _ => pure (Lean.mkConst ``Unit))]
  elabLoop dec loopBody binders (fun _ => pure ()) fun g => do
    let invNames := clauseNames ns "invariant"
    let invs' ← liftMacroM <| mkAssertionList invs invNames
    let invLam ← g.mkStateFun invs'
    let mut loopArgs := #[← Term.exprToSyntax g.init, ← Term.exprToSyntax g.body, invLam]
    -- Without `done_with`, every exit goes straight to the code after the loop. With it, every exit
    -- other than a `return` establishes the invariants and the `done_with` condition.
    if let some doneWith := d then
      let doneName := h_done.join.map (fun (id : Ident) => id.getId) |>.getD `h_done_with
      let exitedInvs ← liftMacroM <| mkAssertionList (invs.push doneWith) (invNames.push doneName)
      loopArgs := loopArgs.push (← `(some $(← g.mkStateFun exitedInvs)))
    else
      loopArgs := loopArgs.push (← `(none))
    let gadget := match m.isSome, g.returnsEarly with
      | false, false => ``Loop.Gadget.whileLoopPartial
      | false, true => ``Loop.Gadget.whileLoopPartialReturning
      | true, false => ``Loop.Gadget.whileLoopTotal
      | true, true => ``Loop.Gadget.whileLoopTotalReturning
    match m with
    | none =>
      if isPartial == false then
        throwError "`while` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness"
      g.mkCall gadget loopArgs
    | some m =>
      let measureName := hm.join.map (fun (id : Ident) => id.getId) |>.getD `termination
      let measureNameStr := Lean.Syntax.mkStrLit measureName.toString
      let measureNameTerm : TSyntax `term ← `(Lean.Name.mkSimple $measureNameStr)
      let measureStx ← liftMacroM <| Named.sourceRefTerm m.raw
      let measureTerm ← `(Named.Measure.mk $measureNameTerm $measureStx $m)
      g.mkCall gadget (loopArgs.push (← g.mkStateFun measureTerm))
