import Lean
import Lean.Parser

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic

import CaseStudies.Theory
import CaseStudies.Velvet.VelvetTheory
import CaseStudies.Tactic
import CaseStudies.TestingUtil
import Loom.MonadAlgebras.WP.DoNames'

open Lean Elab Command Term Meta Lean.Parser

private def _root_.Lean.EnvExtension.set (ext : EnvExtension σ) (s : σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

private def _root_.Lean.EnvExtension.modify (ext : EnvExtension σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

private def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.modify
  (ext : SimplePersistentEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

abbrev doSeq := TSyntax ``Term.doSeq
abbrev doSeqItem := TSyntax ``Term.doSeqItem

declare_syntax_cat require_caluse
declare_syntax_cat ensures_caluse
declare_syntax_cat leafny_binder

def termBeforeReqEnsDo := withForbidden "require" (withForbidden "ensures" Term.termBeforeDo)

attribute [run_builtin_parser_attribute_hooks] termBeforeReqEnsDo

builtin_initialize
  register_parser_alias termBeforeReqEnsDo


syntax "(" ident ":" term ")" : leafny_binder
syntax "(mut" ident ":" term ")" : leafny_binder
syntax "require" termBeforeReqEnsDo : require_caluse
syntax "ensures" termBeforeReqEnsDo : ensures_caluse

syntax "method" ident leafny_binder* "return" "(" ident ":" term ")"
  (require_caluse )*
  (ensures_caluse)* "do" doSeq
  Termination.suffix : command

declare_syntax_cat prove_correct_command
syntax "prove_correct" : prove_correct_command
syntax "prove_correct?" : prove_correct_command

syntax prove_correct_command ident Termination.suffix "by" tacticSeq : command

syntax (priority := high) ident noWs "[" term "]" ":=" term : doElem
syntax (priority := high) ident noWs "[" term "]" "+=" term : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := ($id:term).modify $idx (fun _ => $val))
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := ($id:term).modify $idx (· + $val))

private def toBracketedBinderArrayLeafny (stx : Array (TSyntax `leafny_binder)) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let mut binders := #[]
  for b in stx do
    match b with
    | `(leafny_binder| ($id:ident : $tp:term)) => do
      let fb ← `(bracketedBinder| ($id : $tp:term))
      binders := binders.push fb
    | `(leafny_binder| (mut $id:ident : $tp:term)) => do
      let idOld := mkIdent <| id.getId.appendAfter "Old"
      let fb ← `(bracketedBinder| ($idOld : $tp:term))
      binders := binders.push fb
    | _ => throwError "unexpected syntax in leafny binder: {b}"
  return binders

def getMutTypes (stx : Array (TSyntax `leafny_binder)) : MetaM (Array (TSyntax `term)) := do
  let mut types := #[]
  for b in stx do
    match b with
    | `(leafny_binder| (mut $_:ident : $tp:term)) => do
      types := types.push tp
    | _ => pure ()
  return types

def getModIds (stx : Array (TSyntax `leafny_binder)) : MetaM (Array (Nat × Ident)) := do
  let mut ids := #[]
  let mut pos := 0
  for b in stx do
    match b with
    | `(leafny_binder| (mut $id:ident : $_:term)) => do
      ids := ids.push (pos, id)
      pos := pos + 1
    | _ => pos := pos + 1
  return ids

def getIds (stx : Array (TSyntax `leafny_binder)) : MetaM (Array Ident) := do
  let mut ids := #[]
  for b in stx do
    match b with
    | `(leafny_binder| (mut $id:ident : $_:term)) => do
      let idOld := mkIdent <| id.getId.appendAfter "Old"
      ids := ids.push idOld
    | `(leafny_binder| ($id:ident : $_:term)) => do
      ids := ids.push id
    | _ => throwError "unexpected syntax in leafny binder: {b}"
  return ids

abbrev doMatchAltExpr := Term.matchAlt (rhsParser := Term.doSeq)

mutual
partial def expandLeafnyDoSeq (modIds : Array Ident) (stx : doSeq) : TermElabM (Array doSeqItem) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => return Array.flatten $ ← doS.mapM (expandLeafnyDoSeqItem modIds)
  | _ => throwErrorAt stx s!"unexpected syntax of Velvet `do`-notation sequence {stx}"


partial def expandLeafnyDoSeqItem (modIds : Array Ident) (stx : doSeqItem) : TermElabM (Array doSeqItem) := do
  match stx with
  -- Ignore semicolons
  | `(Term.doSeqItem| $stx ;) => expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| $stx:doElem)
  | `(Term.doSeqItem| return) => expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| return ())
  | `(Term.doSeqItem| return $t) =>
    let ret <-
      if modIds.size = 0 then
      `(term| $t)
     else
       `(term| ($t, $[$modIds:term],*))
    return #[<-`(Term.doSeqItem| return $ret)]
  | `(Term.doSeqItem| pure $t) =>
    let ret <-
      if modIds.size = 0 then
      `(term| $t)
     else
       `(term| ($t, $[$modIds:term],*))
    return #[<-`(Term.doSeqItem| pure $ret)]
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandLeafnyDoSeq modIds thn
    let els <- expandLeafnyDoSeq modIds els
    let ret ← `(Term.doSeqItem| if $h:ident : $t then $thn* else $els*)
    return #[ret]
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn) =>
    expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| if $h:ident : $t:term then $thn else pure ())
  | `(Term.doSeqItem| if $t:term then $thn:doSeq) =>
    expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| if $t then $thn:doSeq else pure ())
  | `(Term.doSeqItem| match $discrs:matchDiscr,* with $[$alts:matchAlt]*) =>
    let alts' ← alts.mapM fun (alt : TSyntax _) => do
      match alt with
      | `(doMatchAltExpr| | $a,* => $rhs:doSeq) =>
        let rhs' ← expandLeafnyDoSeq modIds rhs
        let alt' ← `(doMatchAltExpr| | $a,* => $rhs'*)
        pure ⟨alt'.raw⟩
      | _ =>
        pure alt
    let ret ← `(Term.doSeqItem| match $discrs:matchDiscr,* with $[$alts':matchAlt]*)
    return #[ret]
  | `(Term.doSeqItem| if $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandLeafnyDoSeq modIds thn
    let els <- expandLeafnyDoSeq modIds els
    let ret ← `(Term.doSeqItem| if $t then $thn* else $els*)
    return #[ret]
  | `(Term.doSeqItem| let $id <- $trm:term) | `(Term.doSeqItem| let $id : $_ <- $trm:term) =>
    let `($t:ident $args:term*) := trm | pure #[stx]
    -- dbg_trace s!"{t} {args}"
    let ctx <- globalMutVarsCtx.get
    let .some ids := ctx[t.getId]? | pure #[stx]
    let mut mods := #[]
    let mut modArgs := #[]
    for (pos, a) in ids do
      let .some arg := args[pos]? | throwErrorAt stx s!"{t} is not fully applied"
      -- dbg_trace s!"{arg}"
      let argName := arg.raw.getId
      if argName.isAnonymous then throwErrorAt arg s!"mutable argument {arg} is not a name"
      if argName ∈ modArgs then throwErrorAt arg s!"mutable arguments cannot alias"
      modArgs := modArgs.push argName
      mods := mods.push $ <- withRef arg `(Term.doSeqItem| $(mkIdent argName):ident := $a:ident)
    return #[<-`(Term.doSeqItem| let $id <- $trm:term)] ++ mods
  | `(Term.doSeqItem| $trm:term) =>
    let id := mkIdent <| <- mkFreshUserName `ret
    let `($t:ident $args:term*) := trm | pure #[stx]
    -- dbg_trace s!"{t} {args}"
    let ctx <- globalMutVarsCtx.get
    let .some ids := ctx[t.getId]? | pure #[stx]
    let mut mods := #[]
    let mut modArgs := #[]
    for (pos, a) in ids do
      let .some arg := args[pos]? | throwErrorAt stx s!"{t} is not fully applied"
      -- dbg_trace s!"{arg}"
      let argName := arg.raw.getId
      if argName.isAnonymous then throwErrorAt arg s!"mutable argument {arg} is not a name"
      if argName ∈ modArgs then throwErrorAt arg s!"mutable arguments cannot alias"
      modArgs := modArgs.push argName
      mods := mods.push $ <- withRef arg `(Term.doSeqItem| $(mkIdent argName):ident := $a:ident)
    let ret <- withRef trm `(Term.doSeqItem| pure $id)
    return #[<- withRef trm `(Term.doSeqItem| let ⟨$id, _⟩ <- $trm:term)] ++ mods.push ret
  | `(Term.doSeqItem| while_some $id :| $p:term $invs* $done do $doSeq:doSeq) =>
    let doSeq <- expandLeafnyDoSeq modIds doSeq
    return #[<-`(Term.doSeqItem| while_some $id :| $p:term $invs* $done do $doSeq*)]
  | stx => pure #[stx]
end

private def Array.andListWithName (ts : Array (TSyntax `term)) (name_prefix : TSyntax `name) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t <- `(term| with_name_prefix $name_prefix:name $(ts[0]!))
    for t' in ts[1:] do
      t <- `(term| (with_name_prefix $name_prefix:name $t') ∧ $t)
    return t

private def Array.andList (ts : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t := ts[0]!
    for t' in ts[1:] do
      t <- `(term| $t' ∧ $t)
    return t

private def addPreludeToPreCond (pre : Term) (modIds : Array Ident) : CoreM (TSyntax `term) := do
  let mut pre := pre
  for modId in modIds do
    let modIdOld := mkIdent <| modId.getId.appendAfter "Old"
    pre ← `(term| let $modId:ident := $modIdOld:ident; $pre)
  pure pre

elab_rules : command
  | `(command|
  method $name:ident $binders:leafny_binder* return ( $retId:ident : $type:term )
  $[require $req:term]*
  $[ensures $ens:term]* do $doSeq:doSeq
  $suf:suffix
  ) => do
  let (defCmd, obligation, testingCtx) ← Command.runTermElabM fun _vs => do
    let bindersIdents ← toBracketedBinderArrayLeafny binders

    let modIds ← getModIds binders
    globalMutVarsCtx.modify (·.insert name.getId modIds)
    let modIds := modIds.map (·.2)
    let doSeq <- expandLeafnyDoSeq modIds doSeq

    let mut mods := #[]
    for modId in modIds do
      let modIdOld := mkIdent <| modId.getId.appendAfter "Old"
      -- let modOld <- `(Term.doSeqItem| let $modIdOld:ident := $modId:ident)
      let mod <- `(Term.doSeqItem| let mut $modId:ident := $modIdOld:ident)
      mods := mods.push mod
    let mutTypes ← getMutTypes binders
    let mut retType : Term <- `($type)
    if mutTypes.size != 0 then
      let lastMutType := mutTypes[mutTypes.size - 1]!
      let mutTypes := mutTypes.pop.reverse
      let mut mutTypeProd := lastMutType
      for mutType in mutTypes do
        mutTypeProd <- `($mutType × $mutTypeProd)
      retType <- `($retType × $mutTypeProd)
    /- We need Velvet methods to be elaborated in a modified `do`-notation.
      For that we localy open the `DoNames` namespace which contains the extensioned `do`-notation. -/
    let defCmd <- `(command|
      open Lean.Elab.Term.DoNames in
      set_option linter.unusedVariables false in
      def $name $bindersIdents* : VelvetM $retType:term := do $mods* $doSeq*
      $suf:suffix)
    -- let lemmaName := mkIdent <| name.getId.appendAfter "_correct"

    let reqName <- `(name| `require)
    let ensName <- `(name| `ensures)
    let pre <- req.andListWithName reqName
    let post <- ens.andListWithName ensName

    let namelessPre <- req.andList
    let namelessPre <- addPreludeToPreCond namelessPre modIds
    let namelessPost <- ens.andList

    let ret <- if modIds.size = 0 then
      `(term| $retId)
    else
      `(term| ($retId, $[$modIds:term],*))

    let ids ← getIds binders
    let obligation : VelvetObligation := {
      binderIdents := bindersIdents
      ids := ids
      retId := retId
      ret := ret
      pre := pre
      post := post
      modIds := modIds
    }
    let modBinders ← modIds.zip mutTypes |>.mapM fun (mId, mutType) =>
      `(bracketedBinder| ($mId : $mutType))
    return (defCmd, obligation, { obligation with pre := namelessPre , post := namelessPost , modBinders , retType := type })
  elabCommand defCmd
  velvetObligations.modify (·.insert name.getId obligation)
  velvetTestingContextMap.modify (·.insert name.getId testingCtx)

notation "{" P "}" c "{" v "," Q "}" => triple P c (fun v => Q)
/-
example:
open TotalCorrectness DemonicChoice
lemma triple_test (arr: arrInt) :
  {True}(insertionSort_part arr){b, 0 ≤ size b.snd.fst} := by
  sorry
-/

@[incremental]
elab_rules : command
  | `(command| $pv:prove_correct_command $name:ident $suf:suffix by%$tkp $proof:tacticSeq) => do
    let ctx <- velvetObligations.get
    let .some obligation := ctx[name.getId]? | throwError "no obligation found"
    let bindersIdents := obligation.binderIdents
    let ids := obligation.ids
    -- let retId := obligation.retId
    let ret := obligation.ret
    let pre ← liftCoreM <| addPreludeToPreCond obligation.pre obligation.modIds
    let post := obligation.post
    let lemmaName := mkIdent <| name.getId.appendAfter "_correct"
    let triple <- `($(mkIdent ``triple))
    let proofSeq ← withRef tkp `(tacticSeq|
      unfold $name
      ($proof))
    let thmCmd <- withRef tkp `(command|
      @[$(mkIdent `loomSpec):ident]
      lemma $lemmaName $bindersIdents* :
      $triple
        $pre
        ($name $ids*)
        (fun $ret => $post) := by $proofSeq $suf:suffix)
    let opts <- getOptions

    /- We need to check the termination and choice semantics options before
      stating the proof. -/
    if opts.getString (defVal := "unspecified") `loom.semantics.choice = "unspecified" then
      throwError "First, you need to specify the choice semantics using `set_option loom.semantics.choice <demonic/angelic>`"

    if opts.getString (defVal := "unspecified") `loom.semantics.termination = "unspecified" then
      throwError "First, you need to specify the termination semantics using `set_option loom.semantics.termination <partial/total>`"
    trace[Loom] "{thmCmd}"
    match pv with
    | `(prove_correct_command| prove_correct) =>
      Command.elabCommand thmCmd
    | `(prove_correct_command| prove_correct?) =>
      Command.liftTermElabM do
        Tactic.TryThis.addSuggestion (<-getRef) thmCmd
    | _ => throwError "unexpected proof command: {pv}"
    velvetObligations.modify (·.erase name.getId)

set_option linter.unusedVariables false in
def atomicAssertion {α : Type u} (n : Name) (a : α) := a

syntax "extract_program_for" ident : command
syntax "prove_precondition_decidable_for" ident ("by" tacticSeq)? : command
syntax "prove_postcondition_decidable_for" ident ("by" tacticSeq)? : command
syntax "derive_tester_for" ident : command

def obtainVelvetTestingCtx (nameRaw : Ident) : CommandElabM (VelvetTestingCtx × Name) := do
  let ctxMap ← velvetTestingContextMap.get
  let name := nameRaw.getId
  unless ctxMap.contains name do
    throwError "{name} is not a Velvet program"
  return (ctxMap[name]!, name)

elab_rules : command
  | `(command| extract_program_for $nameRaw:ident ) => do
  -- assuming the thing is computable, then extract the program first
  let (ctx, name) ← obtainVelvetTestingCtx nameRaw
  let bindersIdents := ctx.binderIdents
  let ids := ctx.ids
  let execName := name.appendAfter "Exec"
  let execDefCmd ← `(command|
    def $(mkIdent execName) $bindersIdents* :=
      $(mkIdent ``NonDetT.run) ($nameRaw $ids*))
  elabCommand execDefCmd

def elabDefiningDecidableInstancesForVelvetSpec (nameRaw : Ident)
    (pre? : Bool) (tk : Option Syntax) (tac : Option (TSyntax `Lean.Parser.Tactic.tacticSeq)) : CommandElabM Unit := do
  let (ctx, name) ← obtainVelvetTestingCtx nameRaw
  let bindersIdents := ctx.binderIdents
  let (target, suffix, binders) :=
    if pre?
    then (ctx.pre, "PreDecidable", bindersIdents)
    else (ctx.post, "PostDecidable", bindersIdents ++ ctx.modBinders |>.push ⟨mkExplicitBinder ctx.retId ctx.retType⟩)
  let decidableInstName := name.appendAfter suffix
  -- let proof := tac.getD (← `(term| (by infer_instance) ))
  let tac := tac.getD (← `(Lean.Parser.Tactic.tacticSeq| skip ))
  let proof ← (tk.elim id withRef) `(Lean.Parser.Tactic.tacticSeq|
    repeat' refine @instDecidableAnd _ _ ?_ ?_
    all_goals (try (infer_aux_decidable_instance ; infer_instance))
    ($tac) )
  let decidableInstDefCmd ← `(command|
    def $(mkIdent decidableInstName) $binders* :
      $(mkIdent ``Decidable) ($target) := by $proof)
  elabCommand decidableInstDefCmd

elab_rules : command
  | `(command| prove_precondition_decidable_for $nameRaw:ident ) => do
    elabDefiningDecidableInstancesForVelvetSpec nameRaw true none none
  | `(command| prove_precondition_decidable_for $nameRaw:ident by%$tk $tac) => do
    elabDefiningDecidableInstancesForVelvetSpec nameRaw true (some tk) (some tac)
  | `(command| prove_postcondition_decidable_for $nameRaw:ident ) => do
    elabDefiningDecidableInstancesForVelvetSpec nameRaw false none none
  | `(command| prove_postcondition_decidable_for $nameRaw:ident by%$tk $tac) => do
    elabDefiningDecidableInstancesForVelvetSpec nameRaw false (some tk) (some tac)

elab_rules : command
  | `(command| derive_tester_for $nameRaw:ident ) => do
  let (ctx, name) ← obtainVelvetTestingCtx nameRaw
  let execName ← do
    try resolveGlobalConstNoOverloadCore <| name.appendAfter "Exec"
    catch _ =>
      throwError "no executable found for {name}, please extract the program first"
  let ids := ctx.ids
  let retId := ctx.retId
  let ret := ctx.ret
  let bindersIdents := ctx.binderIdents
  let bundle (pre? : Bool) := if pre?
    then (ctx.pre, name.appendAfter "PreDecidable", ids)
    else (ctx.post, name.appendAfter "PostDecidable", ids ++ ctx.modIds |>.push retId)
  let decideTerm bundled : CommandElabM (TSyntax `term) := do
    let (target, instname, args) := bundled
    try
      let instname ← resolveGlobalConstNoOverloadCore instname
      `(term| (@$(mkIdent ``decide) _ ($(Syntax.mkApp (mkIdent instname) args))))
    catch _ =>
      `(term| ($(mkIdent ``decide) ($target)))
  let matcherTerm ← `(term|
      match ($(Syntax.mkApp (mkIdent execName) ids)) with
      | $(mkIdent ``DivM.res) $ret => $(← decideTerm <| bundle false)
      | _ => false)
  let ifTerm ← `(term| if $(← decideTerm <| bundle true) then $matcherTerm else true)
  let testerName := name.appendAfter "Tester"
  let testerDefCmd ← `(command|
    def $(mkIdent testerName) $bindersIdents* : Bool := $ifTerm)
  elabCommand testerDefCmd
