import Lean
import Velvet2.Specs
import Velvet2.Named
import Lean.Parser
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.WP.Lemmas
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.Gadget
import Std.Internal.Do.Triple.SpecLemmas

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do Named

/-! ## Small local compatibility layer -/

abbrev Triple {α : Type} (pre : Prop) (x : Option α) (post : α → Prop) (epost : Prop) : Prop :=
  Std.Internal.Do.Triple x pre post epost

public def optionalIdentNames (ids : Array (Option Ident)) : Array (Option Name) :=
  ids.map fun
    | some id => some id.getId
    | none => none

public def explicitNames (names : Array Name) : Array (Option Name) :=
  names.map some

theorem triple_from_option_spec {α β : Type}
    {f : α → Option β} {a : α} {pre : Prop} {post : β → Prop}
    (h : ∀ (r : β), f a = some r → pre → post r) :
    Triple pre (f a) (fun r => post r) (True : Prop) := by
  change Std.Internal.Do.Triple (f a) pre (fun r => post r) (True : Prop)
  apply Std.Internal.Do.Triple.intro
  intro hpre
  show (f a).elim True post
  cases hfa : f a with
  | none => trivial
  | some r => exact h r hfa hpre

theorem triple_to_option_spec {β : Type} {pre : Prop} {post : β → Prop}
    {x : Option β}
    (h : Triple pre x (fun r => post r) (True : Prop)) :
    ∀ r, x = some r → pre → post r := by
  intro r hx hpre
  change Std.Internal.Do.Triple x pre (fun r => post r) (True : Prop) at h
  rcases h with ⟨hwp⟩
  have hwp := hwp hpre
  subst hx
  exact hwp

/-! ## Environment extension for method obligations -/

structure Obligations where
  binderIdents : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  ids          : Array Ident
  retId        : Ident
  pre          : TSyntax `term
  post         : TSyntax `term
  isFixpoint   : Bool := false

initialize obligations : EnvExtension (Std.HashMap Name Obligations) ←
  registerEnvExtension (pure {})

private def _root_.Lean.EnvExtension.modify' [Inhabited σ] (ext : EnvExtension σ)
    [MonadEnv m] (f : σ → σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · f)

private def _root_.Lean.EnvExtension.get' [Inhabited σ] (ext : EnvExtension σ)
    [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (← getEnv)

syntax "while' " (atomic(ident " : "))? termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  " decreasing " (atomic(ident " : ")? termBeforeDo )
  (" done_with " (atomic(ident " : ")? termBeforeDo  ("by " tacticSeq)?))?
  " do " doSeq : doElem

/--
A finite range loop with inline state invariants. Like Lean's built-in `for`,
the collection controls termination; the initial version supports one binder
and one collection, including closed-open ranges such as `start...stop`.
-/
syntax "for' " term " in " termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  (" done_with " (atomic(ident " : "))? termBeforeDo)?
  " do " doSeq : doElem

syntax "method " ("rec ")? ident bracketedBinder* " returns " "(" ident " : " term ")"
  (" requires " (atomic(ident " : "))? termBeforeDo)*
  (" ensures " (atomic(ident " : "))? termBeforeDo)* " do " doSeq : command

syntax "assert" (atomic(ident " : ")) term : term

macro_rules
  | `(term| assert $nm:ident : $t:term) => do
    let nameStr := Lean.Syntax.mkStrLit nm.getId.toString
    let name : TSyntax `term ← `(Lean.Name.mkSimple $nameStr)
    let text := t.raw.reprint.getD (toString t.raw.formatStx)
    let textStr := Lean.Syntax.mkStrLit text
    let stx : TSyntax `term ←
      `(some (Lean.Syntax.atom Lean.SourceInfo.none $textStr))
    `(_root_.assertGadget (Named.mk $name $stx $t))

set_option linter.unusedVariables false in
elab_rules : command
  | `(command|
      method $[rec%$recTk]? $name:ident $binders:bracketedBinder* returns ($retId:ident : $retType:term)
        $[requires $[$reqNs : ]? $req]*
        $[ensures $[$ensNs : ]? $ens]* do $body:doSeq) => do
    let (defCmd, obligation) ← Command.runTermElabM fun _vs => do
      let mut ids : Array Ident := #[]
      for b in binders do
        match b with
        | `(bracketedBinder| ($id:ident : $_:term)) => ids := ids.push id
        | `(bracketedBinder| {$id:ident : $_:term}) => ids := ids.push id
        | _ => throwErrorAt b "unexpected binder syntax"
      let mut reqNames : Array Name := #[]
      for idx in [:reqNs.size] do
        reqNames := reqNames.push <| match reqNs[idx]! with
          | some id => id.getId
          | none => Name.mkSimple s!"requires{idx + 1}"
      let mut ensNames : Array Name := #[]
      for idx in [:ensNs.size] do
        ensNames := ensNames.push <| match ensNs[idx]! with
          | some id => id.getId
          | none => Name.mkSimple s!"ensures{idx + 1}"
      let pre ← liftMacroM <| mkPropList req (explicitNames reqNames) "requires"
      let post ← liftMacroM <| mkPropList ens (explicitNames ensNames) "ensures"
      let defCmd ←
        if recTk.isSome then
          `(command|
            set_option linter.unusedVariables false in
            def $name $binders* : Option $retType:term := do $body
              partial_fixpoint)
        else
          `(command|
            set_option linter.unusedVariables false in
            def $name $binders* : Option $retType:term := do $body)
      let obligation : Obligations := {
        binderIdents := binders
        ids := ids
        retId := retId
        pre := pre
        post := post
      }
      return (defCmd, obligation)
    elabCommand defCmd
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    let isRec ← liftCoreM <| isRecursiveDefinition declName
    match recTk, isRec with
    | some recStx, false =>
        logWarningAt recStx "unneeded `rec`; this method is not recursive, please remove it"
    | none, true =>
        throwErrorAt name "recursive method `{declName}` requires `rec`; write `method rec {name.getId} ...`"
    | _, _ => pure ()
    obligations.modify' (·.insert declName { obligation with isFixpoint := isRec })

syntax "prove_correct " ident " by " tacticSeq : command

private def mkProveCorrectThm (name : Ident) (obligation : Obligations)
    (proof : TSyntax ``Lean.Parser.Tactic.tacticSeq) : CommandElabM (TSyntax `command) := do
  let binders := obligation.binderIdents
  let ids := obligation.ids
  let retId := obligation.retId
  let pre := obligation.pre
  let post := obligation.post
  let lemmaName := mkIdent <| name.getId.appendAfter "_correct"
  let tripleId := mkIdent ``_root_.Triple
  if obligation.isFixpoint then
    let tripleFromPC := mkIdent ``triple_from_option_spec
    let tripleToPC := mkIdent ``triple_to_option_spec
    let pcName := mkIdent <| name.getId ++ `partial_correctness
    let ihName := mkIdent <| name.getId.appendAfter "_ih"
    let ihRawName := mkIdent <| Name.mkSimple s!"ih_{name.getId}_raw"
    let ihTripleName := mkIdent <| Name.mkSimple s!"ih_{name.getId}"
    let ihConversion ← `(fun $ids* => $tripleFromPC ($ihRawName $ids*))
    `(
      command|
      set_option linter.unusedVariables false in
      @[spec]
      theorem $lemmaName $binders* :
        $tripleId
          $pre
          ($name $ids*)
          (fun $retId => $post)
          (True : Prop) := by
        apply $tripleFromPC
        apply $pcName
        intro $ihName $ihRawName
        have $ihTripleName := $ihConversion
        intro $ids*
        exact $tripleToPC (by
          ($proof)))
  else
    `(
      command|
      set_option linter.unusedVariables false in
      @[spec]
      theorem $lemmaName $binders* :
        $tripleId
          $pre
          ($name $ids*)
          (fun $retId => $post)
          (True : Prop) := by
        simp only [$name:ident]
        ($proof))

@[incremental]
elab_rules : command
  | `(command| prove_correct $name:ident by $proof:tacticSeq) => do
    let ctx ← obligations.get'
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    let .some obligation := ctx[declName]?
      | throwError "no obligation found for `{name.getId}`. Did you define it with `method`?"
    let thmCmd ← mkProveCorrectThm name obligation proof
    elabCommand thmCmd
    obligations.modify' (·.erase declName)

macro_rules
  | `(doElem| for' $pat:term in $xs $[ invariant $[$ns : ]? $invs]* $[done_with $[$hDone : ]? $done]? do $body) => do
  let invs' ← mkPropList invs (optionalIdentNames ns) "invariant"
  let doneTerm ← match done with
    | some done => pure done
    | none => `(True)
  let doneName := hDone.join.map (·.getId) |>.getD `h_done_with
  let done' ← mkPropList #[doneTerm] #[some doneName] "done_with"
  `(doElem| for $pat in $xs do
    invariantGadget $invs'
    onDoneGadget $done'
    do $body)
  | `(doElem| while' $[$hcond : ]? $cond $[ invariant $[$ns : ]? $invs]* decreasing $[$hm : ]? $m $[done_with $[$h_done : ]? $d]? do $body) => do
  let defaultLoopIdent := mkIdent `h_loop
  let loopIdent := hcond.getD defaultLoopIdent
  let invs' ← mkPropList invs (optionalIdentNames ns) "invariant"
  let defaultDoneWith : TSyntax `term ← withRef cond do `(¬ $cond)
  let doneWith := d.getD defaultDoneWith
  let doneWithName := match h_done.join with
    | some id => id.getId
    | none => `h_done_with
  let doneWithNamed ← mkPropList #[doneWith] #[some doneWithName] "done_with"
  let measureName := hm.map (·.getId) |>.getD `decreasing
  let measureNameStr := Lean.Syntax.mkStrLit measureName.toString
  let measureNameTerm : TSyntax `term ←
    `(Lean.Name.mkSimple $measureNameStr)
  let measureText := m.raw.reprint.getD (toString m.raw.formatStx)
  let measureTextStr := Lean.Syntax.mkStrLit measureText
  let measureStx : TSyntax `term ←
    `(some (Lean.Syntax.atom Lean.SourceInfo.none $measureTextStr))
  let measureNamed : TSyntax `term ←
    `(Named.Measure.mk $measureNameTerm $measureStx $m)
  `(doElem| repeat do
    invariantGadget $invs'
    decreasingGadget $measureNamed
    onDoneGadget $doneWithNamed
    if $loopIdent : $cond then $body else break)
