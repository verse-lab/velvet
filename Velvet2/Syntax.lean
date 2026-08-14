import Velvet2.Specs
import Velvet2.Named
import Lean.Parser
import Lean.Elab.Command
import Std.Internal.Do
import Std.Internal.Do.WP.Basic
import Std.Internal.Do.WP.Lemmas
import Std.Internal.Do.Triple.Basic
import Std.Internal.Do.Triple.Gadget
import Std.Internal.Do.Triple.SpecLemmas

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do Named

public def makeNameArrayFromIdents (ids : Array (Option Ident)) (pref: String) : Array Name :=
  ids.mapIdx fun i e =>
    match e with
    | some id => id.getId
    | none => Name.mkSimple s!"{pref}{i+1}"

/-- Persisted direct statement of a generated `methodName.spec` contract. -/
structure MethodSpecEntry where
  name : Name
  statement : Syntax

private def addMethodSpecEntry (state : Std.HashMap Name Syntax) (entry : MethodSpecEntry) :=
  state.insert entry.name entry.statement

initialize methodSpecExt : SimplePersistentEnvExtension MethodSpecEntry (Std.HashMap Name Syntax) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addMethodSpecEntry
    addImportedFn := fun entries =>
      mkStateFromImportedEntries addMethodSpecEntry {} entries }

theorem triple_from_option_spec {α β : Type}
    {f : α → Option β} {a : α} {pre : Prop} {post : β → Prop}
    (h : ∀ (r : β), f a = some r → pre → post r) :
    Triple (f a) pre (fun r => post r) (True : Prop) := by
  apply Std.Internal.Do.Triple.intro
  intro hpre
  show (f a).elim True post
  cases hfa : f a with
  | none => trivial
  | some r => exact h r hfa hpre

theorem triple_to_option_spec {β : Type} {pre : Prop} {post : β → Prop}
    {x : Option β}
    (h : Triple x pre (fun r => post r) (True : Prop)) :
    ∀ r, x = some r → pre → post r := by
  intro r hx hpre
  rcases h with ⟨hwp⟩
  have hwp := hwp hpre
  subst hx
  exact hwp

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

syntax "method " ("rec ")? ident bracketedBinder* " returns " "(" ident " : " term ")" (" in " term)?
  (" requires " (atomic(ident " : "))? termBeforeDo)* (" signals " (atomic(ident " : "))? termBeforeDo)* 
  (" ensures " (atomic(ident " : "))? termBeforeDo)* " do " doSeq : command

syntax "assert" (atomic(ident " : ")) term : term

macro_rules
  | `(term| assert $nm:ident : $t:term) => do
    let nameStr := Lean.Syntax.mkStrLit nm.getId.toString
    let name : TSyntax `term ← `(Lean.Name.mkSimple $nameStr)
    let stx ← Named.sourceRefTerm t.raw
    `(_root_.assertGadget (Named.mk $name $stx $t))

set_option linter.unusedVariables false in
elab_rules : command
  | `(command|
      method $[rec%$recTk]? $name:ident $binders:bracketedBinder* returns ($retId:ident : $retType:term) $[in $monadStack:term]?
        $[requires $[$reqNs : ]? $req]* $[signals $[$sigNs : ]? $sig]*
        $[ensures $[$ensNs : ]? $ens]* do $body:doSeq) => do
    let (defCmd, specCmd, statement) ← Command.runTermElabM fun _vs => do
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
        let ensAtIdx := ensNs[idx]!
        ensNames := ensNames.push <| match ensNs[idx]! with
          | some id => id.getId
          | none => Name.mkSimple s!"ensures{idx + 1}"

      let mut sigNames : Array Name := #[]
      for idx in [:sigNs.size] do
        let sigNsAtIdx := sigNs[idx]!
        sigNames := sigNames.push <| match sigNs[idx]! with
          | some id => id.getId
          | none => Name.mkSimple s!"signals{idx + 1}"
      let pre ← liftMacroM <| mkAssertionList req reqNames
      let postBody ← liftMacroM <| mkAssertionList ens ensNames
      let sigs ← liftMacroM <| mkSignalsList sig sigNames
      let post ← `(fun $retId => $postBody)

      let monadStack' <-
          if monadStack.isSome then `($monadStack.get! $retType:term)
          else `(term|Option $retType:term)
      let defCmd ←
        if recTk.isSome then
          `(command|
            set_option linter.unusedVariables false in
            def $name $binders* : ($monadStack') := do $body
              partial_fixpoint)
        else
          `(command|
            set_option linter.unusedVariables false in
            def $name $binders* : ($monadStack') := do $body)
      let specId := mkIdentFrom name (name.getId ++ `spec)
      let statement ← `(term|
        ∀ $binders*, Std.Internal.Do.Triple
          ($name $ids*)
          $pre
          ($post)
          ($sigs))
      let specCmd ← `(command|
        set_option linter.unusedVariables false in
        def $specId := $statement)
      return (defCmd, specCmd, statement)
    elabCommand defCmd
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    let isRec ← liftCoreM <| isRecursiveDefinition declName
    match recTk, isRec with
    | some recStx, false =>
        logWarningAt recStx "unneeded `rec`; this method is not recursive, please remove it"
    | none, true =>
        throwErrorAt name "recursive method `{declName}` requires `rec`; write `method rec {name.getId} ...`"
    | _, _ => pure ()
    elabCommand specCmd
    let specName ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom name (name.getId ++ `spec))
    modifyEnv (methodSpecExt.addEntry · { name := specName, statement := statement })

syntax "prove_correct " ident " by " tacticSeq : command

/-- Prove a method contract such as `foo.spec`, producing the registered theorem
`foo.spec.proof`. The contract definition owns the complete quantified `Triple`; this command only
unfolds and proves that proposition. -/
@[incremental]
elab_rules : command
  | `(command| prove_correct $specId:ident by $proof:tacticSeq) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverload specId
    let info ← liftCoreM <| getConstInfo declName
    unless (← liftTermElabM <| whnf info.type).isProp do
      throwErrorAt specId "`{declName}` is not a proposition"
    let some statement := methodSpecExt.getState (← getEnv) |>.get? declName
      | throwErrorAt specId "no method contract metadata found for `{declName}`"
    let statement : Term := ⟨statement⟩
    let proofId := mkIdentFrom specId (specId.getId ++ `proof)
    let thmCmd ← `(command|
      open scoped Std.Internal.Do Lean.Order in
      set_option linter.unusedVariables false in
      @[spec] theorem $proofId : $statement :=
        show $specId from by
          unfold $specId
          ($proof))
    elabCommand thmCmd

macro_rules
  | `(doElem| for' $pat:term in $xs $[ invariant $[$ns : ]? $invs]* $[done_with $[$hDone : ]? $done]? do $body) => do
  let invs' ← mkAssertionList invs (makeNameArrayFromIdents ns "invariant")
  let doneTerm ← match done with
    | some done => pure done
    | none => `(True)
  let doneName := hDone.join.map (·.getId) |>.getD `h_done_with
  let done' ← mkAssertionList #[doneTerm] #[doneName]
  let pref := Lean.mkIdent `__pref
  let suff := Lean.mkIdent `__suff
  let cursorInv ← `(term|
    Velvet2.Spec.rangeInvariantValue (fun $pat => $invs') $done' $suff:ident)
  `(doElem| for $pat in $xs
    invariant $pref $suff => $cursorInv
    do $body)
  | `(doElem| while' $[$hcond : ]? $cond $[ invariant $[$ns : ]? $invs]* decreasing $[$hm : ]? $m $[done_with $[$h_done : ]? $d]? do $body) => do
  let defaultLoopIdent := mkIdent `h_loop
  let loopIdent := hcond.getD defaultLoopIdent
  let invNames := makeNameArrayFromIdents ns "invariant"
  let invs' ← mkAssertionList invs invNames
  let defaultDoneWith : TSyntax `term ← withRef cond do `(¬ $cond)
  let doneWith := d.getD defaultDoneWith
  let doneWithName := match h_done.join with
    | some id => id.getId
    | none => `h_done_with
  let exitedInvs ← mkAssertionList (invs.push doneWith) (invNames.push (doneWithName)) 
  let measureName := hm.map (·.getId) |>.getD `decreasing
  let measureNameStr := Lean.Syntax.mkStrLit measureName.toString
  let measureNameTerm : TSyntax `term ←
    `(Lean.Name.mkSimple $measureNameStr)
  let measureStx ← Named.sourceRefTerm m.raw
  let measureNamed : TSyntax `term ←
    `(Named.Measure.mk $measureNameTerm $measureStx $m)
  let exited := Lean.mkIdent `__exited
  `(doElem| while $loopIdent : $cond
    invariant $exited =>
      if $exited then $exitedInvs else $invs'
    decreasing $measureNamed
    do $body)
