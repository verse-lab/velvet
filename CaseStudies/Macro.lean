import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Gen
import Loom.MonadAlgebras.NonDetT.Basic

open Lean Elab Command

macro "assert" t:term : term => `(assertGadget $t)

/--
Elaboration rule for the `decreasing` annotation. Here we will
  - Throw an error if the termination semantics is unspecified.
  - Throw an error if the decreasing annotation is missing in total correctness semantics.
  - Throw a warning if the decreasing annotation is present in partial correctness semantics.
-/
elab "decreasing" t:term : term => do
  let opts <- getOptions
  let semantics := opts.getString (defVal := "unspecified") `loom.semantics.termination
  if semantics = "unspecified" then
    throwError "First, you need to specify the termination semantics using `set_option loom.semantics.termination <partial/total>`"
  let decr <- `(decreasingGadget $t)
  let decrIsNone := match t with
    | `(none) => true
    | _ => false
  let errorsEnabled := opts.getBool (defVal := true) `loom.linter.errors
  let warningsEnabled := opts.getBool (defVal := true) `loom.linter.warnings
  if semantics = "total" && decrIsNone && errorsEnabled then
    throwError "Decreasing annotations are required in total correctness semantics
To turn off this error, use `set_option loom.linter.errors false`."
  if semantics = "partial" && !decrIsNone && warningsEnabled then
    logWarningAt (<- getRef) "Decreasing annotations are not checked in partial correctness semantics
To turn off this warning, use `set_option loom.linter.warnings false`."
  Term.elabTerm decr none

elab "invariants" invs:term : term => do
  let opts <- getOptions
  let invsIsEmpty := match invs with
    | `([]) => true
    | _ => false
  let warningsEnabled := opts.getBool (defVal := true) `loom.linter.warnings
  if invsIsEmpty && warningsEnabled then
    logWarningAt (<- getRef) "Invariant annotations are not specified, so the loop invariant is assumed to be just `True`.
To turn off this warning, use `set_option loom.linter.warnings false`."
  Term.elabTerm (<- `(invariantGadget $invs:term)) none


declare_syntax_cat doneWith
declare_syntax_cat decreasingTerm
declare_syntax_cat invariantClause
declare_syntax_cat invariantClauses
syntax "invariant" (str)? termBeforeDo linebreak : invariantClause
syntax "done_with" termBeforeDo : doneWith
syntax "decreasing" termBeforeDo : decreasingTerm
syntax (invariantClause linebreak)* : invariantClauses

syntax "let" term ":|" term : doElem
syntax "while" term
  (invariantClause)*
  (doneWith)?
  (decreasingTerm)?
  "do" doSeq : doElem
syntax "while_some" term ":|" termBeforeDo "do" doSeq : doElem
syntax "while_some" term ":|" term
  (invariantClause)+
  (doneWith)?
  "do" doSeq : doElem
syntax "for" ident "in" termBeforeInvariant
  (invariantClause)+
  "do" doSeq : doElem

macro_rules
  | `(doElem| let $x:term :| $t) => `(doElem| let $x:term <- pickSuchThat _ (fun $x => type_with_name_prefix `choice $t))

/-
### While loop elaboration rules

The general syntax for a while loop is:
```lean
while <condition>
  [invariant <invariant1>]
  [invariant <invariant2>]
  ...
  [done_with <termination_condition>]?
  [decreasing <measure>]?
do <body>
```
Unlike ordinary Lean's `while` loop, `Velvet` loops require at least one
invariant annotation. Invariant annotations are followed by an optional `done_with` statement.
In a nutshell, `done_with` is a condition that is true upon loop termination. Such condition is
usefull to specify when the loop contains `break` or `continue` statements. Which means that loop
might terminate without reaching the stated where the loop condition is false.
If unspecified, it is assumed to be the negation of the loop condition.

The optional `decreasing` annotation is used to specify a measure function that is used to prove termination.
This measure elaborates to a term of type `β → Option ℕ` where `β` is a record of the loop variables. We need
`Option ℕ` to incorporate the cases when the measure is not specified, which should be the case for partial
correctness semantics.
If `decreasing` is unspecified, measure is assumed to be `none`.
-/
/-- Helper to wrap an invariant with the appropriate name elaborator -/
def mkNamedInvariant (invName? : Option (TSyntax `str)) (inv : TSyntax `term) : MacroM (TSyntax `term) :=
  match invName? with
  | some name => `(with_custom_name `invariant $name $inv)
  | none => `(with_name_prefix `invariant $inv)

macro_rules
  | `(doElem| while $t do $seq:doSeq) => do
    let decr <- withRef (<- getRef) `(decreasing none)
    let invs <- withRef (<- getRef) `(invariants [])
    `(doElem|
      for _ in Lean.Loop.mk do
        $invs:term
        onDoneGadget (with_name_prefix `done ¬$t:term)
        $decr:term
        if $t then
          $seq:doSeq
        else break)
  | `(doElem| while $t
              $[invariant $[$invName:str]? $inv:term
              ]*
              $[done_with $inv_done]?
              $[decreasing $measure]?
              do $seq:doSeq) => do
      let namedInvs ← (invName.zip inv).mapM fun (n?, i) => mkNamedInvariant n? i
      let invs <- `(invariants [ $[$namedInvs:term],* ])
      let invd_some ← match inv_done with
      | some invd_some => withRef invd_some ``($invd_some)
      | none => ``(¬$t:term)
      match measure with
      | some measure_some =>
        let decr <- withRef measure_some `(decreasing type_with_name_prefix `decreasing $measure_some)
        `(doElem|
          for _ in Lean.Loop.mk do
            $invs:term
            onDoneGadget (with_name_prefix `done $invd_some:term)
            $decr:term
            if $t then
              $seq:doSeq
            else break)
      | none => do
        let decr <- withRef (<- getRef) `(decreasing none)
        `(doElem|
          for _ in Lean.Loop.mk do
            $invs:term
            onDoneGadget (with_name_prefix `done $invd_some:term)
            $decr:term
            if $t then
              $seq:doSeq
            else break)
  | `(doElem| while_some $x:ident :| $t do $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        while ∃ $x:ident, $t do
          let $x :| $t
          $[$seq:doElem]*)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"
  | `(doElem| while_some $x:ident :| $t
              $[invariant $[$invName:str]? $inv:term
              ]*
              $[done_with $inv_done]? do
                $seq:doSeq) => do
    let namedInvs ← (invName.zip inv).mapM fun (n?, i) => mkNamedInvariant n? i
    let invs <- `(invariants [ $[$namedInvs:term],* ])
    let invd_some ← match inv_done with
    | some invd_some => withRef invd_some ``($invd_some)
    | none => ``(¬$t:term)
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      let decr <- withRef (<- getRef) `(decreasing none)
      `(doElem|
        for _ in Lean.Loop.mk do
          $invs:term
          onDoneGadget (with_name_prefix `done $invd_some:term)
          $decr:term
          if ∃ $x:ident, $t then
            let $x :| $t
            $[$seq:doElem]*
          else break)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"
  | `(doElem| for $x:ident in $t
            $[invariant $[$invName:str]? $inv:term
            ]*
            do $seq:doSeq) => do
      let namedInvs ← (invName.zip inv).mapM fun (n?, i) => mkNamedInvariant n? i
      let invs <- `(invariants [ $[$namedInvs:term],* ])
      match seq with
      | `(doSeq| $[$seq:doElem]*)
      | `(doSeq| $[$seq:doElem;]*)
      | `(doSeq| { $[$seq:doElem]* }) =>
        `(doElem|
          for $x:ident in $t do
            $invs:term
            $[$seq:doElem]*)
      | _ => Lean.Macro.throwError "for expects a sequence of do-elements"
