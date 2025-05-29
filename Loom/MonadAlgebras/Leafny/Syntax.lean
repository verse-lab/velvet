import Lean
import Lean.Parser

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic

import Loom.MonadAlgebras.Leafny.Extension

open Lean Elab Command Term Meta Lean.Parser


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

syntax "leafny_def" ident leafny_binder* "return" "(" ident ":" term ")"
  (require_caluse )*
  (ensures_caluse)* "do" doSeq linebreak "correct_by" term : command

syntax (priority := high) ident noWs "[" term "]" ":=" term : doElem
syntax (priority := high) ident noWs "[" term "]" "+=" term : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := ($id:term).modify $idx (· + $val))
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := ($id:term).modify $idx (· + $val))

def toBracketedBinderArray (stx : Array (TSyntax `leafny_binder)) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let mut binders := #[]
  for b in stx do
    match b with
    | `(leafny_binder| ($id:ident : $tp:term)) => do
      let fb ← `(bracketedBinder| ($id : $tp:term))
      binders := binders.push fb
    | `(leafny_binder| (mut $id:ident : $tp:term)) => do
      let fb ← `(bracketedBinder| ($id : $tp:term))
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
      ids := ids.push id
    | `(leafny_binder| ($id:ident : $_:term)) => do
      ids := ids.push id
    | _ => throwError "unexpected syntax in leafny binder: {b}"
  return ids

mutual
partial def expandLeafnyDoSeq (modIds : Array Ident) (stx : doSeq) : TermElabM (Array doSeqItem) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => return Array.flatten $ ← doS.mapM (expandLeafnyDoSeqItem modIds)
  | _ => throwErrorAt stx s!"unexpected syntax of Leafny `do`-notation sequence {stx}"


partial def expandLeafnyDoSeqItem (modIds : Array Ident) (stx : doSeqItem) : TermElabM (Array doSeqItem) := do
  match stx with
  -- Ignore semicolons
  | `(Term.doSeqItem| $stx ;) => expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| $stx:doElem)
  | `(Term.doSeqItem| return) => expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| return ())
  | `(Term.doSeqItem| return $t) =>
    let mut ret <- `(term| ())
    for modId in modIds do
      ret <- `(term| ($modId, $ret))
    return #[<-`(Term.doSeqItem| return ($t, $ret))]
  | `(Term.doSeqItem| pure $t) =>
    let mut ret <- `(term| ())
    for modId in modIds do
      ret <- `(term| ($modId, $ret))
    return #[<-`(Term.doSeqItem| pure ($t, $ret))]
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandLeafnyDoSeq modIds thn
    let els <- expandLeafnyDoSeq modIds els
    let ret ← `(Term.doSeqItem| if $h:ident : $t then $thn* else $els*)
    return #[ret]
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn) =>
    expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| if $h:ident : $t:term then $thn else pure ())
  | `(Term.doSeqItem| if $t:term then $thn:doSeq) =>
    expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| if $t then $thn:doSeq else pure ())
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
    return #[<-`(Term.doSeqItem| let ⟨$id, _⟩ <- $trm:term)] ++ mods
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

def Array.andList (ts : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t := ts[0]!
    for t' in ts[1:] do
      t <- `(term| $t ∧ $t')
    return t

elab_rules : command
  | `(command|
  leafny_def $name:ident $binders:leafny_binder* return ( $retId:ident : $type:term )
  $[require $req:term]*
  $[ensures $ens:term]* do $doSeq:doSeq
  correct_by $proof:term) => do
  let (defCmd, thmCmd) ← Command.runTermElabM fun _vs => do
    let bindersIdents ← toBracketedBinderArray binders

    let modIds ← getModIds binders
    globalMutVarsCtx.modify (·.insert name.getId modIds)
    let modIds := modIds.map (·.2)
    let doSeq <- expandLeafnyDoSeq modIds doSeq

    let mut mods := #[]
    for modId in modIds do
      let modIdOld := mkIdent <| modId.getId.appendAfter "_old"
      let modOld <- `(Term.doSeqItem| let $modIdOld:ident := $modId:ident)
      let mod <- `(Term.doSeqItem| let mut $modId:ident := $modId:ident)
      mods := mods.push modOld |>.push mod
    let mutTypes ← getMutTypes binders
    let mut retType <- `(Unit)
    for mutType in mutTypes do
      retType <- `($mutType × $retType)
    let defCmd <- `(command|
      def $name $bindersIdents* : NonDetT DevM ($type × $retType) := do $mods* $doSeq*)
    let lemmaName := mkIdent <| name.getId.appendAfter "_lemma"

    let pre <- req.andList
    let post <- ens.andList

    let mut ret <- `(term| ())
    for modId in modIds do
      ret <- `(term| ($modId, $ret))

    let ids ← getIds binders
    let thmCmd <- `(command|
      lemma $lemmaName $bindersIdents* :
      $pre ->
      triple
        True
        ($name $ids*)
        (fun ⟨$retId, $ret⟩ => $post) := $proof)
    return (defCmd, thmCmd)
  elabCommand defCmd
  trace[Loom.debug] "{thmCmd}"
  elabCommand thmCmd


open PartialCorrectness DemonicChoice

leafny_def foo (mut x : ℕ) (mut y : ℕ) return (u : Unit)
  require x = y
  ensures x = y + 1
  ensures u = u do
  pure ()
  correct_by by sorry

#print foo_lemma

leafny_def bar (mut x : ℕ) (z : ℕ) : Unit :=
  x := x + z
  let mut y := x
  let u <- foo x y
  foo y x
  return u



@[spec, wpSimp]
def WPGen.pickSuchThat : WPGen (pickSuchThat τ p : NonDetT DevM τ) := by
  refine ⟨fun post => ∀ t, p t -> post t, True, ?_⟩
  intro post _; apply le_of_eq;
  simp [MonadNonDet.wp_pickSuchThat, logicSimp]

attribute [aesop safe cases] Decidable
attribute [-simp] if_true_left Bool.if_true_left ite_eq_left_iff
attribute [logicSimp] ite_self
attribute [aesop unsafe 20% apply] le_antisymm

@[simp]
lemma Array.replicate_get (n : ℕ) [Inhabited α] (a : α) (i : ℕ) (_ : i < n := by omega) :
  (Array.replicate n a)[i]! = a := by
  rw [getElem!_pos, Array.getElem_replicate]; aesop

@[simp]
lemma Array.modify_get (a : Array α) [Inhabited α] (i j : ℕ) (f : α -> α) :
  (a.modify i f)[j]! = if j < a.size then if j = i then f a[j]! else a[j]! else default := by
  by_cases h : j < a.size
  { (repeat rw [getElem!_pos]) <;> try solve | aesop
    rw [@getElem_modify]; aesop }
  repeat rw [getElem!_neg]
  all_goals (try split) <;> solve | omega | aesop

def Array.sumUpTo [Inhabited α] [AddCommMonoid β] (a : Array α) (f : ℕ -> α -> β) (bound : ℕ) : β :=
  ∑ i ∈ Finset.range bound, f i a[i]!

@[simp]
lemma Array.sumUpToSucc [Inhabited α] [AddCommMonoid α] (a : Array α) (f : ℕ -> α -> α) (bound : ℕ) :
  a.sumUpTo f (bound + 1) = a.sumUpTo f bound + f bound a[bound]! := by
  simp [sumUpTo]
  rw [@Finset.sum_range_succ]

variable [Inhabited α] [Ring α]
leafny_def spmv
  (mInd : Array (Array ℕ))
  (mVal : Array (Array α))
  (v : Array α) (mut out : Array α) return (u : Unit)
  require mInd.size = mVal.size
  require ∀ i < mInd.size, mInd[i]!.size = mVal[i]!.size
  require out.size = mVal.size
  require ∀ i : ℕ, out[i]! = 0
  ensures ∀ i < mInd.size, out[i]! = mVal[i]!.sumUpTo (fun j x => x * v[mInd[i]![j]!]!) mInd[i]!.size
  do
    let mut arrInd : Array ℕ := Array.replicate mInd.size 0
    while_some i :| i < arrInd.size ∧ arrInd[i]! < mInd[i]!.size
    invariant arrInd.size = mVal.size
    invariant out.size = mVal.size
    invariant ∀ i < arrInd.size, arrInd[i]! <= (mInd[i]!).size
    invariant ∀ i < arrInd.size, out[i]! = mVal[i]!.sumUpTo (fun j x => x * v[mInd[i]![j]!]!) arrInd[i]!
    done_with ∀ i < arrInd.size, arrInd[i]! = mInd[i]!.size do
      let ind := arrInd[i]!
      let vInd := mInd[i]![ind]!
      let mVal := mVal[i]![ind]!
      let val := mVal * v[vInd]!
      out[i] += val
      arrInd[i] += 1
    return ()
  correct_by by
    simp; intros; dsimp [spmv]
    mwp
    { intros; mwp; aesop }
    aesop

#print spmv_lemma
