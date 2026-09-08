module

public import Velvet.Core.NonDet.Defs

open Lean

@[expose] public section

/-- Extract a meaningful identifier name from a choice binder syntax,
falling back to `"choice"` if no identifier is found. -/
public meta partial def extractChoiceName (stx : Lean.Syntax) : Lean.Name :=
  match stx with
  | Lean.Syntax.ident _ _ val _ => val.eraseMacroScopes
  | Lean.Syntax.node _ ``Lean.Parser.Term.typeAscription args =>
      if h : 1 < args.size then
        match args[1] with
        | Lean.Syntax.ident _ _ val _ => val.eraseMacroScopes
        | other => extractChoiceName other
      else `choice
  | Lean.Syntax.node _ ``Lean.Parser.Term.paren args =>
      if h : 1 < args.size then
        match args[1] with
        | Lean.Syntax.ident _ _ val _ => val.eraseMacroScopes
        | other => extractChoiceName other
      else `choice
  | _ => `choice

/-- Hilbert choice operator notation: `let x :| p` inside `do` blocks,
optionally with an explicit name label: `let name : x :| p`,
and optionally with an explicit finder instance or hint: `let x :| p using inst`. -/
syntax "let" (atomic(ident " : "))? term ":|" term (" using " term)? : doElem

macro_rules
  | `(doElem| let $[$nm:ident :]? $x:term :| $t $[using $inst]?) => do
    let name := match nm with
      | some n => n.getId
      | none => extractChoiceName x.raw
    let nameStr := Lean.Syntax.mkStrLit name.toString
    let nameTerm : Lean.TSyntax `term ← `(Lean.Name.mkSimple $nameStr)
    match inst with
    | some i => `(doElem| let $x:term ← NonDetT.pickSuchThat _ (fun $x => $t) $nameTerm (wf := $i))
    | none   => `(doElem| let $x:term ← NonDetT.pickSuchThat _ (fun $x => $t) $nameTerm)

end
