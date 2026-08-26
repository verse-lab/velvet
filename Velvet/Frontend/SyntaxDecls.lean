module

public import Velvet.Core.Specs
public meta import Lean.Parser
public meta import Lean.Elab.Command

open Lean Elab Command Term Meta Lean.Parser Lean.Macro

syntax (docComment)? "method " ("rec ")? ident (bracketedBinder <|> binderIdent)* " returns " "(" ident " : " term ")" (" in " term)?
  (" given " (bracketedBinder <|> binderIdent)+)?
  (" requires " (atomic(ident " : "))? velvSpecTerm)* (" signals " (atomic(ident " : "))? velvSpecTerm)*
  (" ensures " (atomic(ident " : "))? velvSpecTerm)* " do " doSeq : command

syntax "prove_correct " ident " by " tacticSeq : command
