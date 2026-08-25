import Velvet.Core.Specs
import Lean.Parser
import Lean.Elab.Command

open Lean Elab Command Term Meta Lean.Parser Lean.Macro

syntax "method " ("rec ")? ident bracketedBinder* " returns " "(" ident " : " term ")" (" in " term)?
  (" requires " (atomic(ident " : "))? velvSpecTerm)* (" signals " (atomic(ident " : "))? velvSpecTerm)*
  (" ensures " (atomic(ident " : "))? velvSpecTerm)* " do " doSeq : command

syntax "prove_correct " ident " by " tacticSeq : command
