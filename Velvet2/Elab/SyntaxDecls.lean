import Lean.Parser
import Lean.Elab.Command
import Std.Internal.Do
import Velvet2.Ghost

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do

declare_syntax_cat velvBinder
syntax "(" ident (" : " term)? ")" : velvBinder

declare_syntax_cat velvSpecTerm
syntax (atomic(velvBinder+ " => " termBeforeDo) <|> termBeforeDo) : velvSpecTerm

syntax "method " ("rec ")? ident bracketedBinder* " returns " "(" ident " : " term ")" (" in " term)?
  (" requires " (atomic(ident " : "))? velvSpecTerm)* (" signals " (atomic(ident " : "))? velvSpecTerm)*
  (" ensures " (atomic(ident " : "))? velvSpecTerm)* " do " doSeq : command

syntax "prove_correct " ident " by " tacticSeq : command

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

syntax "assert" (atomic(ident " : ")) term : term

macro "let" "ghost" x:ident ":=" value:term : doElem =>
  `(doElem| let mut $x := _root_.Ghost.mk $value)

syntax (name := ghostReassign) "*" ident " := " term : doElem
