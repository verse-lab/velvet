import Velvet.Core.Options
import Velvet.Core.Specs
import Lean.Parser

open Lean

/-- An explicit binder `(x : T)` (or `(x)`), decomposed for later use.
The raw syntax node is retained for source-accurate error reporting. -/
structure AssertionBinder where
  ident : Ident
  type : Option (TSyntax `term)
  stx : TSyntax `velvBinder

/-- A single `requires`/`ensures`/`signals` assertion, either `(binder)*, term` or a bare `term`.
The original syntax node is retained so that later elaboration errors can point at the clause. -/
structure AssertionInfo where
  name : Option Ident
  binders : Array AssertionBinder
  term : TSyntax `term
  stx : TSyntax `velvSpecTerm

/-- A method parameter binder, e.g. `(n : Nat)` or `{n : Nat}`. -/
structure MethodParam where
  ident : Ident
  type : TSyntax `term
  stx : TSyntax `Lean.Parser.Term.bracketedBinder

/-- All flags parsed from a `method` declaration, before the `def`/`spec` are generated. -/
structure MethodElabContext where
  name : Ident
  binders : Array MethodParam
  retId : Ident
  retType : TSyntax `term
  monadStack : Option (TSyntax `term)
  termination : VelvetSemanticsTermination
  isRec : Bool
  body : TSyntax `Lean.Parser.Term.doSeq
  requiresClauses : Array AssertionInfo
  signalsClauses : Array AssertionInfo
  ensuresClauses : Array AssertionInfo

/-- Persisted direct statement of a generated `methodName.spec_triple` contract. -/
structure MethodSpecEntry where
  name : Name
  statement : Syntax
