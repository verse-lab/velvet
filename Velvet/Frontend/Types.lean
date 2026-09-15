module

public import Velvet.Frontend.Options
public import Velvet.Core.Specs
public meta import Lean.Parser

open Lean

/-- An explicit binder `(x : T)` (or `(x)`), decomposed for later use.
The raw syntax node is retained for source-accurate error reporting. -/
public structure AssertionBinder where
  ident : Ident
  type : Option (TSyntax `term)
  stx : TSyntax `velvBinder

/-- A single `requires`/`ensures`/`signals` assertion, either `(binder)*, term` or a bare `term`.
The original syntax node is retained so that later elaboration errors can point at the clause. -/
public structure AssertionInfo where
  name : Option Ident
  binders : Array AssertionBinder
  term : TSyntax `term
  stx : TSyntax `velvSpecTerm

/-- All flags parsed from a `method` declaration, before the `def`/`spec` are generated. -/
public structure MethodElabContext where
  doc : Option (TSyntax `Lean.Parser.Command.docComment) := none
  name : Ident
  binders : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder]
  givenBinders : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] := #[]
  retId : Ident
  retType : TSyntax `term
  monadStack : Option (TSyntax `term)
  termination : VelvetSemanticsTermination
  isRec : Bool
  body : TSyntax `Lean.Parser.Term.doSeq
  requiresClauses : Array AssertionInfo
  signalsClauses : Array AssertionInfo
  ensuresClauses : Array AssertionInfo

/-- Persisted contract statement, keyed by the fully qualified method name. -/
public structure MethodSpecEntry where
  name : Name
  statement : Syntax

private def addMethodSpecEntry (state : Std.HashMap Name Syntax) (entry : MethodSpecEntry) :=
  state.insert entry.name entry.statement

public initialize methodSpecExt : SimplePersistentEnvExtension MethodSpecEntry (Std.HashMap Name Syntax) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addMethodSpecEntry
    addImportedFn := fun entries =>
      mkStateFromImportedEntries addMethodSpecEntry {} entries }
