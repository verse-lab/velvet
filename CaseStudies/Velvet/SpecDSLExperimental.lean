import Lean
import Lean.Parser.Command

import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Attributes

import Loom.MonadAlgebras.WP.Gen

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

open Lean Elab Command Parser Meta


-- `spec` is like `def` but automatically adds `@[loomAbstractionSimp, velvetSpecHelper]` attribute 
elab "spec " name:declId sig:optDeclSig val:declVal : command => do
  let valRaw := val.raw
  if valRaw.isOfKind ``Command.declValSimple then
    let stx ← `(command|
      @[loomAbstractionSimp, velvetSpecHelper]
      def $name $sig $val:declVal
    )
    elabCommand stx
  else
    throwErrorAt val "Unsupported syntax, only allowed syntax is with ':=' "

elab "#printVelvetHelpers" : command => do
  let st := velvetSpecHelpers.getState (← getEnv)
  logInfo m!"Velvet Helpers: {st}"
