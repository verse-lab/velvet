import Auto
import Lean
import Lean.Parser

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import Loom.MonadAlgebras.Velvet.Extension

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

-- lemma simpMProp (α β : Type) (P : _ -> Prop) :
--   (∀ a : MProdWithNames α β n, P a) =
--   (∀ a b, P ⟨a, b⟩) := by
--   sorry

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

elab "velvet_solve" : tactic => withMainContext do
  let ctx := (<- solverHints.get)
  let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
  for c in ctx do
    hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
  hints := hints.push $ <- `(Auto.hintelem| *)
  evalTactic $ <- `(tactic| (
  intro; wpgen;
  try simp only [loomWpSimp]
  try unfold spec
  try simp only [invariants]
  try simp only [WithName.mk']
  try simp only [WithName.erase]
  try simp only [List.foldr]
  try simp only [loomLogicSimp]
  repeat' (apply And.intro <;> (repeat loom_intro))
  all_goals try unfold WithName at *
  any_goals solve | ((try simp only [loomAbstractionSimp] at *); auto [$hints,*])
))

elab "velvet_solve?" : tactic => withMainContext do
  let ctx := (<- solverHints.get)
  let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
  for c in ctx do
    hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
  -- hints := hints.push $ <- `(Auto.hintelem| *)
  let tac <- `(tactic| (
  intro
  try simp only [$(mkIdent `loomAbstractionSimp):ident] at *
  wpgen
  try simp only [$(mkIdent `loomWpSimp):ident]
  try simp only [$(mkIdent `WithName):ident]
  try unfold spec
  try simp only [$(mkIdent `invariants):ident]
  try simp only [$(mkIdent `WithName.mk'):ident]
  try simp only [$(mkIdent `WithName.erase):ident]
  try simp only [$(mkIdent `List.foldr):ident]
  try simp only [$(mkIdent `loomLogicSimp):ident]
  try simp only [$(mkIdent `simpMProp):ident]
  repeat' (apply $(mkIdent `And.intro) <;> (repeat loom_intro))
  any_goals auto [$hints,*]
  ))
  Tactic.TryThis.addSuggestion (<-getRef) tac
