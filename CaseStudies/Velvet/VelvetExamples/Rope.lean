import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Bitwise
import Mathlib.Init
import Mathlib.Data.Nat.Basic

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Loom.MonadAlgebras.WP.Gen

import CaseStudies.Velvet.Std

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

inductive Rope where
    | leaf (seg: String ) (weight: Nat)
    | single (c: Rope) (weight: Nat)
    | double (l: Rope) (r: Rope) (weight: Nat)


#generate_predicates Rope

#generate_immediate_structures Rope


method toStr (r: Rope) return (s: String) 
  do
    if r.isSingle then
      return ""
    else if r.isLeaf then
      return ""
    else if r.isDouble then
      return ""
    else return ""

method str_id (s: String) return (ss: String) 
  ensures (s = ss)
  do
    return s

structure Rope': Type where
  wt: Nat
  content: Option String
  left: Option Rope'
  right: Option Rope'


method toStr' (r: Rope') return (s: String) 
 do
   let first := (match r.content with
     | some x => x
     | none => ""
    )
   let second <-  (match r.left with
     | some x => toStr' x
     | none => str_id ""
    )
   let third <-  (match r.right with
     | some x => toStr' x
     | none => str_id ""
    )
    return (first ++ second.1 ++ third.1)

