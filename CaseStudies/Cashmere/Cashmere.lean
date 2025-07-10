import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Lean

import CaseStudies.Cashmere.Syntax_Cashmere

import Loom.MonadAlgebras.WP.Tactic

open Lean.Elab.Term.DoNames

open ExceptionAsFailure

instance demonic_exception: MonadExceptOf String CashmereM where
  throw e := liftM (m := ExceptT String (StateT Bal DivM)) (throw e)
  tryCatch := fun x _ => x

section


open PartialCorrectness DemonicChoice

#derive_lifted_wp for (get : StateT Bal DivM Bal) as CashmereM Bal
#derive_lifted_wp (res: Bal) for (set res : StateT Bal DivM PUnit) as CashmereM PUnit
#derive_lifted_wp (s : String) for (throw s : ExceptT String (StateT Bal DivM) PUnit) as CashmereM PUnit

end

section

open TotalCorrectness DemonicChoice

#derive_lifted_wp for (get : StateT Bal DivM Bal) as CashmereM Bal
#derive_lifted_wp (res: Bal) for (set res : StateT Bal DivM PUnit) as CashmereM PUnit
#derive_lifted_wp (s : String) for (throw s : ExceptT String (StateT Bal DivM) PUnit) as CashmereM PUnit

end

--small aesop upgrade
add_aesop_rules safe (by linarith)

--simple withdraw
bdef withdraw (amount : Nat) returns (u: Unit)
  ensures balance + amount = balanceOld do
  balance := balance - amount
  return

open PartialCorrectness DemonicChoice in
prove_correct withdraw by
  dsimp [withdraw]
  loom_solve

--withdraw a list of values
open PartialCorrectness DemonicChoice in
bdef withdrawSession (amounts : List Nat) returns (u: Unit)
  ensures balance + amounts.sum = balanceOld do
  let mut tmp := amounts
  let balancePrev := balance
  while tmp.nonEmpty
  invariant balance + amounts.sum = balancePrev + tmp.sum
  do
    let amount := tmp.head!
    balance := balance - amount
    tmp := tmp.tail
  return


open PartialCorrectness DemonicChoice in
prove_correct withdrawSession by
  dsimp [withdrawSession]
  loom_solve!

--adding termination measure for total correctness
open TotalCorrectness DemonicChoice in
bdef withdrawSessionTot (amounts : List Nat) returns (u: Unit)
  ensures balance + amounts.sum = balanceOld do
  let mut tmp := amounts
  let balancePrev := balance
  while tmp.nonEmpty
  invariant balance + amounts.sum = balancePrev + tmp.sum
  decreasing tmp.length
  do
    let amount := tmp.head!
    balance := balance - amount
    tmp := tmp.tail
  return

open TotalCorrectness DemonicChoice in
prove_correct withdrawSessionTot by
  dsimp [withdrawSessionTot]
  loom_solve!

--withdraw a concrete session and throw an exception if balance goes below zero
open TotalCorrectness DemonicChoice in
bdef withdrawSessionExcept (amounts : List Nat) returns (u: Unit)
  require balance >= amounts.sum
  ensures balance >= 0
  ensures balance + amounts.sum = balanceOld do
  let mut tmp := amounts
  let balancePrev := balance
  while tmp.nonEmpty
  invariant balance + amounts.sum = balancePrev + tmp.sum
  invariant balance >= tmp.sum
  decreasing tmp.length do
    let amount := tmp.head!
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    tmp := tmp.tail
  return

open TotalCorrectness DemonicChoice in
prove_correct withdrawSessionExcept by
  dsimp [withdrawSessionExcept]
  loom_solve!

--withdraw a session that does not bring balance below zero
open TotalCorrectness DemonicChoice in
bdef withdrawSessionNonDet returns (history : List Nat)
  require balance >= 0
  ensures balance >= 0
  ensures balance + history.sum = balanceOld do
  let (amounts : List Nat) :| amounts.sum ≤ balance
  let mut tmp := amounts
  let balancePrev := balance
  while tmp.nonEmpty
  invariant balance + amounts.sum = balancePrev + tmp.sum
  decreasing tmp.length do
    let amount := tmp.head!
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    tmp := tmp.tail
  return amounts

open TotalCorrectness DemonicChoice in
prove_correct withdrawSessionNonDet by
  dsimp [withdrawSessionNonDet]
  loom_solve!

--we can actually run our code

#eval (withdraw 2).run.run.run 10
#eval (withdrawSession ([1, 2, 6])).run.run.run 12

#eval (withdrawSessionExcept ({1,2,3})).run.run.run 8
#eval (withdrawSessionExcept ([1,2,6])).run.run.run 8
