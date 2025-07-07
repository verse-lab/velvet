import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.NonDetT.Extract
import Velvet.BankExample.Syntax_bank
import Mathlib.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Lean

import Loom.MonadAlgebras.WP.Tactic

import Velvet.Extension
import Velvet.Tactic

open Lean.Elab.Term.DoNames

open Queue

open ExceptionAsSuccess

instance mlift : MonadLift (ExceptT String (StateT Balance DivM)) BankM where
  monadLift x := NonDetT.vis x pure

instance : MonadExceptOf String BankM where
  throw e := mlift.monadLift (throw e)
  tryCatch := fun x _ => x

open TotalCorrectness AngelicChoice

@[spec, loomWpSimp]
noncomputable
def BankM.wp_get_totl: WPGen (get : BankM Balance) where
    get := fun fn x => fn x x
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      erw [StateT.wp_get]


@[spec, loomWpSimp]
def BankM.wp_set_totl (res: Balance) : WPGen (set res : BankM PUnit) where
    get := fun fn x => fn PUnit.unit res
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      simp [StateT.wp_eq, set, StateT.set, wp_pure]

@[spec, loomWpSimp]
noncomputable
def BankM.wp_throw_totl (s: String) : WPGen (throw s: BankM PUnit) where
    get := fun fn x => ⊤
    prop := fun post => by
      simp [throw, instMonadExceptOfMonadExceptOf, throwThe, MonadExceptOf]
      rw [MonadExceptOf.throw, instMonadExceptOfStringBankM]
      simp [mlift, ExceptT.wp_throw]

--small aesop upgrade
add_aesop_rules safe (by linarith)

bdef withdrawSessionAngelic returns (u: Unit)
  require balance > 0
  ensures False do
  let mut amounts: Queue Nat ← pick (Queue Nat)
  while amounts.nonEmpty
  invariant balance >= 0
  invariant balance < amounts.sum
  decreasing amounts.length
  do
    let amount := amounts.dequeue
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    amounts := amounts.tail
  return

@[aesop norm]
theorem mkQueue (x: Balance) : ∃ q: Queue Nat, x < q.sum := by exists {elems := [Int.toNat (x + 1)]}; simp [Queue.sum]

prove_correct withdrawSessionAngelic by
  dsimp [withdrawSessionAngelic]
  loom_solve
