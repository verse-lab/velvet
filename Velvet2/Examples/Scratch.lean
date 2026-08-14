import Velvet2.Syntax
import Velvet2.Ghost
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

/-
# Scratch / experiments

Not polished demonstrations; kept for reference while features are under development.
-/

open Std.Internal.Do

def one : Option Nat := do
  pure 1

def incr1 : StateT Nat Id Unit := do
  let cur ← get
  set (cur + 1)

theorem rel_fun_prop_intro {σ : Type} (f g : σ → Prop) :
    (∀ s, Lean.Order.PartialOrder.rel (f s) (g s)) → Lean.Order.PartialOrder.rel f g := by
  intro h
  exact h

theorem spec_bind_intro_state : True := by
  trivial

abbrev BalM α := StateT Nat Id α

noncomputable def withdraw (amt : Nat) (curBal : Ghost Nat) : StateT Nat Id Nat := do
  let bal ← get
  assert hCurBalUnchanged : (fun s => curBal.reveal = s)
  if bal > amt then
    let newAmt := bal - amt
    let _ ← set newAmt
    assert hChanged : (fun s => s = (curBal.reveal - amt))
    pure newAmt
  else
    pure bal

theorem withdraw_correct : True := by
  trivial

method get_idx returns (res : Nat)
  signals False
  ensures res = 1
  do
    return 1
