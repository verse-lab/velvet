import Velvet2.Syntax
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

open Std.Internal.Do

@[grind]
def fibAccSpec : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibAccSpec n b (a + b)

@[grind =]
theorem fibAccSpec_add (n a b c d : Nat) :
    fibAccSpec n (a + c) (b + d) = fibAccSpec n a b + fibAccSpec n c d := by
  induction n generalizing a b c d with
  | zero => simp [fibAccSpec]
  | succ n ih =>
    simp only [fibAccSpec]
    rw [show a + c + (b + d) = (a + b) + (c + d) by omega]
    exact ih b (a + b) d (c + d)

@[grind =]
theorem fibAccSpec_pair_step (n : Nat) :
    fibAccSpec n 0 1 + fibAccSpec n 1 1 = fibAccSpec (n + 1) 1 1 := by
  rw [← fibAccSpec_add]
  rfl

method rec fibAcc (n : Nat) (a : Nat) (b : Nat)
  returns (result : Nat)
  signals False
  ensures result = fibAccSpec n a b
do
  match n with
  | 0 => return a
  | n' + 1 =>
      let result ← fibAcc n' b (a + b)
      return result

#check fibAcc

prove_correct fibAcc.spec by
  sorry

/- Iterative Fibonacci using Velvet's annotated finite-range loop syntax. -/
method fibFor (n : Nat)
  returns (result : Nat)
  signals False
  ensures result = fibAccSpec n 0 1
do
  let mut a := 0
  let mut b := 1
  let mut i := 0
  assert hi : i = 0
  for' j in 0...n
    invariant cursor_index : i = j
    invariant fib_values :
      a = fibAccSpec i 0 1 ∧ b = fibAccSpec i 1 1
    invariant index_bound : i ≤ n
    done_with fib_done : i = n ∧ a = fibAccSpec n 0 1
  do
    let next := a + b
    a := b
    b := next
    i := i + 1
  return a

#check fibFor

prove_correct fibFor.spec by
  vcgen_ [fibFor, fibAccSpec] with try finish
  all_goals sorry


set_option linter.unusedVariables false in
theorem fibAcc_correct' (n : Nat) (a : Nat) (b : Nat) :
    Triple
    (fibAcc n a b)
    True
    (fun result =>
        Named.mk
        (Lean.Name.mkSimple "ensures1")
        none
        (result = fibAccSpec n a b))
    (True : Prop) := by
    apply triple_from_option_spec
    apply fibAcc.partial_correctness

    intro fibAcc_ih ih_fibAcc_raw

    have ih_fibAcc :=
        fun n a b => triple_from_option_spec (ih_fibAcc_raw n a b)

    intro n a b

    exact triple_to_option_spec (by
      vcgen_ [fibAcc, fibAccSpec]
      all_goals simp_all [fibAccSpec])


def f : Option Nat :=
    f 
partial_fixpoint

#check f.partial_correctness
