import Velvet2.Syntax

open Std.Internal.Do

@[grind]
def fibAccSpec : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibAccSpec n b (a + b)

method rec fibAcc (n : Nat) (a : Nat) (b : Nat)
  returns (result : Nat)
  ensures result = fibAccSpec n a b
do
  match n with
  | 0 => return a
  | n' + 1 =>
      let result ← fibAcc n' b (a + b)
      return result

#check fibAcc

prove_correct fibAcc by
  sorry


set_option linter.unusedVariables false in
theorem fibAcc_correct' (n : Nat) (a : Nat) (b : Nat) :
    Triple
    True
    (fibAcc n a b)
    (fun result =>
        NamedProp.one
        (Lean.Name.mkSimple "ensures1")
        (result = fibAccSpec n a b))
    (True : Prop) := by
    apply triple_from_option_spec
    apply fibAcc.partial_correctness

    intro fibAcc_ih ih_fibAcc_raw

    have ih_fibAcc :=
        fun n a b => triple_from_option_spec (ih_fibAcc_raw n a b)

    intro n a b

    exact triple_to_option_spec (by
        sorry)


def f : Option Nat :=
    f 
partial_fixpoint

#check f.partial_correctness
