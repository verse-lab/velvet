import Velvet2.Syntax
import Velvet2.VCGen.Frontend

open Std.Internal.Do

method rec countUp (n : Nat)
  returns (res : Nat)
  ensures res_eq: res = n
do
  match n with
  | .zero => pure 0
  | .succ k =>
    let b ← countUp k
    pure (Nat.succ b)

prove_correct countUp by
  intro n
  induction n with
  | zero => rw [countUp.eq_1]; vcgen_
  | succ k ih => rw [countUp.eq_2]; vcgen_ [ih] with finish

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

/- Recursive Fibonacci, verified by structural induction on `n`. -/
method rec fibAcc (n : Nat) (a : Nat) (b : Nat)
  returns (result : Nat)
  ensures result = fibAccSpec n a b
do
  match n with
  | 0 => return a
  | n' + 1 =>
      let result ← fibAcc n' b (a + b)
      return result

prove_correct fibAcc by
  intro n a b
  induction n generalizing a b with
  | zero => rw [fibAcc.eq_1]; vcgen_ with finish
  | succ k ih => rw [fibAcc.eq_2]; vcgen_ [ih] with finish

/- Iterative Fibonacci using Velvet's annotated `while'` loop syntax. -/
method fibWhile (n : Nat)
  returns (result : Nat)
  ensures result_eq: result = fibAccSpec n 0 1
do
  let mut a := 0
  let mut b := 1
  let mut i := 0
  while' i < n
    invariant fib_state :
      a = fibAccSpec i 0 1 ∧ b = fibAccSpec i 1 1 ∧ i ≤ n
    decreasing remaining : n - i
    done_with fib_done : i = n ∧ a = fibAccSpec n 0 1
  do
    let next := a + b
    a := b
    b := next
    i := i + 1
  return a

prove_correct fibWhile by
  vcgen_ [fibWhile, fibAccSpec] with finish
