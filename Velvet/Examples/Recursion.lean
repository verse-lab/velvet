module

public import Velvet
public meta import Velvet

open Std.Internal.Do
open Lean.Order
open WPPartial

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
  | zero => rw [countUp.eq_1]; velvet_vcgen with finish
  | succ k ih => rw [countUp.eq_2]; velvet_vcgen [ih] with finish

@[expose, grind]
public def fibAccSpec : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibAccSpec n b (a + b)

@[grind =]
public theorem fibAccSpec_add (n a b c d : Nat) :
    fibAccSpec n (a + c) (b + d) = fibAccSpec n a b + fibAccSpec n c d := by
  induction n generalizing a b c d with
  | zero => rfl
  | succ n ih =>
    simp [fibAccSpec]
    have : a + c + (b + d) = a + b + (c + d) := by omega
    rw [this]
    exact ih b (a + b) d (c + d)

method rec fibAcc (n : Nat) (a : Nat) (b : Nat)
  returns (res : Nat)
  ensures res = fibAccSpec n a b
do
  match n with
  | .zero => pure a
  | .succ k =>
    let res ← fibAcc k b (a + b)
    pure res

prove_correct fibAcc by
  intro n
  induction n with
  | zero => intro a b; rw [fibAcc.eq_1]; velvet_vcgen with finish
  | succ k ih => intro a b; rw [fibAcc.eq_2]; velvet_vcgen [ih] with finish

@[grind =]
theorem fibAccSpec_succ_0 (n : Nat) : fibAccSpec (n + 1) 0 1 = fibAccSpec n 1 1 := rfl

@[grind =]
theorem fibAccSpec_succ_1 (n : Nat) : fibAccSpec (n + 1) 1 1 = fibAccSpec n 0 1 + fibAccSpec n 1 1 := by
  have : fibAccSpec (n + 1) 1 1 = fibAccSpec n 1 (1 + 1) := rfl
  rw [this]
  have h := fibAccSpec_add n 0 1 1 1
  rw [Nat.zero_add] at h
  exact h

method fibWhile (n : Nat) returns (res : Nat)
  ensures res = fibAccSpec n 0 1
do
  let mut a := 0
  let mut b := 1
  let mut i := 0
  while' loop_cond : i < n
    invariant fib_state : a = fibAccSpec i 0 1 ∧ b = fibAccSpec i 1 1 ∧ i ≤ n
    decreasing remaining : n - i
    done_with fib_done : i = n
  do
    let next := a + b
    a := b
    b := next
    i := i + 1
  return a

prove_correct fibWhile by
  velvet_vcgen [fibWhile, fibAccSpec] with finish

method fibFor (n : Nat) returns (res : Nat)
  ensures res = fibAccSpec n 0 1
do
  let mut a := 0
  let mut b := 1
  let mut i := 0
  assert hi : i = 0
  for' j in List.range n
    invariant cursor_index : i = j
    invariant fib_values : a = fibAccSpec i 0 1 ∧ b = fibAccSpec i 1 1
    invariant index_bound : i ≤ n
    done_with fib_done : i = n ∧ a = fibAccSpec n 0 1
  do
    let next := a + b
    a := b
    b := next
    i := i + 1
  return a

theorem fibFor_correct : fibFor.spec_triple := by
  unfold fibFor.spec_triple
  velvet_vcgen [fibFor, fibAccSpec] with finish

method rec spinRec returns (res : Nat) in Option
  signals True
  ensures res = 2
do
  spinRec

prove_correct spinRec by
  refine spinRec.fixpoint_induct (motive := spinRec.fixpoint_triple_motive) ?_ ?_
  · apply admissible_triple
    intro _
    simp [Named.mk]
  · intro p ih
    velvet_vcgen [ih] with finish

method rec spinRecStateM returns (res : Nat) in StateT Nat Option
  requires (s : Nat) => True
  signals True
  ensures (s : Nat) => res = 2
do
  spinRecStateM

prove_correct spinRecStateM by
  refine spinRecStateM.fixpoint_induct (motive := spinRecStateM.fixpoint_triple_motive) ?_ ?_
  · apply admissible_triple
    intro _
    simp [Named.mk]
  · intro p ih
    velvet_vcgen [ih] with finish

/- Parameterized recursive method (1 argument) with automatically synthesized fixpoint_triple_motive -/
method rec countdownRec (n : Nat) returns (res : Nat) in Option
  signals True
  ensures res = 0
do
  if n = 0 then
    return 0
  else
    countdownRec (n - 1)

prove_correct countdownRec by
  intro n
  refine countdownRec.fixpoint_induct (motive := countdownRec.fixpoint_triple_motive) ?_ ?_ n
  · apply admissible_pi_triple
    intro _
    simp [Named.mk]
  · intro p ih n
    velvet_vcgen [ih] with finish

/-! Recursive method using `partial_fixpoint` with ghost variable `given (g : Nat)` -/
method rec spinWithGiven returns (res : Nat) in Option
  given (g : Nat)
  signals True
  ensures res = 2 ∧ g = g
do
  spinWithGiven

prove_correct spinWithGiven by
  refine spinWithGiven.fixpoint_induct (motive := spinWithGiven.fixpoint_triple_motive) ?_ ?_
  · apply admissible_pi
    intro g
    apply admissible_triple
    intro _
    simp [Named.mk]
  · intro p ih g
    have ih_g := ih g
    velvet_vcgen [ih_g] with finish

#check @spinWithGiven.spec

/-! Parameterized recursive method with program parameter `(n : Nat)` and ghost `given (g : Nat)` -/
method rec countdownWithGiven (n : Nat) returns (res : Nat) in Option
  given (g : Nat)
  signals True
  ensures res = 0 ∧ g = g
do
  if n = 0 then
    return 0
  else
    countdownWithGiven (n - 1)

prove_correct countdownWithGiven by
  refine countdownWithGiven.fixpoint_induct (motive := countdownWithGiven.fixpoint_triple_motive) ?_ ?_
  · apply admissible_pi_apply (P := fun _ c => ∀ (g : Nat), ⦃ True ⦄ c ⦃ fun res => ⌜⟪ensures1 : res = 0 ∧ g = g⟫⌝; ⌜⟪signals1 : True⟫⌝ ⦄)
    intro n
    apply admissible_pi
    intro g
    apply admissible_triple
    intro _
    simp [Named.mk]
  · intro p ih n g
    have ih_n_g := ih (n - 1) g
    velvet_vcgen [ih_n_g] with finish

#check @countdownWithGiven.spec
