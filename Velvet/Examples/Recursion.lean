module

public import Velvet
public meta import Velvet

open Std.WP
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
  | zero => unfold countUp; velvet_vcgen with finish
  | succ k ih => unfold countUp; velvet_vcgen with finish

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
  while loop_cond : i < n
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
  for j in List.range n
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

method rec spinRecStateM returns (res : Nat) in StateT Nat Option
  requires (s : Nat) => True
  signals True
  ensures (s : Nat) => res = 2
do
  spinRecStateM

prove_correct spinRecStateM by
  fixpoint_induction spinRecStateM
  all_goals velvet_vcgen with finish

method rec countdownRec (n : Nat) returns (res : Nat) in Option
  signals True
  ensures res = 0
do
  if n = 0 then
    return 0
  else
    countdownRec (n - 1)

prove_correct countdownRec by
  fixpoint_induction countdownRec
  all_goals velvet_vcgen with finish

/-! A statement about `countdownRec` other than its contract. -/
theorem countdownRec_le :
    ∀ n, ⦃ True ⦄ countdownRec n ⦃ fun res => ⌜res ≤ n⌝; fun _ => ⌜True⌝ ⦄ := by
  fixpoint_induction countdownRec
  all_goals velvet_vcgen with finish

/-! `fixpoint_induction` has no rule for `∃`, so it leaves the admissibility of that part as goal
`adm`, to prove directly. -/
theorem countdownRec_exists :
    ∃ k, ∀ n, ⦃ ⌜n < k⌝ ⦄ countdownRec n ⦃ fun res => ⌜res = 0⌝; fun _ => ⌜True⌝ ⦄ := by
  fixpoint_induction countdownRec
  case step =>
    refine ⟨0, ?_⟩
    velvet_vcgen with finish
  case adm =>
    -- `k = 0` works for every approximation, so the statement is `True` of each of them.
    have h : ∀ p : Nat → Option Nat,
        ∃ k, ∀ n, ⦃ ⌜n < k⌝ ⦄ p n ⦃ fun res => ⌜res = 0⌝; fun _ => ⌜True⌝ ⦄ :=
      fun p => ⟨0, fun n => ⟨by simp⟩⟩
    simp only [h]
    exact admissible_const_true

/-! `k` stays fixed in the recursive calls, so it is introduced; `n` stays quantified. -/
method rec addTo (n : Nat) (k : Nat) returns (res : Nat) in Option
  signals True
  ensures res = n + k
do
  if n = 0 then
    return k
  else
    let r ← addTo (n - 1) k
    return r + 1


prove_correct addTo by
  fixpoint_induction addTo
  all_goals velvet_vcgen with finish

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
  fixpoint_induction countdownWithGiven
  all_goals velvet_vcgen with finish

#check @countdownWithGiven.spec

/-! McCarthy's 91 function: nested recursion, where the inner call's result is the outer call's
argument. The induction hypothesis holds for every argument, so it applies at both calls. -/
method rec f91 (n : Nat) returns (res : Nat) in Option
  signals True
  ensures res = if n > 100 then n - 10 else 91
do
  if n > 100 then
    return n - 10
  else
    let r ← f91 (n + 11)
    f91 r

prove_correct f91 by
  fixpoint_induction f91
  all_goals velvet_vcgen with finish

/-! Two triples proved together: each is the other's induction hypothesis at the recursive call. -/
method rec parity (n : Nat) returns (res : Bool) in Option
  signals True
  ensures True
do
  if n = 0 then
    return true
  else
    let r ← parity (n - 1)
    return !r

theorem parity_even_odd :
    (∀ n, ⦃ ⌜n % 2 = 0⌝ ⦄ parity n ⦃ fun r => ⌜r = true⌝; fun _ => ⌜True⌝ ⦄) ∧
    (∀ n, ⦃ ⌜n % 2 = 1⌝ ⦄ parity n ⦃ fun r => ⌜r = false⌝; fun _ => ⌜True⌝ ⦄) := by
  fixpoint_induction parity
  case step =>
    -- Keeps the conjunction: clearing it hits the bug in `SplitAfterClear.lean`.
    obtain ⟨ih_even, ih_odd⟩ := ‹_ ∧ _›
    constructor
    · clear ih_even
      velvet_vcgen with finish
    · clear ih_odd
      velvet_vcgen with finish
  all_goals velvet_vcgen with finish
