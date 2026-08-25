import Velvet

open Std.WP

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
  | zero => rw [countUp.eq_1]; vcgen_ with finish
  | succ k ih => rw [countUp.eq_2]; vcgen_ [ih] with finish

@[grind]
def fibAccSpec : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibAccSpec n b (a + b)

@[grind =]
theorem fibAccSpec_add (n a b c d : Nat) :
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
  | zero => intro a b; rw [fibAcc.eq_1]; vcgen_ with finish
  | succ k ih => intro a b; rw [fibAcc.eq_2]; vcgen_ [ih] with finish

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
  vcgen_ [fibWhile, fibAccSpec] with finish

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
  vcgen_ [fibFor, fibAccSpec] with try finish
  case cursor_index =>
    rename_i cur rest h
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_head h
    omega
  case cursor_index =>
    rename_i pref cur next rest h _
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_next h
    omega
  case index_bound =>
    rename_i n pref cur next rest h b
    rcases b with ⟨a, b, i⟩
    rw [Std.Internal.ForIn.toList_list] at h
    have hcur : (List.range n)[pref.length]? = (pref ++ cur :: next :: rest)[pref.length]? := by rw [h]
    rw [List.getElem?_append_right (by omega)] at hcur
    simp only [Nat.sub_self, List.getElem?_cons_zero] at hcur
    have hlen : pref.length < n := by
      have := congrArg List.length h
      simp only [List.length_range, List.length_append, List.length_cons] at this
      omega
    rw [List.getElem?_range hlen] at hcur
    cases hcur
    have := list_range_next h
    omega
  case fib_done =>
    rename_i n pref cur h b
    rcases b with ⟨a, b, i⟩
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_last h
    grind
