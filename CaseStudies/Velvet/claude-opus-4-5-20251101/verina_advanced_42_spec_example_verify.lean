import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000







def profitAt (prices : List Nat) (i : Nat) (j : Nat) : Nat :=
  if i < j ∧ j < prices.length then prices[j]! - prices[i]! else 0



def precondition (prices : List Nat) : Prop :=
  True






def postcondition (prices : List Nat) (result : Nat) : Prop :=

  (∀ i : Nat, ∀ j : Nat, i < j → j < prices.length → prices[j]! - prices[i]! ≤ result) ∧

  (result = 0 ∨ (∃ i : Nat, ∃ j : Nat, i < j ∧ j < prices.length ∧ prices[j]! - prices[i]! = result))


def test1_prices : List Nat := [7, 1, 5, 3, 6, 4]

def test1_Expected : Nat := 5

def test2_prices : List Nat := [7, 6, 4, 3, 1]

def test2_Expected : Nat := 0

def test3_prices : List Nat := [2, 4, 1]

def test3_Expected : Nat := 2







section Proof
theorem test1_precondition :
  precondition test1_prices := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_prices test1_Expected := by
  constructor
  · intro i j hij hjlen
    simp only [test1_prices, test1_Expected, List.length] at *
    match i, j, hij, hjlen with
    | 0, 1, _, _ => decide
    | 0, 2, _, _ => decide
    | 0, 3, _, _ => decide
    | 0, 4, _, _ => decide
    | 0, 5, _, _ => decide
    | 1, 2, _, _ => decide
    | 1, 3, _, _ => decide
    | 1, 4, _, _ => decide
    | 1, 5, _, _ => decide
    | 2, 3, _, _ => decide
    | 2, 4, _, _ => decide
    | 2, 5, _, _ => decide
    | 3, 4, _, _ => decide
    | 3, 5, _, _ => decide
    | 4, 5, _, _ => decide
    | i + 5, j, hij, hjlen => omega
    | i, j + 6, hij, hjlen => omega
  · right
    use 1, 4
    decide

theorem test2_precondition :
  precondition test2_prices := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_prices test2_Expected := by
  unfold postcondition test2_prices test2_Expected
  constructor
  · intro i j hij hjlen
    simp only [test2_prices, List.length] at hjlen
    interval_cases j <;> interval_cases i <;> simp_all [test2_prices]
  · left
    rfl

theorem test3_precondition :
  precondition test3_prices := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_prices test3_Expected := by
  simp only [postcondition, test3_prices, test3_Expected]
  constructor
  · intro i j hij hjlen
    simp only [List.length] at hjlen
    match i, j with
    | 0, 1 => native_decide
    | 0, 2 => native_decide
    | 1, 2 => native_decide
    | 0, 0 => omega
    | 1, 0 => omega
    | 1, 1 => omega
    | 2, 0 => omega
    | 2, 1 => omega
    | 2, 2 => omega
    | 0, j+3 => omega
    | 1, j+3 => omega
    | 2, j+3 => omega
    | i+3, _ => omega
  · right
    use 0, 1
    native_decide

theorem uniqueness (prices : List Nat):
  precondition prices →
  (∀ ret1 ret2,
    postcondition prices ret1 →
    postcondition prices ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hbound1, hexists1⟩ := hpost1
  obtain ⟨hbound2, hexists2⟩ := hpost2
  apply Nat.le_antisymm
  · -- Show ret1 ≤ ret2
    cases hexists1 with
    | inl h0 =>
      -- ret1 = 0, so ret1 ≤ ret2 trivially
      rw [h0]
      exact Nat.zero_le ret2
    | inr hex =>
      -- There exist i, j such that prices[j]! - prices[i]! = ret1
      obtain ⟨i, j, hij, hjlen, heq⟩ := hex
      -- By hbound2, this difference is ≤ ret2
      have h := hbound2 i j hij hjlen
      rw [heq] at h
      exact h
  · -- Show ret2 ≤ ret1
    cases hexists2 with
    | inl h0 =>
      -- ret2 = 0, so ret2 ≤ ret1 trivially
      rw [h0]
      exact Nat.zero_le ret1
    | inr hex =>
      -- There exist i, j such that prices[j]! - prices[i]! = ret2
      obtain ⟨i, j, hij, hjlen, heq⟩ := hex
      -- By hbound1, this difference is ≤ ret1
      have h := hbound1 i j hij hjlen
      rw [heq] at h
      exact h
end Proof
