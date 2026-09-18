module

public import Velvet
public meta import Velvet

/-!
## Program description

You are given an array `prices` where `prices[i]` is the price of a given stock
on the `i`-th day.

You want to maximize your profit by choosing a single day to buy one stock and
choosing a different day in the future to sell that stock.

Return the maximum profit you can achieve from this transaction. If you cannot
achieve any profit, return 0.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace BestTimeToBuyAndSellStock

section Specs

public def pairProfit (prices : Array Nat) (i : Nat) (j : Nat) : Nat :=
  prices[j]! - prices[i]!

public def ValidPair (prices : Array Nat) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < prices.size

public def precondition (_prices : Array Nat) : Prop :=
  True

public def postcondition (prices : Array Nat) (result : Nat) : Prop :=
  (∀ (i : Nat) (j : Nat), ValidPair prices i j → pairProfit prices i j ≤ result) ∧
  ((prices.size < 2) → result = 0) ∧
  ((prices.size ≥ 2) → (∃ (i : Nat) (j : Nat), ValidPair prices i j ∧ result = pairProfit prices i j))

end Specs

section Implementation

method maxProfit (prices : Array Nat)
  returns (result : Nat)
  requires valid: precondition prices
  ensures maximum_profit: postcondition prices result
do
  if small: prices.size < 2 then
    return 0
  else
    let mut minPrice := prices[0]!
    let mut best := 0
    let mut i := 1
    while scanning: i < prices.size
      invariant bounds: 1 ≤ i ∧ i ≤ prices.size
      invariant minPrice_witness: ∃ m : Nat, m < i ∧ minPrice = prices[m]!
      invariant minPrice_is_min: ∀ k : Nat, k < i → minPrice ≤ prices[k]!
      invariant best_upper_prefix: ∀ a b : Nat, a < b ∧ b < i → pairProfit prices a b ≤ best
      invariant best_witness_prefix: (i < 2 → best = 0) ∧ (2 ≤ i → ∃ a b : Nat, a < b ∧ b < i ∧ best = pairProfit prices a b)
      decreasing remaining: prices.size - i
      done_with done: i = prices.size
    do
      let price := prices[i]!
      let profit := price - minPrice
      if better: best < profit then
        best := profit
      if smaller: price < minPrice then
        minPrice := price
      i := i + 1
    return best

end Implementation

section Proof

theorem small_postcondition (prices : Array Nat) (h : prices.size < 2) :
    postcondition prices 0 := by
  refine ⟨?_, by simp, ?_⟩
  · intro i j ⟨hij, hj⟩
    omega
  · intro h2
    omega

theorem exit_postcondition (prices : Array Nat) (best i : Nat)
    (hsize : ¬ prices.size < 2)
    (hbest_upper : ∀ a b : Nat, a < b ∧ b < i → pairProfit prices a b ≤ best)
    (hbest_witness : (i < 2 → best = 0) ∧ (2 ≤ i → ∃ a b : Nat, a < b ∧ b < i ∧ best = pairProfit prices a b))
    (hdone : i = prices.size) :
    postcondition prices best := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ⟨hab, hb⟩
    rw [← hdone] at hb
    exact hbest_upper a b ⟨hab, hb⟩
  · intro hlt
    omega
  · intro _
    have h2 : 2 ≤ i := by omega
    rcases hbest_witness.2 h2 with ⟨a, b, hab, hb, heq⟩
    refine ⟨a, b, ⟨hab, by omega⟩, heq⟩

theorem pairProfit_le_of_min (prices : Array Nat) (minPrice i a : Nat)
    (ha : a < i) (hmin : ∀ k, k < i → minPrice ≤ prices[k]!) :
    pairProfit prices a i ≤ prices[i]! - minPrice := by
  unfold pairProfit
  have := hmin a ha
  omega

theorem step_upper_new_best (prices : Array Nat) (minPrice best i : Nat)
    (hbetter : best < prices[i]! - minPrice)
    (hbest_upper : ∀ a b : Nat, a < b ∧ b < i → pairProfit prices a b ≤ best)
    (hmin : ∀ k, k < i → minPrice ≤ prices[k]!) :
    ∀ a b : Nat, a < b ∧ b < i + 1 → pairProfit prices a b ≤ prices[i]! - minPrice := by
  intro a b ⟨hab, hb⟩
  by_cases hbi : b < i
  · have h1 := hbest_upper a b ⟨hab, hbi⟩
    omega
  · have hbeq : b = i := by omega
    subst b
    exact pairProfit_le_of_min prices minPrice i a (by omega) hmin

theorem step_witness_new_best (prices : Array Nat) (minPrice i : Nat)
    (hwitness : ∃ m, m < i ∧ minPrice = prices[m]!) :
    (i + 1 < 2 → prices[i]! - minPrice = 0) ∧
    (2 ≤ i + 1 → ∃ a b, a < b ∧ b < i + 1 ∧ prices[i]! - minPrice = pairProfit prices a b) := by
  rcases hwitness with ⟨m, hm, rfl⟩
  refine ⟨by omega, ?_⟩
  intro _
  refine ⟨m, i, hm, by omega, ?_⟩
  unfold pairProfit
  rfl

theorem step_upper_keep_best (prices : Array Nat) (minPrice best i : Nat)
    (hnot_better : ¬ best < prices[i]! - minPrice)
    (hbest_upper : ∀ a b : Nat, a < b ∧ b < i → pairProfit prices a b ≤ best)
    (hmin : ∀ k, k < i → minPrice ≤ prices[k]!) :
    ∀ a b : Nat, a < b ∧ b < i + 1 → pairProfit prices a b ≤ best := by
  intro a b ⟨hab, hb⟩
  by_cases hbi : b < i
  · exact hbest_upper a b ⟨hab, hbi⟩
  · have hbeq : b = i := by omega
    subst b
    have hle := pairProfit_le_of_min prices minPrice i a (by omega) hmin
    omega

theorem step_witness_keep_best (prices : Array Nat) (minPrice best i : Nat)
    (hnot_better : ¬ best < prices[i]! - minPrice)
    (hwitness : ∃ m, m < i ∧ minPrice = prices[m]!)
    (hbest_witness : (i < 2 → best = 0) ∧ (2 ≤ i → ∃ a b : Nat, a < b ∧ b < i ∧ best = pairProfit prices a b))
    (hbound : 1 ≤ i) :
    (i + 1 < 2 → best = 0) ∧
    (2 ≤ i + 1 → ∃ a b, a < b ∧ b < i + 1 ∧ best = pairProfit prices a b) := by
  refine ⟨by omega, ?_⟩
  intro _
  by_cases hi2 : 2 ≤ i
  · rcases hbest_witness.2 hi2 with ⟨a, b, hab, hb, heq⟩
    exact ⟨a, b, hab, by omega, heq⟩
  · have hi1 : i = 1 := by omega
    subst i
    have hbest0 : best = 0 := hbest_witness.1 (by omega)
    rcases hwitness with ⟨m, hm, hm_eq⟩
    have hm0 : m = 0 := by omega
    subst m
    have hprofit0 : prices[1]! - minPrice = 0 := by omega
    refine ⟨0, 1, by omega, by omega, ?_⟩
    unfold pairProfit
    rw [hbest0, ← hm_eq, ← hprofit0]

prove_correct maxProfit by
  velvet_vcgen [maxProfit, postcondition] with try finish
  case maximum_profit =>
    exact small_postcondition _ small
  case maximum_profit =>
    rename_i prices
    exact exit_postcondition prices best i small best_upper_prefix best_witness_prefix done
  case best_upper_prefix =>
    rename_i prices
    exact step_upper_new_best prices minPrice best i better best_upper_prefix minPrice_is_min
  case best_witness_prefix =>
    rename_i prices
    exact step_witness_new_best prices minPrice i minPrice_witness
  case best_upper_prefix =>
    rename_i prices
    exact step_upper_keep_best prices minPrice best i better best_upper_prefix minPrice_is_min
  case best_witness_prefix =>
    rename_i prices
    exact step_witness_keep_best prices minPrice best i better minPrice_witness best_witness_prefix bounds.1
  case best_upper_prefix =>
    rename_i prices
    exact step_upper_keep_best prices minPrice best i better best_upper_prefix minPrice_is_min
  case best_witness_prefix =>
    rename_i prices
    exact step_witness_keep_best prices minPrice best i better minPrice_witness best_witness_prefix bounds.1

end Proof

end BestTimeToBuyAndSellStock
