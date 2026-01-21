/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d966dc2e-0639-4ba7-ae43-20436503f1ff

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (prices : List Nat):
  VerinaSpec.maxProfit_precond prices ↔ LeetProofSpec.precondition prices

- theorem postcondition_equiv (prices : List Nat) (result : Nat) (h_precond : VerinaSpec.maxProfit_precond prices):
  VerinaSpec.maxProfit_postcond prices result h_precond ↔ LeetProofSpec.postcondition prices result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def maxProfit_precond (prices : List Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit

def maxProfit_postcond (prices : List Nat) (result: Nat) (h_precond : maxProfit_precond (prices)) : Prop :=
  -- !benchmark @start postcond
  -- All valid transactions have profit ≤ result
  List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧
  -- result = 0 when no profitable transaction exists (empty, single element, or decreasing prices)
  (result = 0 ↔
    (prices.length ≤ 1 ∨
     prices.zipIdx.all (fun ⟨pi, i⟩ =>
       prices.zipIdx.all (fun ⟨pj, j⟩ => i ≥ j ∨ pj ≤ pi)))) ∧
  -- If result > 0, there exists a transaction achieving it
  (result > 0 → prices.zipIdx.any (fun ⟨pi, i⟩ =>
    prices.zipIdx.any (fun ⟨pj, j⟩ => i < j ∧ pj - pi = result)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- The maximum profit is the largest value of prices[j] - prices[i] where i < j
-- If no such pair exists or all such differences are non-positive, the result is 0

-- Helper: compute the profit for a specific (buy at i, sell at j) pair
-- Using Nat subtraction which truncates to 0 for negative results
def profitAt (prices : List Nat) (i : Nat) (j : Nat) : Nat :=
  if i < j ∧ j < prices.length then prices[j]! - prices[i]! else 0

-- Precondition: no special requirements (works for any list including empty)
def precondition (prices : List Nat) : Prop :=
  True

-- Postcondition: result is the maximum profit achievable
-- 1. Result is an upper bound: for all valid (i, j) pairs with i < j, result >= profit
-- 2. Result is achievable: either result = 0 (no profit possible) or there exists a pair achieving it
-- 3. Result is 0 when list has fewer than 2 elements
def postcondition (prices : List Nat) (result : Nat) : Prop :=
  -- result is an upper bound on all possible profits
  (∀ i : Nat, ∀ j : Nat, i < j → j < prices.length → prices[j]! - prices[i]! ≤ result) ∧
  -- result is achievable (either 0 for no profit or achieved by some pair)
  (result = 0 ∨ (∃ i : Nat, ∃ j : Nat, i < j ∧ j < prices.length ∧ prices[j]! - prices[i]! = result))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (prices : List Nat):
  VerinaSpec.maxProfit_precond prices ↔ LeetProofSpec.precondition prices := by
  exact iff_of_true ( by unfold VerinaSpec.maxProfit_precond; trivial ) ( by unfold LeetProofSpec.precondition; trivial )

theorem postcondition_equiv (prices : List Nat) (result : Nat) (h_precond : VerinaSpec.maxProfit_precond prices):
  VerinaSpec.maxProfit_postcond prices result h_precond ↔ LeetProofSpec.postcondition prices result := by
  -- By definition of `VerinaSpec.maxProfit_postcond` and `LeetProofSpec.postcondition`, we can show that they are equivalent by breaking down the conditions.
  apply Iff.intro;
  · -- Let's unfold the definitions of `VerinaSpec.maxProfit_postcond` and `LeetProofSpec.postcondition`.
    intro h
    unfold VerinaSpec.maxProfit_postcond at h
    unfold LeetProofSpec.postcondition at *;
    constructor;
    · intro i j hij hj; have := h.1; simp_all +decide [ List.pairwise_iff_get ] ;
      convert h.1 ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij using 1;
      rw [ List.getElem?_eq_getElem ] ; aesop;
    · -- If result is positive, then there must be some i and j such that i < j and the profit is exactly result.
      by_cases h_pos : result > 0;
      · -- By definition of `any`, there exists some element in the list where the predicate holds.
        obtain ⟨i, j, hij, h_eq⟩ : ∃ i j, i < j ∧ j < prices.length ∧ prices[j]! - prices[i]! = result := by
          have h_any : ∃ x ∈ prices.zipIdx, ∃ y ∈ prices.zipIdx, x.2 < y.2 ∧ y.1 - x.1 = result := by
            simp_all +decide [ List.any_eq_true ]
          obtain ⟨ x, hx, y, hy, hxy ⟩ := h_any;
          -- Since x and y are in the zipIdx of prices, their indices are valid. Therefore, we can take i = x.2 and j = y.2.
          use x.2, y.2;
          grind;
        exact Or.inr ⟨ i, j, hij, h_eq ⟩;
      · exact Or.inl <| Nat.eq_zero_of_not_pos h_pos;
  · intro h_postcond;
    -- Split the proof into two cases: result = 0 and result > 0.
    by_cases h_result : result = 0;
    · -- Since there's no pair (i, j) with i < j and profit > 0, for any pair (i, j) with i < j, the profit must be 0.
      have h_no_profit : ∀ i j, i < j → j < prices.length → prices[j]! - prices[i]! = 0 := by
        cases h_postcond ; aesop;
      -- Since there's no pair (i, j) with i < j and profit > 0, the pairwise condition holds because for any i < j, the profit is 0, which is ≤ 0.
      have h_pairwise : List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ 0) (prices.zipIdx) := by
        -- By definition of pairwise, we need to show that for any two elements in the list, if their indices are in order, then the second element is not greater than the first.
        have h_pairwise : ∀ (x y : ℕ × ℕ), x ∈ prices.zipIdx → y ∈ prices.zipIdx → x.2 < y.2 → y.1 - x.1 ≤ 0 := by
          intros x y hx hy hxy
          have h_zip : x.1 = prices[x.2]! ∧ y.1 = prices[y.2]! := by
            grind;
          grind;
        exact?;
      -- Since there's no pair (i, j) with i < j and profit > 0, the all condition holds because for any i < j, the profit is 0, which is ≤ 0.
      have h_all : (prices.length ≤ 1 ∨ prices.zipIdx.all (fun ⟨pi, i⟩ => prices.zipIdx.all (fun ⟨pj, j⟩ => i ≥ j ∨ pj ≤ pi))) := by
        simp_all +decide [ List.all_eq_true ];
        grind;
      unfold VerinaSpec.maxProfit_postcond; aesop;
    · -- Since there exists a pair (i, j) where i < j and prices[j] - prices[i] = result, the maximum profit must be at least result.
      have h_max_profit : ∀ i j : ℕ, i < j → j < prices.length → prices[j]! - prices[i]! ≤ result := by
        exact h_postcond.1;
      constructor;
      · -- By definition of `h_max_profit`, for any `i` and `j`, if `i < j` and `j < prices.length`, then `prices[j]! - prices[i]! ≤ result`.
        have h_pairwise : ∀ (x y : ℕ × ℕ), x ∈ prices.zipIdx → y ∈ prices.zipIdx → x.2 < y.2 → y.1 - x.1 ≤ result := by
          intros x y hx hy hxy
          have h_zip : x.1 = prices[x.2]! ∧ y.1 = prices[y.2]! := by
            grind;
          have h_zip : y.2 < prices.length := by
            grind;
          grind;
        exact?;
      · -- Since result is not zero, there exists a pair (i, j) with i < j and prices[j] - prices[i] = result.
        obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : ℕ, i < j ∧ j < prices.length ∧ prices[j]! - prices[i]! = result := by
          cases h_postcond ; aesop;
        -- Since $i < j$ and $prices[j]! - prices[i]! = result$, we can conclude that the pair $(i, j)$ satisfies the condition for the `any` function.
        have h_pair : (prices.zipIdx.any fun ⟨pi, i⟩ => prices.zipIdx.any fun ⟨pj, j⟩ => i < j ∧ pj - pi = result) := by
          simp +zetaDelta at *;
          use prices[i]!, i, by
            grind, prices[j]!, j, by
            grind;
          aesop;
        simp_all +decide [ List.any_eq, List.all_eq ];
        grind