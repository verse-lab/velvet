import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- maxProfit: Find the maximum profit from buying and selling stock once
--
-- Natural language breakdown:
-- 1. Given a list of stock prices where each element represents the price on a day
-- 2. We want to find the maximum profit achievable by buying on one day and selling on a later day
-- 3. The buy day must come strictly before the sell day (i < j)
-- 4. Profit is calculated as sell price minus buy price: prices[j] - prices[i]
-- 5. If no profitable transaction exists (prices always decrease), return 0
-- 6. The result is the maximum over all valid (buy, sell) pairs of (prices[j] - prices[i])
-- 7. For empty list or single element list, no valid transaction exists, so result is 0
-- 8. Natural number subtraction truncates to 0, so unprofitable transactions give 0

section Specs

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

end Specs

section Impl

method maxProfit (prices : List Nat)
  return (result : Nat)
  require precondition prices
  ensures postcondition prices result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - buy at day 1 (price 1), sell at day 4 (price 6), profit = 5
def test1_prices : List Nat := [7, 1, 5, 3, 6, 4]
def test1_Expected : Nat := 5

-- Test case 2: Decreasing prices - no profitable transaction possible
def test2_prices : List Nat := [7, 6, 4, 3, 1]
def test2_Expected : Nat := 0

-- Test case 3: Small profit possible - buy at day 0 (price 2), sell at day 1 (price 4)
def test3_prices : List Nat := [2, 4, 1]
def test3_Expected : Nat := 2

-- Test case 4: Two elements with profit
def test4_prices : List Nat := [1, 2]
def test4_Expected : Nat := 1

-- Test case 5: Empty list - no transaction possible
def test5_prices : List Nat := []
def test5_Expected : Nat := 0

-- Test case 6: Single element - no transaction possible
def test6_prices : List Nat := [5]
def test6_Expected : Nat := 0

-- Test case 7: All same prices - no profit possible
def test7_prices : List Nat := [3, 3, 3, 3]
def test7_Expected : Nat := 0

-- Test case 8: Increasing prices - best to buy first, sell last
def test8_prices : List Nat := [1, 2, 3, 4, 5]
def test8_Expected : Nat := 4

-- Test case 9: V-shaped prices - buy at bottom
def test9_prices : List Nat := [10, 5, 2, 8, 12]
def test9_Expected : Nat := 10

-- Test case 10: Two elements with no profit (decreasing)
def test10_prices : List Nat := [5, 3]
def test10_Expected : Nat := 0

-- Recommend to validate: 1, 2, 3

end TestCases
