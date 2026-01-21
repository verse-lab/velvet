import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- SquareRoot: Compute the integer square root of a given natural number
--
-- Natural language breakdown:
-- 1. Given a natural number N, find the largest natural number r such that r * r ≤ N
-- 2. The result r must satisfy two conditions:
--    a. r * r ≤ N (r squared does not exceed N)
--    b. N < (r + 1) * (r + 1) (the next integer squared exceeds N)
-- 3. These two conditions together uniquely determine r as the integer square root
-- 4. For N = 0, the result is 0 (since 0 * 0 = 0 ≤ 0 and 1 * 1 = 1 > 0)
-- 5. For perfect squares like N = 16, the result is exactly sqrt(N) = 4
-- 6. For non-perfect squares like N = 15, the result is floor(sqrt(N)) = 3
--
-- Note: Mathlib provides Nat.sqrt which computes this exact function

section Specs

-- Precondition: No restrictions on input N (all natural numbers are valid)
def precondition (N : Nat) :=
  True

-- Postcondition: result r satisfies r * r ≤ N < (r + 1) * (r + 1)
-- This uniquely characterizes the integer square root
def postcondition (N : Nat) (result : Nat) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)

end Specs

section Impl

method SquareRoot (N : Nat)
  return (result : Nat)
  require precondition N
  ensures postcondition N result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Edge case N = 0 (smallest input, sqrt(0) = 0)
def test1_N : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: N = 1 (smallest positive input, sqrt(1) = 1)
def test2_N : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: N = 15 (non-perfect square, floor(sqrt(15)) = 3)
def test3_N : Nat := 15
def test3_Expected : Nat := 3

-- Test case 4: N = 16 (perfect square, sqrt(16) = 4)
def test4_N : Nat := 16
def test4_Expected : Nat := 4

-- Test case 5: N = 26 (non-perfect square, floor(sqrt(26)) = 5)
def test5_N : Nat := 26
def test5_Expected : Nat := 5

-- Test case 6: N = 100 (larger perfect square, sqrt(100) = 10)
def test6_N : Nat := 100
def test6_Expected : Nat := 10

-- Test case 7: N = 99 (just below perfect square, floor(sqrt(99)) = 9)
def test7_N : Nat := 99
def test7_Expected : Nat := 9

-- Test case 8: N = 2 (small non-perfect square, floor(sqrt(2)) = 1)
def test8_N : Nat := 2
def test8_Expected : Nat := 1

-- Test case 9: N = 4 (small perfect square, sqrt(4) = 2)
def test9_N : Nat := 4
def test9_Expected : Nat := 2

-- Test case 10: N = 50 (non-perfect square, floor(sqrt(50)) = 7)
def test10_N : Nat := 50
def test10_Expected : Nat := 7

-- Recommend to validate: 1, 3, 4

end TestCases
