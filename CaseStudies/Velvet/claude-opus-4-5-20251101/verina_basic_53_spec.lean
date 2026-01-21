import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    CalSum: Compute the sum of the first N natural numbers
    Natural language breakdown:
    1. Given a natural number N, compute the sum 0 + 1 + 2 + ... + N
    2. When N = 0, the sum is 0
    3. For positive N, the sum follows the triangular number formula: N * (N + 1) / 2
    4. The result is equivalent to the sum of all natural numbers from 0 to N inclusive
    5. Key mathematical identity: ∑_{i=0}^{N} i = N * (N + 1) / 2
    6. This is related to Finset.sum_range_id which gives ∑_{i=0}^{n-1} i = n * (n - 1) / 2
    7. For our problem (sum from 0 to N inclusive), we need (N + 1) * N / 2 = N * (N + 1) / 2
-/

section Specs

-- Precondition: No restrictions on N (any natural number is valid)
def precondition (N : Nat) :=
  True

-- Postcondition: The result equals the closed-form formula N * (N + 1) / 2
-- This is the triangular number formula for the sum of first N natural numbers
def postcondition (N : Nat) (result : Nat) :=
  result = N * (N + 1) / 2

end Specs

section Impl

method CalSum (N : Nat)
  return (result : Nat)
  require precondition N
  ensures postcondition N result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: N = 0, sum of first 0 natural numbers is 0
def test1_N : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: N = 1, sum = 0 + 1 = 1
def test2_N : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: N = 5, sum = 0 + 1 + 2 + 3 + 4 + 5 = 15
def test3_N : Nat := 5
def test3_Expected : Nat := 15

-- Test case 4: N = 10, sum = 55
def test4_N : Nat := 10
def test4_Expected : Nat := 55

-- Test case 5: N = 20, sum = 210
def test5_N : Nat := 20
def test5_Expected : Nat := 210

-- Test case 6: N = 2, sum = 0 + 1 + 2 = 3
def test6_N : Nat := 2
def test6_Expected : Nat := 3

-- Test case 7: N = 100, sum = 5050 (classic example)
def test7_N : Nat := 100
def test7_Expected : Nat := 5050

-- Test case 8: N = 3, sum = 0 + 1 + 2 + 3 = 6
def test8_N : Nat := 3
def test8_Expected : Nat := 6

-- Recommend to validate: 1, 3, 4

end TestCases
