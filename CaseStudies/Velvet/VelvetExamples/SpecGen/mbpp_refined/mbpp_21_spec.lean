import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 21: Write a function to find m number of multiples of n
--
-- Natural language breakdown:
-- 1. We need to find the first m multiples of a given number n
-- 2. A multiple of n is any number of the form k×n where k is a positive integer
-- 3. The first multiple of n is n itself (1×n = n)
-- 4. The second multiple is 2×n, the third is 3×n, and so on
-- 5. We need to return exactly m such multiples in ascending order
-- 6. The result should be a Array containing: [n, 2×n, 3×n, ..., m×n]
-- 7. Edge cases:
--    - m = 0: Should return an empty Array (no multiples requested)
--    - m = 1: Should return a Array with one element [n]
--    - n = 0: All multiples are 0, so return [0, 0, 0, ..., 0] (m times)
--    - Both m and n can be any natural number (including 0)
-- 8. The function should work for any non-negative values of m and n

section Specs

-- Postcondition clauses
def ensures1 (n : Nat) (m : Nat) (multiples : Array Nat) :=
  multiples.size = m  -- The result contains exactly m elements
def ensures2 (n : Nat) (m : Nat) (multiples : Array Nat) :=
  ∀ i, i < m → multiples[i]! = (i + 1) * n  -- Each element is the (i+1)-th multiple of n

def precondition (n : Nat) (m : Nat) :=
  True  -- no preconditions
def postcondition (n : Nat) (m : Nat) (multiples : Array Nat) :=
  ensures1 n m multiples ∧
  ensures2 n m multiples

end Specs

method FindMultiples (n: Nat) (m: Nat)
  return (multiples: Array Nat)
  require precondition n m
  ensures postcondition n m multiples
  do
    sorry

prove_correct FindMultiples by sorry

-- Test cases for specification validation
section TestCases

-- Test case 1: Find 5 multiples of 3
-- Input: n = 3, m = 5
-- Expected: [3, 6, 9, 12, 15]
def test1_n : Nat := 3
def test1_m : Nat := 5
def test1_Expected : Array Nat := #[3, 6, 9, 12, 15]

-- Test case 2: Find 0 multiples (edge case: m = 0)
-- Input: n = 7, m = 0
-- Expected: []
def test2_n : Nat := 7
def test2_m : Nat := 0
def test2_Expected : Array Nat := #[]

-- Test case 3: Find 1 multiple (edge case: m = 1)
-- Input: n = 10, m = 1
-- Expected: [10]
def test3_n : Nat := 10
def test3_m : Nat := 1
def test3_Expected : Array Nat := #[10]

-- Test case 4: Multiples of 0 (edge case: n = 0)
-- Input: n = 0, m = 4
-- Expected: [0, 0, 0, 0]
def test4_n : Nat := 0
def test4_m : Nat := 4
def test4_Expected : Array Nat := #[0, 0, 0, 0]

-- Test case 5: Multiples of 1
-- Input: n = 1, m = 6
-- Expected: [1, 2, 3, 4, 5, 6]
def test5_n : Nat := 1
def test5_m : Nat := 6
def test5_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

-- Test case 6: Large multiples
-- Input: n = 50, m = 3
-- Expected: [50, 100, 150]
def test6_n : Nat := 50
def test6_m : Nat := 3
def test6_Expected : Array Nat := #[50, 100, 150]

-- Test case 7: Many small multiples
-- Input: n = 2, m = 10
-- Expected: [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]
def test7_n : Nat := 2
def test7_m : Nat := 10
def test7_Expected : Array Nat :=
  #[2, 4, 6, 8, 10, 12, 14, 16, 18, 20]

-- Test case 8: Both m and n are 0 (edge case)
-- Input: n = 0, m = 0
-- Expected: []
def test8_n : Nat := 0
def test8_m : Nat := 0
def test8_Expected : Array Nat := #[]

-- Recommend to validate: test cases 1, 2, 3, 4, 6, 7

-- Verification that our specification captures the correct behavior:
-- 1. Returns exactly m elements
-- 2. Each element at index i is (i+1) × n
-- 3. Elements are strictly increasing when n > 0
-- 4. Handles edge cases: m=0 (empty), n=0 (all zeros), m=1 (single element)
-- 5. First element is always n when m > 0
-- 6. Works for any combination of natural numbers m and n

end TestCases
