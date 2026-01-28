import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 35: Find the n-th rectangular number
--
-- Natural language breakdown:
-- 1. A rectangular number R(n) is the product of two consecutive positive integers: n and (n+1)
-- 2. The sequence starts from n=1: R(1) = 1×2 = 2, R(2) = 2×3 = 6, R(3) = 3×4 = 12, etc.
-- 3. Rectangular numbers represent the number of dots that can be arranged in a rectangle
--    with sides differing by 1 (e.g., 2×3, 3×4, 4×5, etc.)
-- 4. The function takes a positive natural number n and returns R(n) = n × (n+1)
-- 5. Edge case: For n=0, we define R(0) = 0 (0×1 = 0) by convention, though typically
--    rectangular numbers start from n=1
-- 6. Property: R(n) is always even because it's the product of consecutive integers
--    (one must be even)
-- 7. Property: R(n) > n for all n > 0 (since R(n) = n×(n+1) > n)
-- 8. Property: R(n) = n² + n (alternative form showing growth rate)
--
-- Specification approach:
-- - Use property-oriented specification: define the mathematical properties the result must satisfy
-- - Primary property: result = n × (n+1)
-- - Secondary properties: result is even (for n > 0), result > n (for n > 0)
-- - The result should uniquely determine the output for any given input

-- Helper definition: Check if a number is even

section Specs

-- Postcondition clauses
def ensures1 (n : Nat) (result : Nat) :=
  result = n * (n + 1)

def precondition (n : Nat) :=
  True  -- no preconditions
def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result

end Specs

section Impl

method NthRectangularNumber (n: Nat)
  return (result: Nat)
  require precondition n
  ensures postcondition n result
  do
    sorry

prove_correct NthRectangularNumber by sorry

-- Test cases for specification validation
end Impl

section TestCases
-- Test case 0: Sample from the problem (n = 4)
def test0_n : Nat := 4
def test0_Expected : Nat := 20

-- Test case 1: n = 0 (edge case - smallest input)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 (first rectangular number)
def test2_n : Nat := 1
def test2_Expected : Nat := 2

-- Test case 3: n = 2 (second rectangular number)
def test3_n : Nat := 2
def test3_Expected : Nat := 6

-- Test case 4: n = 3
def test4_n : Nat := 3
def test4_Expected : Nat := 12

-- Test case 5: n = 5
def test5_n : Nat := 5
def test5_Expected : Nat := 30

-- Test case 6: n = 10 (two-digit input)
def test6_n : Nat := 10
def test6_Expected : Nat := 110

-- Test case 7: n = 15
def test7_n : Nat := 15
def test7_Expected : Nat := 240

-- Test case 8: n = 20
def test8_n : Nat := 20
def test8_Expected : Nat := 420

-- Test case 9: n = 50 (larger input)
def test9_n : Nat := 50
def test9_Expected : Nat := 2550

-- Test case 10: n = 100 (three-digit input)
def test10_n : Nat := 100
def test10_Expected : Nat := 10100

-- Test case 11: n = 123
def test11_n : Nat := 123
def test11_Expected : Nat := 15252

-- Test case 12: n = 500 (larger scale)
def test12_n : Nat := 500
def test12_Expected : Nat := 250500

-- Test case 13: n = 999 (near 1000)
def test13_n : Nat := 999
def test13_Expected : Nat := 999000

-- Test case 14: n = 1000 (four-digit input)
def test14_n : Nat := 1000
def test14_Expected : Nat := 1001000

-- Recommend to validate: 0,1,2,5,9,14

end TestCases
