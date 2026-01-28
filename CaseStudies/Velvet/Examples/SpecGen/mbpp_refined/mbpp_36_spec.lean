import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 36: Find the nth digit in the decimal expansion of a proper fraction
--
-- Natural language breakdown:
-- 1. A proper fraction is a fraction where the numerator is strictly less than the denominator
-- 2. The decimal expansion of a fraction numerator/denominator is the sequence of digits
--    that appear after the decimal point when dividing numerator by denominator
-- 3. For example: 1/2 = 0.5, so the decimal expansion is [5, 0, 0, 0, ...]
--    (trailing zeros after terminating decimals)
-- 4. For example: 1/3 = 0.333..., so the decimal expansion is [3, 3, 3, 3, ...]
--    (repeating decimals)
-- 5. We want to find the nth digit in this decimal expansion, where n is 1-indexed
--    (n=1 gives the first digit after the decimal point)
-- 6. The digit is computed using the long division algorithm:
--    - To find the kth digit, we compute: (numerator * 10^k) / denominator (integer division)
--      and take the last digit (mod 10)
-- 7. More precisely, the kth digit d_k satisfies:
--    - d_k = ((numerator * 10^k) / denominator) % 10
--    where / is integer division and % is modulo
-- 8. Property-oriented specification: we define what the nth digit IS, not how to compute it
--
-- Key insights:
-- - The nth digit can be computed by multiplying the numerator by 10^n,
--   dividing by the denominator (integer division), and taking mod 10
-- - This works for both terminating and repeating decimals
-- - For proper fractions, numerator < denominator, so we never have digits before the decimal point
--
-- Mathematical definition:
-- Given fraction numerator/denominator where numerator < denominator,
-- the nth digit (1-indexed) in the decimal expansion is:
--   digit_n = ((numerator * 10^n) / denominator) mod 10

-- Helper function: compute the nth digit of the decimal expansion
-- This is the mathematical definition of what we're computing

section Specs

-- Helper Functions

def nthDecimalDigit (numerator: Nat) (denominator: Nat) (n: Nat) : Nat :=
  if denominator = 0 then 0  -- guard against division by zero
  else ((numerator * (10 ^ n)) / denominator) % 10

def require1 (numerator : Nat) (denominator : Nat) (n : Nat) :=
  numerator < denominator  -- proper fraction constraint
def require2 (numerator : Nat) (denominator : Nat) (n : Nat) :=
  denominator > 0  -- cannot divide by zero
def require3 (numerator : Nat) (denominator : Nat) (n : Nat) :=
  n ≥ 1  -- n is 1-indexed (first digit is at position 1)

-- Postcondition clauses
def ensures1 (numerator : Nat) (denominator : Nat) (n : Nat) (digit : Nat) :=
  digit = nthDecimalDigit numerator denominator n  -- the result is the nth decimal digit
def ensures2 (numerator : Nat) (denominator : Nat) (n : Nat) (digit : Nat) :=
  digit ≥ 0 ∧ digit ≤ 9  -- result is a valid decimal digit

def precondition (numerator : Nat) (denominator : Nat) (n : Nat) :=
  require1 numerator denominator n ∧require2 numerator denominator n ∧require3 numerator denominator n
def postcondition (numerator : Nat) (denominator : Nat) (n : Nat) (digit : Nat) :=
  ensures1 numerator denominator n digit ∧
  ensures2 numerator denominator n digit

end Specs

section Impl

method FindNthDigit (numerator: Nat) (denominator: Nat) (n: Nat)
  return (digit: Nat)
  require precondition numerator denominator n
  ensures postcondition numerator denominator n digit
  do
    sorry

prove_correct FindNthDigit by sorry

-- Test cases for specification validation
end Impl

section TestCases

-- Test case 1: 1/2 = 0.5, digit at position 1 is 5
def test1_numerator   : Nat := 1
def test1_denominator : Nat := 2
def test1_n           : Nat := 1
def test1_Expected    : Nat := 5

-- Test case 2: 1/4 = 0.25, digit at position 2 is 5
def test2_numerator   : Nat := 1
def test2_denominator : Nat := 4
def test2_n           : Nat := 2
def test2_Expected    : Nat := 5

-- Test case 3: 1/5 = 0.2, digit at position 1 is 2
def test3_numerator   : Nat := 1
def test3_denominator : Nat := 5
def test3_n           : Nat := 1
def test3_Expected    : Nat := 2

-- Test case 4: 1/8 = 0.125, digit at position 3 is 5
def test4_numerator   : Nat := 1
def test4_denominator : Nat := 8
def test4_n           : Nat := 3
def test4_Expected    : Nat := 5

-- Test case 5: 1/3 = 0.333..., digit at position 5 is 3
def test5_numerator   : Nat := 1
def test5_denominator : Nat := 3
def test5_n           : Nat := 5
def test5_Expected    : Nat := 3

-- Test case 6: 1/6 = 0.16666..., digit at position 4 is 6
def test6_numerator   : Nat := 1
def test6_denominator : Nat := 6
def test6_n           : Nat := 4
def test6_Expected    : Nat := 6

-- Test case 7: 2/3 = 0.666..., digit at position 3 is 6
def test7_numerator   : Nat := 2
def test7_denominator : Nat := 3
def test7_n           : Nat := 3
def test7_Expected    : Nat := 6

-- Test case 8: 5/2 = 2.5, digit at position 1 is 5
def test8_numerator   : Nat := 5
def test8_denominator : Nat := 2
def test8_n           : Nat := 1
def test8_Expected    : Nat := 5

-- Test case 9: 7/4 = 1.75, digit at position 2 is 5
def test9_numerator   : Nat := 7
def test9_denominator : Nat := 4
def test9_n           : Nat := 2
def test9_Expected    : Nat := 5

-- Test case 10: 22/7 = 3.142857..., digit at position 4 is 8
def test10_numerator   : Nat := 22
def test10_denominator : Nat := 7
def test10_n           : Nat := 4
def test10_Expected    : Nat := 8

-- Test case 11: 10/4 = 2.5, position 1 is 5
def test11_numerator   : Nat := 10
def test11_denominator : Nat := 4
def test11_n           : Nat := 1
def test11_Expected    : Nat := 5

-- Test case 12: 50/8 = 6.25, position 2 is 5
def test12_numerator   : Nat := 50
def test12_denominator : Nat := 8
def test12_n           : Nat := 2
def test12_Expected    : Nat := 5

-- Test case 13: 3/11 = 0.2727..., position 3 is 7
def test13_numerator   : Nat := 3
def test13_denominator : Nat := 11
def test13_n           : Nat := 3
def test13_Expected    : Nat := 7

-- Test case 14: 50/99 = 0.505050..., position 6 is 0
def test14_numerator   : Nat := 50
def test14_denominator : Nat := 99
def test14_n           : Nat := 6
def test14_Expected    : Nat := 0

-- Test case 15: 8/16 = 0.5, position 1 is 5
def test15_numerator   : Nat := 8
def test15_denominator : Nat := 16
def test15_n           : Nat := 1
def test15_Expected    : Nat := 5

-- Test case 16: 25/50 = 0.5, position 1 is 5
def test16_numerator   : Nat := 25
def test16_denominator : Nat := 50
def test16_n           : Nat := 1
def test16_Expected    : Nat := 5

-- Test case 17: 7/9 = 0.777..., position 4 is 7
def test17_numerator   : Nat := 7
def test17_denominator : Nat := 9
def test17_n           : Nat := 4
def test17_Expected    : Nat := 7

-- Test case 18: 11/12 = 0.91666..., position 3 is 6
def test18_numerator   : Nat := 11
def test18_denominator : Nat := 12
def test18_n           : Nat := 3
def test18_Expected    : Nat := 6

-- Test case 19: 99/100 = 0.99, position 2 is 9
def test19_numerator   : Nat := 99
def test19_denominator : Nat := 100
def test19_n           : Nat := 2
def test19_Expected    : Nat := 9

-- Test case 20: 47/99 = 0.474747..., position 10 is 7
def test20_numerator   : Nat := 47
def test20_denominator : Nat := 99
def test20_n           : Nat := 10
def test20_Expected    : Nat := 7

-- Recommend to validate: 1, 5, 7, 10, 13, 20

end TestCases
