import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
--   sumOfDigits: Compute the sum of the digits of a non-negative integer
--   Natural language breakdown:
--   1. Given a non-negative integer n, we need to compute the sum of its decimal digits
--   2. Each digit of n can be extracted using modulo 10 (n % 10 gives the last digit)
--   3. Integer division by 10 (n / 10) removes the last digit
--   4. The digit sum satisfies a recurrence: digitSum(n) = (n % 10) + digitSum(n / 10)
--   5. Base case: for n < 10, the digit sum is n itself (single digit)
--   6. Edge cases:
--      - n = 0: result should be 0
--      - Single digit n: result equals n itself
--      - Numbers with zeros (like 1001): zeros contribute 0 to the sum
--      - Large numbers: sum can be much smaller than the number itself
--   7. Property: The result satisfies the digit sum recurrence relation
--   8. Alternative characterization: result = (Nat.digits 10 n).sum

section Specs

-- Precondition: n is a natural number (always satisfied for Nat type)
def precondition (n : Nat) :=
  True

-- Postcondition: result equals the sum of the decimal digits of n
-- Using the mathematical property that digit sum equals the sum of digits in base 10
-- Nat.digits 10 n gives the list of digits, and List.sum computes their sum
-- This is the standard mathematical definition of digit sum
def postcondition (n : Nat) (result : Nat) :=
  result = (Nat.digits 10 n).sum

end Specs

section Impl

method sumOfDigits (n: Nat)
  return (result: Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Typical multi-digit number (from problem examples)
def test1_n : Nat := 12345
def test1_Expected : Nat := 15

-- Test case 2: Zero (edge case - base case)
def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: Large number with all digits 1-9
def test3_n : Nat := 987654321
def test3_Expected : Nat := 45

-- Test case 4: Repeated same digit
def test4_n : Nat := 11111
def test4_Expected : Nat := 5

-- Test case 5: Number with zeros in the middle
def test5_n : Nat := 1001
def test5_Expected : Nat := 2

-- Test case 6: All nines (maximum digit sum for 4 digits)
def test6_n : Nat := 9999
def test6_Expected : Nat := 36

-- Test case 7: Single digit number
def test7_n : Nat := 7
def test7_Expected : Nat := 7

-- Test case 8: Power of 10 (only leading 1 contributes)
def test8_n : Nat := 1000
def test8_Expected : Nat := 1

-- Test case 9: Two digit number
def test9_n : Nat := 99
def test9_Expected : Nat := 18

-- Test case 10: Number ending in zero
def test10_n : Nat := 120
def test10_Expected : Nat := 3

-- Recommend to validate: 1, 2, 5

end TestCases
