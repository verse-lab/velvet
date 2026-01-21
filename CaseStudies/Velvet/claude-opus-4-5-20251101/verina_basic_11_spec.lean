import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lastDigit: Extract the last digit of a given non-negative integer
    Natural language breakdown:
    1. Given a non-negative integer n, compute its last digit
    2. The last digit is the remainder when n is divided by 10
    3. The result must always be between 0 and 9 (inclusive)
    4. For example: lastDigit(123) = 3, lastDigit(0) = 0, lastDigit(10) = 0
    5. This is equivalent to n % 10 (modulo operation)
    6. Edge cases:
       - n = 0: last digit is 0
       - Single digit n: last digit is n itself
       - n ends in 0: last digit is 0
-/

section Specs

-- Precondition: n is a natural number (always satisfied for Nat type)
def precondition (n : Nat) :=
  True

-- Postcondition clauses
-- The result equals n modulo 10
def ensures1 (n : Nat) (result : Nat) :=
  result = n % 10

-- The result is a valid single digit (0 to 9)
def ensures2 (n : Nat) (result : Nat) :=
  result < 10

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result ∧
  ensures2 n result

end Specs

section Impl

method lastDigit (n: Nat)
  return (result: Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Typical three-digit number (example from problem)
def test1_n : Nat := 123
def test1_Expected : Nat := 3

-- Test case 2: Zero input (edge case - minimum value)
def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: Large number
def test3_n : Nat := 987654321
def test3_Expected : Nat := 1

-- Test case 4: Number ending in zero
def test4_n : Nat := 10
def test4_Expected : Nat := 0

-- Test case 5: All same digits (9s)
def test5_n : Nat := 999
def test5_Expected : Nat := 9

-- Test case 6: Two-digit number
def test6_n : Nat := 45
def test6_Expected : Nat := 5

-- Test case 7: Multiple zeros at end
def test7_n : Nat := 100
def test7_Expected : Nat := 0

-- Test case 8: Single digit number (edge case)
def test8_n : Nat := 5
def test8_Expected : Nat := 5

-- Recommend to validate: 1, 2, 8

end TestCases
