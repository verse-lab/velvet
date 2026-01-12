import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LastDigitFactorialDivision: Find the last digit when factorial of a divides factorial of b
    Natural language breakdown:
    1. Given two natural numbers a and b where a ≤ b, compute b! / a!
    2. The division b! / a! = b × (b-1) × ... × (a+1) when a < b
    3. When a = b, the result is 1
    4. We need to find the last digit (ones place) of this quotient
    5. The last digit is the result modulo 10
    6. Since b! = a! × (a+1) × (a+2) × ... × b, we have b! / a! = (a+1) × (a+2) × ... × b
    7. This is always an integer when a ≤ b (factorial division property)
    8. The last digit only depends on the last digits of factors in the product
    9. Edge cases:
       - When a = b: result is 1, last digit is 1
       - When a = 0: result is b!, need last digit of b!
       - Large values: only track last digit through multiplication
    10. For the example a=2, b=4: 4!/2! = (3×4) = 12, last digit is 2
-/

-- Helper Functions

-- Compute the factorial of a natural number

section Specs

-- Helper Functions

register_specdef_allow_recursion

def factorial (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- Get the last digit (ones place) of a natural number
def lastDigit (n: Nat) : Nat :=
  n % 10

-- Compute the quotient of two factorials: b! / a!
def factorialQuotient (a b: Nat) : Nat :=
  factorial b / factorial a

-- Postcondition clauses
def ensures1 (a : Nat) (b : Nat) (result : Nat) :=
  result = lastDigit (factorialQuotient a b)
def ensures2 (a : Nat) (b : Nat) (result : Nat) :=
  result < 10

def precondition (a : Nat) (b : Nat) :=
  True
def postcondition (a : Nat) (b : Nat) (result : Nat) :=
  ensures1 a b result ∧
  ensures2 a b result

end Specs

method LastDigitFactorialDiv (a: Nat) (b: Nat)
  return (result: Nat)
  require precondition a b
  ensures postcondition a b result
  do
    sorry

prove_correct LastDigitFactorialDiv by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_a : Nat := 2
def test1_b : Nat := 4
def test1_Expected : Nat := 2

-- Test case 2: Equal values (a = b)
def test2_a : Nat := 5
def test2_b : Nat := 5
def test2_Expected : Nat := 1

-- Test case 3: Starting from 0
def test3_a : Nat := 0
def test3_b : Nat := 3
def test3_Expected : Nat := 6

-- Test case 4: Starting from 0, larger factorial
def test4_a : Nat := 0
def test4_b : Nat := 5
def test4_Expected : Nat := 0

-- Test case 5: Small consecutive numbers
def test5_a : Nat := 3
def test5_b : Nat := 5
def test5_Expected : Nat := 0

-- Test case 6: Larger range
def test6_a : Nat := 1
def test6_b : Nat := 6
def test6_Expected : Nat := 0

-- Test case 7: Single increment
def test7_a : Nat := 4
def test7_b : Nat := 5
def test7_Expected : Nat := 5

-- Test case 8: Larger single increment
def test8_a : Nat := 9
def test8_b : Nat := 10
def test8_Expected : Nat := 0

-- Test case 9: From 1 to small number
def test9_a : Nat := 1
def test9_b : Nat := 4
def test9_Expected : Nat := 4

-- Test case 10: Medium range
def test10_a : Nat := 2
def test10_b : Nat := 6
def test10_Expected : Nat := 0

-- Test case 11: From 3 to 6
def test11_a : Nat := 3
def test11_b : Nat := 6
def test11_Expected : Nat := 0

-- Test case 12: Large equal values
def test12_a : Nat := 100
def test12_b : Nat := 100
def test12_Expected : Nat := 1

-- Test case 13: Consecutive in upper range
def test13_a : Nat := 7
def test13_b : Nat := 8
def test13_Expected : Nat := 8

-- Test case 14: From 0 to 1
def test14_a : Nat := 0
def test14_b : Nat := 1
def test14_Expected : Nat := 1

-- Test case 15: From 0 to 2
def test15_a : Nat := 0
def test15_b : Nat := 2
def test15_Expected : Nat := 2

-- Recommend to validate: test cases 1, 2, 3, 5, 7, 9
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Equal values (trivial case, result = 1)
-- - Test 3: From 0 to small number (3! = 6)
-- - Test 5: Mid-range with result ending in 0
-- - Test 7: Single increment (result equals b)
-- - Test 9: From 1 to 4 (result = 4! = 24, last digit 4)

end TestCases
