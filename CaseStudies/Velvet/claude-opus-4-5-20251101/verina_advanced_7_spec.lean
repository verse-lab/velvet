import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- binaryToDecimal: Convert a binary number represented as a list of digits (0 or 1)
-- into its corresponding decimal value.
--
-- Natural language breakdown:
-- 1. Input is a list of natural numbers representing binary digits (each 0 or 1)
-- 2. The list is in big-endian format (most significant digit first)
-- 3. For a list of length n, the digit at position i (0-indexed from left) contributes:
--    digit[i] * 2^(n-1-i) to the total value
-- 4. Empty list should return 0
-- 5. Precondition: all digits must be either 0 or 1
-- 6. The result is uniquely determined by summing all positional contributions

section Specs

-- Check if all elements in the list are valid binary digits (0 or 1)
def allBinaryDigits (digits : List Nat) : Prop :=
  ∀ d ∈ digits, d = 0 ∨ d = 1

-- Precondition: all digits must be 0 or 1
def precondition (digits : List Nat) :=
  allBinaryDigits digits

-- Postcondition: the result equals the decimal interpretation of the binary list
-- Each digit at position i contributes digit[i] * 2^(n-1-i) to the result
-- Using testBit to characterize the result: bit position j in result equals digit at position (n-1-j)
def postcondition (digits : List Nat) (result : Nat) :=
  -- The result must satisfy the positional value property:
  -- For a binary number, each bit at position i from left contributes digit * 2^(n-1-i)
  -- This is equivalent to saying the result is bounded and matches the weighted sum
  (digits.length = 0 → result = 0) ∧
  (∀ i : Nat, i < digits.length → 
    result.testBit (digits.length - 1 - i) = (digits[i]! == 1)) ∧
  (∀ j : Nat, j ≥ digits.length → result.testBit j = false)

end Specs

section Impl

method binaryToDecimal (digits : List Nat)
  return (result : Nat)
  require precondition digits
  ensures postcondition digits result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: [1, 0, 1] -> 5 (example from problem: 1*4 + 0*2 + 1*1 = 5)
def test1_digits : List Nat := [1, 0, 1]
def test1_Expected : Nat := 5

-- Test case 2: [1, 1, 1, 1] -> 15 (8 + 4 + 2 + 1 = 15)
def test2_digits : List Nat := [1, 1, 1, 1]
def test2_Expected : Nat := 15

-- Test case 3: [0, 0, 0] -> 0 (all zeros)
def test3_digits : List Nat := [0, 0, 0]
def test3_Expected : Nat := 0

-- Test case 4: [1, 0, 0, 0, 0] -> 16 (2^4 = 16)
def test4_digits : List Nat := [1, 0, 0, 0, 0]
def test4_Expected : Nat := 16

-- Test case 5: [] -> 0 (empty list edge case)
def test5_digits : List Nat := []
def test5_Expected : Nat := 0

-- Test case 6: [1] -> 1 (single bit)
def test6_digits : List Nat := [1]
def test6_Expected : Nat := 1

-- Test case 7: [0] -> 0 (single zero bit)
def test7_digits : List Nat := [0]
def test7_Expected : Nat := 0

-- Test case 8: [1, 0, 1, 0] -> 10 (8 + 0 + 2 + 0 = 10)
def test8_digits : List Nat := [1, 0, 1, 0]
def test8_Expected : Nat := 10

-- Test case 9: [0, 1, 1] -> 3 (leading zero: 0*4 + 1*2 + 1*1 = 3)
def test9_digits : List Nat := [0, 1, 1]
def test9_Expected : Nat := 3

-- Recommend to validate: 1, 2, 5
-- Test 1: Example from problem description (must include)
-- Test 2: All ones case, good coverage
-- Test 5: Empty list edge case

end TestCases
