import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 24: Convert a binary number to its decimal equivalent
--
-- Natural language breakdown:
-- 1. We have a binary number represented as a natural number (e.g., 100 represents binary "100")
-- 2. Each digit in the binary representation is either 0 or 1
-- 3. To convert binary to decimal, we use positional notation with base 2
-- 4. For binary number with digits d_n, d_{n-1}, ..., d_1, d_0 (from left to right),
--    the decimal value is: d_n * 2^n + d_{n-1} * 2^{n-1} + ... + d_1 * 2^1 + d_0 * 2^0
-- 5. Example: binary "100" = 1*2^2 + 0*2^1 + 0*2^0 = 4 + 0 + 0 = 4
-- 6. Example: binary "1011" = 1*2^3 + 0*2^2 + 1*2^1 + 1*2^0 = 8 + 0 + 2 + 1 = 11
-- 7. Special case: binary "0" = 0 in decimal
-- 8. The input is a natural number where each digit must be 0 or 1 (valid binary)
-- 9. Invalid binary numbers (containing digits >= 2) should be considered as precondition violations
--
-- Specification approach:
-- - Use property-oriented specification: define the mathematical relationship between binary and decimal
-- - Extract digits from the binary representation and ensure each is either 0 or 1
-- - The postcondition relates the result to the mathematical sum of (digit * 2^position)
-- - This allows any correct implementation (iterative, recursive, etc.) to be verified
-- Helper function to extract the digits of a binary string in reverse order
-- For example: "1011" -> [1, 1, 0, 1]

section Specs

-- Helper Functions

-- Helper function to check if all characters in string are '0' or '1'
def isValidBinaryStr (s: String) : Prop :=
  ∀ c ∈ s.toList, c = '0' ∨ c = '1'

def bitAt (s : String) (k : Nat) : Bool :=
  s.toList[s.length - 1 - k]! = '1'

def require1 (binary : String) :=
  isValidBinaryStr binary

-- Postcondition clauses
def ensures1 (binary : String) (decimal : Nat) :=
  ∀ k < binary.length,
    decimal.testBit k = bitAt binary k

def ensures2 (binary : String) (decimal : Nat) :=
  ∀ k ≥ binary.length,
    decimal.testBit k = false

def precondition (binary : String) :=
  require1 binary
def postcondition (binary : String) (decimal : Nat) :=
  ensures1 binary decimal ∧ ensures2 binary decimal

end Specs

method BinaryStrToDecimal (binary: String)
  return (decimal: Nat)
  require precondition binary
  ensures postcondition binary decimal
  do
    sorry

prove_correct BinaryStrToDecimal by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0: From problem description (sample)
def test0_binary : String := "100"
def test0_Expected : Nat := 4

-- Test case 1: Edge case - binary "0"
def test1_binary : String := "0"
def test1_Expected : Nat := 0

-- Test case 2: Minimal binary - binary "1"
def test2_binary : String := "1"
def test2_Expected : Nat := 1

-- Test case 3: Binary "10" (power of 2)
def test3_binary : String := "10"
def test3_Expected : Nat := 2

-- Test case 4: Binary "11" (consecutive ones)
def test4_binary : String := "11"
def test4_Expected : Nat := 3

-- Test case 5: Binary "101" (mixed bits)
def test5_binary : String := "101"
def test5_Expected : Nat := 5

-- Test case 6: Binary "110"
def test6_binary : String := "110"
def test6_Expected : Nat := 6

-- Test case 7: Binary "111" (all ones in 3 bits)
def test7_binary : String := "111"
def test7_Expected : Nat := 7

-- Test case 8: Binary "1000" (power of 2)
def test8_binary : String := "1000"
def test8_Expected : Nat := 8

-- Test case 9: Binary "1011"
def test9_binary : String := "1011"
def test9_Expected : Nat := 11

-- Test case 10: Binary "10000"
def test10_binary : String := "10000"
def test10_Expected : Nat := 16

-- Test case 11: Binary "11111" (5-bit all ones)
def test11_binary : String := "11111"
def test11_Expected : Nat := 31

-- Test case 12: Binary "100000"
def test12_binary : String := "100000"
def test12_Expected : Nat := 32

-- Test case 13: Binary "101010" (alternating bits)
def test13_binary : String := "101010"
def test13_Expected : Nat := 42

-- Test case 14: Binary "1111111" (7-bit all ones)
def test14_binary : String := "1111111"
def test14_Expected : Nat := 127

-- Test case 15: Binary "11111111" (8-bit all ones)
def test15_binary : String := "11111111"
def test15_Expected : Nat := 255

-- Test case 16: Binary "100000000" (2^8)
def test16_binary : String := "100000000"
def test16_Expected : Nat := 256

-- Test case 17: Binary "10101010101" (11-bit alternating)
def test17_binary : String := "10101010101"
def test17_Expected : Nat := 1365

-- Test case 18: Binary "1111111111" (10-bit all ones)
def test18_binary : String := "1111111111"
def test18_Expected : Nat := 1023

-- Test case 19: Binary "10000000000" (2^10)
def test19_binary : String := "10000000000"
def test19_Expected : Nat := 1024

-- Recommend to validate: test cases 0, 1, 2, 3, 13, 18, 19

end TestCases
