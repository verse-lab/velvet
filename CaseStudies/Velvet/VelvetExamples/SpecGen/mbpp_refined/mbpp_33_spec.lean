import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 33: Convert a decimal number to binary representation
--
-- Natural language breakdown:
-- 1. We need to convert a natural number from decimal (base 10) to binary (base 2)
-- 2. Binary representation is a list of bits (0s and 1s) in a specific order
-- 3. The binary representation should represent the same numeric value as the decimal input
-- 4. For any natural number n, its binary representation is unique
-- 5. The binary representation should be in big-endian format (most significant bit first)
-- 6. Edge cases:
--    - 0 should map to [0]
--    - 1 should map to [1]
--    - Powers of 2 have exactly one '1' bit followed by zeros
-- 7. The binary representation must be minimal (no leading zeros except for the number 0)
-- 8. Property-oriented specification: we define what makes a binary representation correct,
--    not how to compute it
--
-- Key properties of a correct binary representation:
-- A. Each digit in the result is either 0 or 1
-- B. The list of bits, when interpreted as a binary number, equals the input decimal number
-- C. For non-zero numbers, there are no leading zeros (the first bit must be 1)
-- D. For zero, the representation is exactly [0]

-- Helper function: convert a list of binary digits to its decimal value
-- This computes the value by treating the list as big-endian (most significant bit first)

section Specs

-- Helper Functions

def binaryToDecimal (bits: List Nat) : Nat :=
  bits.foldl (fun acc bit => 2 * acc + bit) 0

-- Helper predicate: all elements in list are valid binary digits (0 or 1)
def allBinaryDigits (bits: List Nat) : Prop :=
  ∀ b ∈ bits, b = 0 ∨ b = 1

-- Helper predicate: check if representation has no leading zeros (except for [0])
def noLeadingZeros (bits: List Nat) : Prop :=
  bits = [0] ∨ (bits.length > 0 ∧ bits.head? = some 1)

-- Postcondition clauses
def ensures1 (n : Nat) (binary : List Nat) :=
  allBinaryDigits binary  -- All elements are 0 or 1
def ensures2 (n : Nat) (binary : List Nat) :=
  binaryToDecimal binary = n  -- The binary representation equals the decimal input
def ensures3 (n : Nat) (binary : List Nat) :=
  noLeadingZeros binary  -- No leading zeros (except for n=0)
def ensures4 (n : Nat) (binary : List Nat) :=
  binary.length > 0  -- Result is never empty

def precondition (n : Nat) :=
  True  -- no preconditions
def postcondition (n : Nat) (binary : List Nat) :=
  ensures1 n binary ∧
  ensures2 n binary ∧
  ensures3 n binary ∧
  ensures4 n binary

end Specs

method DecimalToBinary (n: Nat)
  return (binary: List Nat)
  require precondition n
  ensures postcondition n binary
  do
    sorry

prove_correct DecimalToBinary by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0
def test0_n : Nat := 10
def test0_Expected : List Nat := [1, 0, 1, 0]

-- Test case 1
def test1_n : Nat := 0
def test1_Expected : List Nat := [0]

-- Test case 2
def test2_n : Nat := 1
def test2_Expected : List Nat := [1]

-- Test case 3
def test3_n : Nat := 2
def test3_Expected : List Nat := [1, 0]

-- Test case 4
def test4_n : Nat := 3
def test4_Expected : List Nat := [1, 1]

-- Test case 5
def test5_n : Nat := 4
def test5_Expected : List Nat := [1, 0, 0]

-- Test case 6
def test6_n : Nat := 5
def test6_Expected : List Nat := [1, 0, 1]

-- Test case 7
def test7_n : Nat := 7
def test7_Expected : List Nat := [1, 1, 1]

-- Test case 8
def test8_n : Nat := 8
def test8_Expected : List Nat := [1, 0, 0, 0]

-- Test case 9
def test9_n : Nat := 10
def test9_Expected : List Nat := [1, 0, 1, 0]

-- Test case 10
def test10_n : Nat := 15
def test10_Expected : List Nat := [1, 1, 1, 1]

-- Test case 11
def test11_n : Nat := 16
def test11_Expected : List Nat := [1, 0, 0, 0, 0]

-- Test case 12
def test12_n : Nat := 31
def test12_Expected : List Nat := [1, 1, 1, 1, 1]

-- Test case 13
def test13_n : Nat := 64
def test13_Expected : List Nat := [1, 0, 0, 0, 0, 0, 0]

-- Test case 14
def test14_n : Nat := 100
def test14_Expected : List Nat := [1, 1, 0, 0, 1, 0, 0]

-- Test case 15
def test15_n : Nat := 255
def test15_Expected : List Nat := [1, 1, 1, 1, 1, 1, 1, 1]

-- Test case 16
def test16_n : Nat := 256
def test16_Expected : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0]

-- Test case 17
def test17_n : Nat := 1000
def test17_Expected : List Nat := [1, 1, 1, 1, 1, 0, 1, 0, 0, 0]

-- Test case 18
def test18_n : Nat := 1023
def test18_Expected : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

-- Test case 19
def test19_n : Nat := 1024
def test19_Expected : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- Test case 20
def test20_n : Nat := 65535
def test20_Expected : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

-- Recommend to validate: 1,2,3,9,17,20

end TestCases
