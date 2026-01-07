import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 48: Set all odd bits of a given number.

-- Convention:
-- Bit positions in Lean are 0-indexed (LSB = position 0).
-- MBPP odd positions (1, 3, 5, ...) correspond to EVEN 0-indexed positions (0, 2, 4, ...).
-- MBPP even positions (2, 4, 6, ...) correspond to ODD 0-indexed positions (1, 3, 5, ...).
--
-- Natural language breakdown:
-- 1. We have a natural number as input
-- 2. Each number has a binary representation (sequence of bits)
-- 3. In 0-indexed notation: bits are indexed starting from position 0 (rightmost bit is position 0)
-- 4. MBPP "odd positions" (1, 3, 5, ...) = 0-indexed EVEN positions (0, 2, 4, ...)
-- 5. MBPP "even positions" (2, 4, 6, ...) = 0-indexed ODD positions (1, 3, 5, ...)
-- 6. "Set a bit" means changing that bit to 1
-- 7. The function should:
--    a. Set all bits at 0-indexed EVEN positions (0, 2, 4, ...) to 1
--    b. Keep all bits at 0-indexed ODD positions (1, 3, 5, ...) unchanged
-- 8. The result is a new number with this modified bit pattern

specdef SetOddBitsSpec

-- Helper Functions

-- Postcondition clauses
def ensures1 (n : Nat) (result : Nat) :=
  ∀ i < n.size,
    if i % 2 = 0 then
      result.testBit i = true
    else
      result.testBit i = n.testBit i

def ensures2 (n : Nat) (result : Nat) :=
  ∀ i ≥ n.size, result.testBit i = false

def_pre (n : Nat) :=
  True  -- no preconditions
def_post (n : Nat) (result : Nat) :=
  ensures1 n result ∧ ensures2 n result

specend SetOddBitsSpec

method SetOddBits (n : Nat)
  return (result : Nat)
  require SetOddBitsSpec.pre n
  ensures SetOddBitsSpec.post n result
  do
    sorry

prove_correct SetOddBits by sorry

-- Test cases for specification validation
section TestCases

-- Test case 1: Input n = 10 (binary: 1010)
-- 0-indexed positions: 3=1, 2=0, 1=1, 0=0
-- Expected transformations (set EVEN 0-indexed positions = MBPP odd positions):
--   0-indexed Position 0 (EVEN = MBPP odd): 0 → 1 (set to 1)
--   0-indexed Position 1 (ODD = MBPP even): 1 → 1 (preserved)
--   0-indexed Position 2 (EVEN = MBPP odd): 0 → 1 (set to 1)
--   0-indexed Position 3 (ODD = MBPP even): 1 → 1 (preserved)
-- Expected output: 15 (binary: 1111)
def test1_n : Nat := 10
def test1_Expected : Nat := 15

-- Test case 2: Input n = 4 (binary: 100)
-- 0-indexed positions: 2=1, 1=0, 0=0
-- Expected transformations (set EVEN 0-indexed positions = MBPP odd positions):
--   0-indexed Position 0 (EVEN = MBPP odd): 0 → 1 (set to 1)
--   0-indexed Position 1 (ODD = MBPP even): 0 → 0 (preserved)
--   0-indexed Position 2 (EVEN = MBPP odd): 1 → 1 (already 1, stays 1)
-- Expected output: 5 (binary: 101)
def test2_n : Nat := 4
def test2_Expected : Nat := 5

-- Test case 3: Input n = 0 (binary: 0)
-- bitWidth(0) = 0, so oddBitMask(0) = 0
-- 0 | 0 = 0
-- Expected output: 0
def test3_n : Nat := 0
def test3_Expected : Nat := 0

-- Test case 4: Input n = 255 (binary: 11111111)
-- All bits already set, so setting EVEN positions doesn't change anything
-- Expected output: 255 (binary: 11111111)
def test4_n : Nat := 255
def test4_Expected : Nat := 255

-- Test case 5: Input n = 85 (binary: 1010101)
-- 0-indexed positions: 6=1, 5=0, 4=1, 3=0, 2=1, 1=0, 0=1
-- 85 already has all EVEN 0-indexed positions set (0,2,4,6)
-- Setting them again doesn't change anything
-- Expected output: 85 (binary: 1010101)
def test5_n : Nat := 85
def test5_Expected : Nat := 85

-- Test case 6: Input n = 1 (binary: 1)
-- 0-indexed position 0 (EVEN = MBPP odd) is already 1
-- Expected output: 1 (binary: 1)
def test6_n : Nat := 1
def test6_Expected : Nat := 1

-- Test case 7: Input n = 8 (binary: 1000)
-- 0-indexed positions: 3=1, 2=0, 1=0, 0=0
-- Expected transformations (set EVEN 0-indexed positions):
--   Position 0 (EVEN): 0 → 1 (set to 1)
--   Position 1 (ODD): 0 → 0 (preserved)
--   Position 2 (EVEN): 0 → 1 (set to 1)
--   Position 3 (ODD): 1 → 1 (preserved)
-- Expected output: 13 (binary: 1101)
def test7_n : Nat := 8
def test7_Expected : Nat := 13

-- Test case 8: Large input n = 1024 (binary: 10000000000)
-- 0-indexed positions: 10=1, all others=0
-- Expected transformations (set EVEN 0-indexed positions = 0,2,4,6,8,10):
--   Positions 0,2,4,6,8 (EVEN): set to 1
--   Position 10 (EVEN): already 1, stays 1
--   Positions 1,3,5,7,9 (ODD): remain 0 (preserved)
-- Expected output: 1365 (binary: 10101010101)
-- Calculation: 1024 | oddBitMask(11) = 0b10000000000 | 0b01010101010 = 0b10101010101 = 1365
def test8_n : Nat := 1024
def test8_Expected : Nat := 1365

-- Note: The test cases demonstrate the specification's intended behavior:
-- 1. All EVEN 0-indexed positions (MBPP odd positions 1,3,5,...) become 1 in the result
-- 2. All ODD 0-indexed positions (MBPP even positions 2,4,6,...) retain their value from the input
-- 3. Works correctly for edge cases (0, 1, powers of 2)
-- 4. Works correctly for various bit patterns
-- 5. Handles large numbers correctly

-- Recommended test cases for validation: 1, 2, 3, 4, 5, 7

end TestCases
