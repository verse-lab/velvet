import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ArrayGCD: Find the greatest common divisor (GCD) of all elements in an array
    Natural language breakdown:
    1. Given an array of natural numbers, we need to find a single natural number that is the GCD of all elements
    2. The GCD of a set of numbers is the largest positive integer that divides all of them
    3. For an array [a₁, a₂, ..., aₙ], the result should be gcd(a₁, gcd(a₂, ... gcd(aₙ₋₁, aₙ)...))
    4. The GCD is associative and commutative, so order of computation doesn't matter
    5. GCD has these fundamental properties:
       - gcd(a, a) = a
       - gcd(a, 0) = a
       - gcd(0, a) = a
       - gcd(a, b) divides both a and b
       - Any common divisor of a and b also divides gcd(a, b)
    6. For an array, the result must divide every element in the array
    7. The result must be the largest such divisor
    8. Edge cases:
       - Empty array: undefined behavior (we require non-empty arrays)
       - Single element array: GCD is the element itself
       - Array with zeros: GCD is the GCD of non-zero elements
       - All zeros: technically undefined, but by convention we require at least one non-zero element
-/

-- Helper Functions

-- Predicate: result divides all elements in the array

specdef FindArrayGCDSpec

-- Helper Functions

def dividesAll (d: Nat) (arr: Array Nat) : Prop :=
  ∀ i, i < arr.size → d ∣ arr[i]!

-- Predicate: result is the maximum among all common divisors
def isMaximalDivisor (d: Nat) (arr: Array Nat) : Prop :=
  dividesAll d arr ∧ (∀ d', dividesAll d' arr → d' ≤ d)

def require1 (arr : Array Nat) :=
  arr.size > 0
def require2 (arr : Array Nat) :=
  ∃ i, i < arr.size ∧ arr[i]! > 0   -- At least one non-zero element

-- Postcondition clauses
def ensures1 (arr : Array Nat) (result : Nat) :=
  dividesAll result arr
def ensures2 (arr : Array Nat) (result : Nat) :=
  ∀ d, dividesAll d arr → d ≤ result

def_pre (arr : Array Nat) :=
  require1 arr ∧require2 arr
def_post (arr : Array Nat) (result : Nat) :=
  ensures1 arr result ∧
  ensures2 arr result

specend FindArrayGCDSpec

method FindArrayGCD (arr: Array Nat)
  return (result: Nat)
  require FindArrayGCDSpec.pre arr
  ensures FindArrayGCDSpec.post arr result
  do
    sorry

prove_correct FindArrayGCD by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_arr : Array Nat := #[2, 4, 6, 8, 16]
def test1_Expected : Nat := 2

-- Test case 2: Single element array
def test2_arr : Array Nat := #[42]
def test2_Expected : Nat := 42

-- Test case 3: Two coprime numbers (GCD = 1)
def test3_arr : Array Nat := #[13, 17]
def test3_Expected : Nat := 1

-- Test case 4: Multiple of same number
def test4_arr : Array Nat := #[5, 5, 5, 5]
def test4_Expected : Nat := 5

-- Test case 5: Powers of 2
def test5_arr : Array Nat := #[16, 32, 64, 128]
def test5_Expected : Nat := 16

-- Test case 6: Array with 1 (GCD must be 1)
def test6_arr : Array Nat := #[1, 100, 1000]
def test6_Expected : Nat := 1

-- Test case 7: Fibonacci-like sequence
def test7_arr : Array Nat := #[3, 6, 9, 12, 15]
def test7_Expected : Nat := 3

-- Test case 8: Large numbers with common factor
def test8_arr : Array Nat := #[1000, 2000, 3000, 4000]
def test8_Expected : Nat := 1000

-- Test case 9: Prime numbers (GCD = 1)
def test9_arr : Array Nat := #[7, 11, 13, 17, 19]
def test9_Expected : Nat := 1

-- Test case 10: Mix of small and large numbers with common divisor
def test10_arr : Array Nat := #[12, 18, 24, 30, 36]
def test10_Expected : Nat := 6

-- Test case 11: Two elements with known GCD
def test11_arr : Array Nat := #[48, 18]
def test11_Expected : Nat := 6

-- Test case 12: Large array with uniform divisor
def test12_arr : Array Nat := #[10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
def test12_Expected : Nat := 10

-- Test case 13: Array where one element is the GCD
def test13_arr : Array Nat := #[15, 30, 45, 60]
def test13_Expected : Nat := 15

-- Test case 14: Large numbers
def test14_arr : Array Nat := #[123456, 234567, 345678]
def test14_Expected : Nat := 3

-- Test case 15: Array with 0
def test15_arr : Array Nat := #[0, 12, 0, 6]
def test15_Expected : Nat := 6

-- Recommend to validate: test cases 1, 2, 3, 4, 5, 15
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Single element edge case
-- - Test 3: Coprime numbers (minimal GCD)
-- - Test 4: All identical elements
-- - Test 5: Powers of same base
-- - Test 15: Array with 0

end TestCases
