import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- firstEvenOddDifference: Find the difference between the first even and first odd number in an array
--
-- Natural language breakdown:
-- 1. We are given an array of integers
-- 2. We need to find the FIRST even number in the array (leftmost even number when scanning from left to right)
-- 3. We need to find the FIRST odd number in the array (leftmost odd number when scanning from left to right)
-- 4. We return the difference calculated as (first even number) - (first odd number)
-- 5. The array is guaranteed to be non-empty and contain at least one even and one odd number
--
-- Key properties:
-- - Even number: divisible by 2 (n % 2 = 0)
-- - Odd number: not divisible by 2 (n % 2 ≠ 0)
-- - "First" means the leftmost occurrence when scanning from index 0
-- - Result is an integer (can be negative, zero, or positive)
--
-- Examples:
-- - [2, 3, 4, 5]: first even = 2 (index 0), first odd = 3 (index 1), result = 2 - 3 = -1
-- - [1, 4, 6, 8]: first even = 4 (index 1), first odd = 1 (index 0), result = 4 - 1 = 3
-- - [7, 2, 9, 4]: first even = 2 (index 1), first odd = 7 (index 0), result = 2 - 7 = -5

section Specs

-- Helper: Check if integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Helper: Check if integer is odd
def isOdd (n : Int) : Prop := n % 2 ≠ 0

-- Helper: Check if index i contains the first even number in array
def isFirstEvenAt (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧
  isEven a[i]! ∧
  ∀ j : Nat, j < i → ¬isEven a[j]!

-- Helper: Check if index j contains the first odd number in array
def isFirstOddAt (a : Array Int) (j : Nat) : Prop :=
  j < a.size ∧
  isOdd a[j]! ∧
  ∀ k : Nat, k < j → ¬isOdd a[k]!

-- Precondition: array contains at least one even and one odd number
def require1 (a : Array Int) :=
  ∃ x ∈ a, isEven x

def require2 (a : Array Int) :=
  ∃ x ∈ a, isOdd x

-- Postcondition: result is the difference between first even and first odd
def ensures1 (a : Array Int) (result : Int) :=
  ∃ i j : Nat,
    isFirstEvenAt a i ∧
    isFirstOddAt a j ∧
    result = a[i]! - a[j]!

def precondition (a : Array Int) :=
  require1 a ∧ require2 a

def postcondition (a : Array Int) (result : Int) :=
  ensures1 a result

end Specs

section Impl

method firstEvenOddDifference (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: First even at index 0, first odd at index 1
def test1_a : Array Int := #[2, 3, 4, 5]
def test1_Expected : Int := -1

-- Test case 2: First odd at index 0, first even at index 1
def test2_a : Array Int := #[1, 4, 6, 8]
def test2_Expected : Int := 3

-- Test case 3: First odd at index 0, first even at index 1 (negative result)
def test3_a : Array Int := #[7, 2, 9, 4]
def test3_Expected : Int := -5

-- Test case 4: Duplicate evens and odds
def test4_a : Array Int := #[2, 2, 3, 3]
def test4_Expected : Int := -1

-- Test case 5: First odd before first even with duplicates
def test5_a : Array Int := #[1, 1, 2, 2]
def test5_Expected : Int := 1

-- Test case 6: Negative numbers
def test6_a : Array Int := #[-4, -3, 2, 5]
def test6_Expected : Int := -1

-- Test case 7: First even and first odd are adjacent (even first)
def test7_a : Array Int := #[0, 1]
def test7_Expected : Int := -1

-- Test case 8: Large difference
def test8_a : Array Int := #[100, 1, 50, 3]
def test8_Expected : Int := 99

-- Test case 9: Negative odd, positive even
def test9_a : Array Int := #[-5, 4, 6, 8]
def test9_Expected : Int := 9

-- Test case 10: Zero as first even
def test10_a : Array Int := #[0, 7, 2, 3]
def test10_Expected : Int := -7

-- Recommend to validate: 1, 2, 3

end TestCases
