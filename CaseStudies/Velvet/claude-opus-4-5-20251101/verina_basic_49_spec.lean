import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findFirstOdd: Find the first odd number in an array of integers
    Natural language breakdown:
    1. We are given an array of integers
    2. We need to find the index of the first odd number in the array
    3. An integer is odd if it is not divisible by 2 (i.e., n % 2 ≠ 0)
    4. If an odd number exists, return Some(index) where index is the smallest index with an odd number
    5. If no odd number exists, return None
    6. The result should be the smallest index i such that a[i] is odd
    7. For any index j < i, a[j] must be even (not odd)
    8. Edge cases:
       - Array with all even numbers: return None
       - Array with odd number at index 0: return Some(0)
       - Array with odd number in the middle: return Some(that index)
       - Single element array (odd): return Some(0)
       - Single element array (even): return None
-/

section Specs

-- Helper: Check if an integer is odd
def isOddInt (n : Int) : Prop := n % 2 ≠ 0

-- Helper: Check if an integer is even
def isEvenInt (n : Int) : Prop := n % 2 = 0

-- Precondition: array must be non-empty
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: characterizes the result
def postcondition (a : Array Int) (result : Option Nat) :=
  match result with
  | none =>
      -- No odd number exists in the array
      ∀ i : Nat, i < a.size → isEvenInt a[i]!
  | some idx =>
      -- idx is a valid index with an odd number
      idx < a.size ∧
      isOddInt a[idx]! ∧
      -- idx is the smallest such index (all elements before are even)
      (∀ j : Nat, j < idx → isEvenInt a[j]!)

end Specs

section Impl

method findFirstOdd (a : Array Int)
  return (result : Option Nat)
  require precondition a
  ensures postcondition a result
  do
  pure none

end Impl

section TestCases

-- Test case 1: All even numbers, no odd found
def test1_a : Array Int := #[2, 4, 6, 8]
def test1_Expected : Option Nat := none

-- Test case 2: First element is odd
def test2_a : Array Int := #[3, 4, 6, 8]
def test2_Expected : Option Nat := some 0

-- Test case 3: Odd number in the middle
def test3_a : Array Int := #[2, 4, 5, 8]
def test3_Expected : Option Nat := some 2

-- Test case 4: Single odd element
def test4_a : Array Int := #[7]
def test4_Expected : Option Nat := some 0

-- Test case 5: Single even element
def test5_a : Array Int := #[2]
def test5_Expected : Option Nat := none

-- Test case 6: Multiple odd numbers, return first
def test6_a : Array Int := #[1, 2, 3]
def test6_Expected : Option Nat := some 0

-- Test case 7: Odd at last position
def test7_a : Array Int := #[2, 4, 6, 7]
def test7_Expected : Option Nat := some 3

-- Test case 8: Negative odd number
def test8_a : Array Int := #[2, 4, -3, 8]
def test8_Expected : Option Nat := some 2

-- Test case 9: Mixed negative and positive, first is negative odd
def test9_a : Array Int := #[-5, 2, 3, 4]
def test9_Expected : Option Nat := some 0

-- Test case 10: Zero is even
def test10_a : Array Int := #[0, 0, 1]
def test10_Expected : Option Nat := some 2

-- Recommend to validate: 1, 2, 3

end TestCases
