import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LinearSearch: Find the index of the first occurrence of a target element in an array
    Natural language breakdown:
    1. We are given an array of integers and a target integer to search for
    2. We need to find the index of the first occurrence of the target in the array
    3. "First occurrence" means the smallest index i such that a[i] = e
    4. If the target is found at index i, all elements before i must be different from the target
    5. If the target is not present in the array, return the size of the array
    6. Key properties:
       a. If result < a.size, then a[result] = e (found the target)
       b. If result < a.size, then for all i < result, a[i] ≠ e (it's the first occurrence)
       c. If result = a.size, then the target is not in the array (for all i < a.size, a[i] ≠ e)
    7. Edge cases:
       - Empty array: return 0 (which equals the size)
       - Target at first position: return 0
       - Target at last position: return a.size - 1
       - Multiple occurrences: return index of first one
       - Target not in array: return a.size
-/

section Specs

-- Precondition: No restrictions on input
def precondition (a : Array Int) (e : Int) :=
  True

-- Postcondition clauses
-- ensures1: result is at most the size of the array
def ensures1 (a : Array Int) (e : Int) (result : Nat) :=
  result ≤ a.size

-- ensures2: if result < a.size, then the element at result equals the target
def ensures2 (a : Array Int) (e : Int) (result : Nat) :=
  result < a.size → a[result]! = e

-- ensures3: all elements before result are different from the target (first occurrence property)
def ensures3 (a : Array Int) (e : Int) (result : Nat) :=
  ∀ i : Nat, i < result → a[i]! ≠ e

-- ensures4: if result = a.size, then target is not in the array
def ensures4 (a : Array Int) (e : Int) (result : Nat) :=
  result = a.size → ∀ i : Nat, i < a.size → a[i]! ≠ e

def postcondition (a : Array Int) (e : Int) (result : Nat) :=
  ensures1 a e result ∧
  ensures2 a e result ∧
  ensures3 a e result ∧
  ensures4 a e result

end Specs

section Impl

method LinearSearch (a : Array Int) (e : Int)
  return (result : Nat)
  require precondition a e
  ensures postcondition a e result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Target in the middle of the array (from problem example)
def test1_a : Array Int := #[1, 3, 5, 7, 9]
def test1_e : Int := 5
def test1_Expected : Nat := 2

-- Test case 2: Target not in array (from problem example)
def test2_a : Array Int := #[2, 4, 6, 8]
def test2_e : Int := 5
def test2_Expected : Nat := 4

-- Test case 3: Multiple occurrences, return first (from problem example)
def test3_a : Array Int := #[5, 5, 5]
def test3_e : Int := 5
def test3_Expected : Nat := 0

-- Test case 4: Target at first position (from problem example)
def test4_a : Array Int := #[10, 9, 8, 7]
def test4_e : Int := 10
def test4_Expected : Nat := 0

-- Test case 5: Multiple occurrences in middle (from problem example)
def test5_a : Array Int := #[1, 2, 3, 3, 4]
def test5_e : Int := 3
def test5_Expected : Nat := 2

-- Test case 6: Empty array
def test6_a : Array Int := #[]
def test6_e : Int := 5
def test6_Expected : Nat := 0

-- Test case 7: Single element array, target found
def test7_a : Array Int := #[42]
def test7_e : Int := 42
def test7_Expected : Nat := 0

-- Test case 8: Single element array, target not found
def test8_a : Array Int := #[42]
def test8_e : Int := 7
def test8_Expected : Nat := 1

-- Test case 9: Target at last position
def test9_a : Array Int := #[1, 2, 3, 4, 5]
def test9_e : Int := 5
def test9_Expected : Nat := 4

-- Test case 10: Array with negative numbers
def test10_a : Array Int := #[-3, -1, 0, 1, 3]
def test10_e : Int := -1
def test10_Expected : Nat := 1

-- Recommend to validate: 1, 2, 3

end TestCases
