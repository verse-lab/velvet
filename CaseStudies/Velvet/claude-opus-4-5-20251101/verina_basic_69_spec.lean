import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LinearSearch: Find the index of the first occurrence of an element in an array
    Natural language breakdown:
    1. We are given an array of integers 'a' and a target element 'e'
    2. We need to find the index of the first occurrence of 'e' in 'a'
    3. The precondition requires that 'e' exists somewhere in the array
    4. The result index 'n' must satisfy:
       a. n < a.size (the index is valid)
       b. a[n]! = e (the element at index n equals the target)
       c. For all indices i < n, a[i]! ≠ e (no earlier occurrence exists)
    5. These three properties uniquely determine the result
-/

section Specs

-- Precondition: The element e must exist in the array a
def precondition (a : Array Int) (e : Int) :=
  ∃ i : Nat, i < a.size ∧ a[i]! = e

-- Postcondition: The result is the index of the first occurrence of e
-- 1. The index is valid (within bounds)
-- 2. The element at that index equals e
-- 3. All elements before that index are different from e
def postcondition (a : Array Int) (e : Int) (result : Nat) :=
  result < a.size ∧
  a[result]! = e ∧
  (∀ i : Nat, i < result → a[i]! ≠ e)

end Specs

section Impl

method LinearSearch (a: Array Int) (e: Int)
  return (result: Nat)
  require precondition a e
  ensures postcondition a e result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Element in the middle of array
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_e : Int := 3
def test1_Expected : Nat := 2

-- Test case 2: Element at the beginning of array
def test2_a : Array Int := #[10, 20, 30, 40, 50]
def test2_e : Int := 10
def test2_Expected : Nat := 0

-- Test case 3: Element at the end of array
def test3_a : Array Int := #[5, 4, 3, 2, 1]
def test3_e : Int := 1
def test3_Expected : Nat := 4

-- Test case 4: Negative element at the beginning
def test4_a : Array Int := #[-1, 0, 1, 2]
def test4_e : Int := -1
def test4_Expected : Nat := 0

-- Test case 5: Element appears multiple times, return first occurrence
def test5_a : Array Int := #[7, 8, 7, 9, 7]
def test5_e : Int := 7
def test5_Expected : Nat := 0

-- Test case 6: Single element array
def test6_a : Array Int := #[42]
def test6_e : Int := 42
def test6_Expected : Nat := 0

-- Test case 7: Two element array, find second
def test7_a : Array Int := #[1, 2]
def test7_e : Int := 2
def test7_Expected : Nat := 1

-- Test case 8: All same elements
def test8_a : Array Int := #[5, 5, 5, 5]
def test8_e : Int := 5
def test8_Expected : Nat := 0

-- Test case 9: Large negative numbers
def test9_a : Array Int := #[-100, -50, 0, 50, 100]
def test9_e : Int := 0
def test9_Expected : Nat := 2

-- Test case 10: Element appears at second to last position
def test10_a : Array Int := #[1, 2, 3, 99, 5]
def test10_e : Int := 99
def test10_Expected : Nat := 3

-- Recommend to validate: 1, 2, 5

end TestCases
