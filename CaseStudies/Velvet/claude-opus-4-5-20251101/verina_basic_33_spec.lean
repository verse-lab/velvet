import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    smallestMissingNumber: Find the smallest natural number missing from a sorted list
    Natural language breakdown:
    1. Given a list of natural numbers sorted in non-decreasing order
    2. Find the smallest natural number (starting from 0) that does not appear in the list
    3. If 0 is not in the list, return 0
    4. If all numbers 0, 1, 2, ..., k are in the list, return k+1
    5. The result must not be in the input list
    6. All natural numbers smaller than the result must be in the input list
-/

section Specs

-- Precondition: The input list is sorted in non-decreasing order
def precondition (s : List Nat) : Prop :=
  List.Sorted (· ≤ ·) s

-- Postcondition: The result is the smallest natural number not in the list
-- Property 1: The result is not in the list
-- Property 2: All natural numbers smaller than result are in the list
def postcondition (s : List Nat) (result : Nat) : Prop :=
  result ∉ s ∧
  (∀ k : Nat, k < result → k ∈ s)

end Specs

section Impl

method smallestMissingNumber (s : List Nat)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: List with gap at position 3
def test1_s : List Nat := [0, 1, 2, 6, 9]
def test1_Expected : Nat := 3

-- Test case 2: List starting above 0
def test2_s : List Nat := [4, 5, 10, 11]
def test2_Expected : Nat := 0

-- Test case 3: Consecutive numbers from 0
def test3_s : List Nat := [0, 1, 2, 3, 4, 5]
def test3_Expected : Nat := 6

-- Test case 4: Empty list
def test4_s : List Nat := []
def test4_Expected : Nat := 0

-- Test case 5: Missing 1 in the sequence
def test5_s : List Nat := [0, 2, 3, 4]
def test5_Expected : Nat := 1

-- Test case 6: Single element 0
def test6_s : List Nat := [0]
def test6_Expected : Nat := 1

-- Test case 7: Single element not 0
def test7_s : List Nat := [5]
def test7_Expected : Nat := 0

-- Test case 8: List with duplicates
def test8_s : List Nat := [0, 0, 1, 1, 2, 2, 4]
def test8_Expected : Nat := 3

-- Test case 9: Large gap at the start
def test9_s : List Nat := [100, 101, 102]
def test9_Expected : Nat := 0

-- Test case 10: Consecutive starting from 0 with one missing in middle
def test10_s : List Nat := [0, 1, 2, 3, 5, 6, 7]
def test10_Expected : Nat := 4

-- Recommend to validate: 1, 3, 4

end TestCases
