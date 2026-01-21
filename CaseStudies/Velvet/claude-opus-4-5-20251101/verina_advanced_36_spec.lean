import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    majorityElement: Find the majority element in a list of natural numbers
    Natural language breakdown:
    1. The majority element is defined as the element that appears more than ⌊n / 2⌋ times
    2. n is the total number of elements (length of the list)
    3. The input list is guaranteed to contain a majority element
    4. The result must be a member of the input list
    5. The count of the result in the list must be strictly greater than half the list length
    6. By definition of majority, such an element is unique when it exists
-/

section Specs

-- Precondition: list is non-empty and contains a majority element
def precondition (xs : List Nat) :=
  xs.length > 0 ∧ ∃ x ∈ xs, xs.count x > xs.length / 2

-- Postcondition: result is in the list and appears more than half the time
def postcondition (xs : List Nat) (result : Nat) :=
  result ∈ xs ∧ xs.count result > xs.length / 2

end Specs

section Impl

method majorityElement (xs : List Nat)
  return (result : Nat)
  require precondition xs
  ensures postcondition xs result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - 3 appears 5 times out of 7
def test1_xs : List Nat := [3, 3, 4, 2, 3, 3, 3]
def test1_Expected : Nat := 3

-- Test case 2: 1 appears 5 times out of 7
def test2_xs : List Nat := [1, 1, 2, 1, 3, 1, 1]
def test2_Expected : Nat := 1

-- Test case 3: 2 appears 3 times out of 5
def test3_xs : List Nat := [2, 2, 2, 1, 1]
def test3_Expected : Nat := 2

-- Test case 4: 9 appears 4 times out of 7
def test4_xs : List Nat := [9, 9, 9, 9, 1, 2, 3]
def test4_Expected : Nat := 9

-- Test case 5: 5 appears 5 times out of 7
def test5_xs : List Nat := [5, 5, 5, 5, 5, 6, 7]
def test5_Expected : Nat := 5

-- Test case 6: Single element list
def test6_xs : List Nat := [42]
def test6_Expected : Nat := 42

-- Test case 7: All same elements
def test7_xs : List Nat := [7, 7, 7, 7, 7]
def test7_Expected : Nat := 7

-- Test case 8: Majority at the minimum threshold (3 out of 5)
def test8_xs : List Nat := [1, 2, 1, 3, 1]
def test8_Expected : Nat := 1

-- Test case 9: Large majority element value
def test9_xs : List Nat := [100, 100, 100, 1, 2]
def test9_Expected : Nat := 100

-- Test case 10: Two elements with majority
def test10_xs : List Nat := [5, 5]
def test10_Expected : Nat := 5

-- Recommend to validate: 1, 3, 6

end TestCases
