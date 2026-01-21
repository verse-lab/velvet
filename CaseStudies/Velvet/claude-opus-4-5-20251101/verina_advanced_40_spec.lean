import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxOfList: Return the maximum element from a non-empty list of natural numbers
    Natural language breakdown:
    1. Given a non-empty list of natural numbers lst
    2. Find and return the largest element in the list
    3. The result must be an element of the list (membership)
    4. The result must be greater than or equal to all elements in the list
    5. These two properties uniquely determine the maximum
    6. Precondition: the list must be non-empty (lst.length > 0)
-/

section Specs

-- Precondition: list must be non-empty
def precondition (lst : List Nat) :=
  lst.length > 0

-- Postcondition: result is the maximum element
-- Property 1: result is a member of the list
-- Property 2: result is greater than or equal to all elements in the list
def postcondition (lst : List Nat) (result : Nat) :=
  result ∈ lst ∧
  ∀ x, x ∈ lst → x ≤ result

end Specs

section Impl

method maxOfList (lst : List Nat)
  return (result : Nat)
  require precondition lst
  ensures postcondition lst result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Basic increasing list [1, 2, 3] (from problem description)
def test1_lst : List Nat := [1, 2, 3]
def test1_Expected : Nat := 3

-- Test case 2: All elements same [5, 5, 5]
def test2_lst : List Nat := [5, 5, 5]
def test2_Expected : Nat := 5

-- Test case 3: Maximum at beginning [10, 1, 9]
def test3_lst : List Nat := [10, 1, 9]
def test3_Expected : Nat := 10

-- Test case 4: Single element [7]
def test4_lst : List Nat := [7]
def test4_Expected : Nat := 7

-- Test case 5: All zeros [0, 0, 0, 0]
def test5_lst : List Nat := [0, 0, 0, 0]
def test5_Expected : Nat := 0

-- Test case 6: Decreasing order [9, 7, 5, 3, 1]
def test6_lst : List Nat := [9, 7, 5, 3, 1]
def test6_Expected : Nat := 9

-- Test case 7: Maximum in middle [1, 100, 50]
def test7_lst : List Nat := [1, 100, 50]
def test7_Expected : Nat := 100

-- Test case 8: Two elements [3, 8]
def test8_lst : List Nat := [3, 8]
def test8_Expected : Nat := 8

-- Test case 9: Larger list with duplicates [4, 2, 7, 7, 1, 6]
def test9_lst : List Nat := [4, 2, 7, 7, 1, 6]
def test9_Expected : Nat := 7

-- Test case 10: Maximum at end [1, 2, 3, 4, 5]
def test10_lst : List Nat := [1, 2, 3, 4, 5]
def test10_Expected : Nat := 5

-- Recommend to validate: 1, 4, 7

end TestCases
