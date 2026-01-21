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
    1. Given a non-empty list of natural numbers
    2. Find and return the largest element in the list
    3. The result must be an element of the list (membership property)
    4. The result must be greater than or equal to all other elements in the list
    5. For a singleton list [x], the result is x
    6. Precondition: the list must be non-empty
-/

section Specs

-- Precondition: list must be non-empty
def precondition (lst : List Nat) :=
  lst ≠ []

-- Postcondition clauses:
-- 1. The result is a member of the list
-- 2. The result is greater than or equal to all elements in the list
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

-- Test case 1: Example from problem - ascending list [1, 2, 3]
def test1_lst : List Nat := [1, 2, 3]
def test1_Expected : Nat := 3

-- Test case 2: All elements are the same [5, 5, 5]
def test2_lst : List Nat := [5, 5, 5]
def test2_Expected : Nat := 5

-- Test case 3: Maximum at the beginning [10, 1, 9]
def test3_lst : List Nat := [10, 1, 9]
def test3_Expected : Nat := 10

-- Test case 4: Singleton list [7]
def test4_lst : List Nat := [7]
def test4_Expected : Nat := 7

-- Test case 5: All zeros [0, 0, 0, 0]
def test5_lst : List Nat := [0, 0, 0, 0]
def test5_Expected : Nat := 0

-- Test case 6: Descending order [9, 7, 5, 3, 1]
def test6_lst : List Nat := [9, 7, 5, 3, 1]
def test6_Expected : Nat := 9

-- Test case 7: Maximum in the middle [1, 100, 50]
def test7_lst : List Nat := [1, 100, 50]
def test7_Expected : Nat := 100

-- Test case 8: Two element list with equal values [42, 42]
def test8_lst : List Nat := [42, 42]
def test8_Expected : Nat := 42

-- Test case 9: Large range of values [1, 1000, 500, 999]
def test9_lst : List Nat := [1, 1000, 500, 999]
def test9_Expected : Nat := 1000

-- Test case 10: Maximum at the end [3, 1, 4, 1, 5, 9]
def test10_lst : List Nat := [3, 1, 4, 1, 5, 9]
def test10_Expected : Nat := 9

-- Recommend to validate: 1, 4, 7

end TestCases
