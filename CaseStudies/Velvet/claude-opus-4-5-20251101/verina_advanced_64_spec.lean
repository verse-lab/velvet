import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    removeElement: Remove all occurrences of a given element from a list of natural numbers
    Natural language breakdown:
    1. Given a list of natural numbers and a target number
    2. Return a new list containing all elements except those equal to the target
    3. The relative order of remaining elements must be preserved
    4. If the target doesn't appear in the list, return the original list unchanged
    5. If all elements equal the target, return an empty list
    6. Example: removeElement([1, 2, 3, 2, 4], 2) → [1, 3, 4]
-/

section Specs

-- Postcondition clauses

-- The result contains no occurrences of the target
def ensures1 (lst : List Nat) (target : Nat) (result : List Nat) :=
  target ∉ result

-- Every element in the result was in the original list
def ensures2 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ∈ result → x ∈ lst

-- Every non-target element in the original list appears in the result
def ensures3 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ∈ lst → x ≠ target → x ∈ result

-- The result is a sublist of the original (preserves order)
def ensures4 (lst : List Nat) (target : Nat) (result : List Nat) :=
  result.Sublist lst

-- The count of each non-target element is preserved
def ensures5 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ≠ target → result.count x = lst.count x

def precondition (lst : List Nat) (target : Nat) :=
  True  -- no preconditions needed

def postcondition (lst : List Nat) (target : Nat) (result : List Nat) :=
  ensures1 lst target result ∧
  ensures2 lst target result ∧
  ensures3 lst target result ∧
  ensures4 lst target result ∧
  ensures5 lst target result

end Specs

section Impl

method removeElement (lst : List Nat) (target : Nat)
  return (result : List Nat)
  require precondition lst target
  ensures postcondition lst target result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Basic case with multiple occurrences (from problem)
def test1_lst : List Nat := [1, 2, 3, 2, 4]
def test1_target : Nat := 2
def test1_Expected : List Nat := [1, 3, 4]

-- Test case 2: All elements are the target
def test2_lst : List Nat := [5, 5, 5, 5]
def test2_target : Nat := 5
def test2_Expected : List Nat := []

-- Test case 3: Target not in list
def test3_lst : List Nat := [7, 8, 9]
def test3_target : Nat := 4
def test3_Expected : List Nat := [7, 8, 9]

-- Test case 4: Empty list
def test4_lst : List Nat := []
def test4_target : Nat := 3
def test4_Expected : List Nat := []

-- Test case 5: Target is zero with multiple occurrences
def test5_lst : List Nat := [0, 1, 0, 2, 0]
def test5_target : Nat := 0
def test5_Expected : List Nat := [1, 2]

-- Test case 6: Single element list, element is target
def test6_lst : List Nat := [10]
def test6_target : Nat := 10
def test6_Expected : List Nat := []

-- Test case 7: Single element list, element is not target
def test7_lst : List Nat := [10]
def test7_target : Nat := 5
def test7_Expected : List Nat := [10]

-- Test case 8: Target at beginning and end
def test8_lst : List Nat := [3, 1, 2, 3]
def test8_target : Nat := 3
def test8_Expected : List Nat := [1, 2]

-- Test case 9: Consecutive targets
def test9_lst : List Nat := [1, 2, 2, 2, 3]
def test9_target : Nat := 2
def test9_Expected : List Nat := [1, 3]

-- Test case 10: Large numbers
def test10_lst : List Nat := [100, 200, 100, 300]
def test10_target : Nat := 100
def test10_Expected : List Nat := [200, 300]

-- Recommend to validate: 1, 2, 5

end TestCases
