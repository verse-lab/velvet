import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- smallestMissing: Find the first missing natural number in an increasingly sorted list
--
-- Natural language breakdown:
-- 1. The input is a list of natural numbers sorted in strictly increasing order
-- 2. We need to find the smallest natural number that is NOT in the list
-- 3. All natural numbers smaller than the result must be present in the list
-- 4. For example: [0, 1, 2, 4, 5] is missing 3, so result is 3
-- 5. For [1, 2, 3, 4], 0 is not present, so result is 0
-- 6. For [], no elements exist, so result is 0
-- 7. For [0, 1, 2, 3, 4], all from 0-4 are present, so result is 5
-- 8. Key properties:
--    a. The list must be sorted in strictly increasing order (no duplicates)
--    b. The result is not a member of the list
--    c. All natural numbers less than the result are members of the list
-- 9. The result is uniquely determined by these properties

section Specs

-- Helper definition: check if list is sorted in strictly increasing order
def isStrictlySorted (l : List Nat) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! < l[j]!

-- Precondition: list must be sorted in strictly increasing order
def precondition (l : List Nat) : Prop :=
  isStrictlySorted l

-- Postcondition clauses
-- 1. The result is not in the list
def ensures1 (l : List Nat) (result : Nat) : Prop :=
  result ∉ l

-- 2. All natural numbers less than result are in the list
def ensures2 (l : List Nat) (result : Nat) : Prop :=
  ∀ k : Nat, k < result → k ∈ l

def postcondition (l : List Nat) (result : Nat) : Prop :=
  ensures1 l result ∧ ensures2 l result

end Specs

section Impl

method smallestMissing (l : List Nat)
  return (result : Nat)
  require precondition l
  ensures postcondition l result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: List with gap in the middle [0, 1, 2, 4, 5] -> missing 3
def test1_l : List Nat := [0, 1, 2, 4, 5]
def test1_Expected : Nat := 3

-- Test case 2: Empty list -> missing 0
def test2_l : List Nat := []
def test2_Expected : Nat := 0

-- Test case 3: List starting from 1 (missing 0) [1, 2, 3, 4] -> missing 0
def test3_l : List Nat := [1, 2, 3, 4]
def test3_Expected : Nat := 0

-- Test case 4: Complete sequence from 0 [0, 1, 2, 3, 4] -> missing 5
def test4_l : List Nat := [0, 1, 2, 3, 4]
def test4_Expected : Nat := 5

-- Test case 5: List not starting from 0 [2, 3, 4, 5, 6] -> missing 0
def test5_l : List Nat := [2, 3, 4, 5, 6]
def test5_Expected : Nat := 0

-- Test case 6: Single element 0 [0] -> missing 1
def test6_l : List Nat := [0]
def test6_Expected : Nat := 1

-- Test case 7: Single element not 0 [5] -> missing 0
def test7_l : List Nat := [5]
def test7_Expected : Nat := 0

-- Test case 8: Long complete sequence [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] -> missing 10
def test8_l : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def test8_Expected : Nat := 10

-- Test case 9: Gap at the beginning then complete [0, 2, 3, 4, 5] -> missing 1
def test9_l : List Nat := [0, 2, 3, 4, 5]
def test9_Expected : Nat := 1

-- Test case 10: Two elements forming complete sequence [0, 1] -> missing 2
def test10_l : List Nat := [0, 1]
def test10_Expected : Nat := 2

-- Recommend to validate: 1, 2, 4

end TestCases
