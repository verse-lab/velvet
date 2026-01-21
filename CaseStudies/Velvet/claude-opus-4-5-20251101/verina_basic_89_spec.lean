import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    SetToSeq: Transform a list with possible duplicate entries into a new list where each element appears only once, maintaining the order of its first occurrence.
    Natural language breakdown:
    1. We have a list of integers that may contain duplicate elements
    2. We need to produce a new list where each element appears exactly once
    3. The order of elements in the output should be based on their first occurrence in the input
    4. The set of elements in the output should be identical to the set of elements in the input
    5. Edge case: Empty list should return empty list
    6. Edge case: List with all same elements should return a single element list
    7. Edge case: List with all distinct elements should return the same list
-/

section Specs

-- Postcondition clause 1: Every element in the result appears in the input
def ensures1 (s : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ result → x ∈ s

-- Postcondition clause 2: Every element in the input appears in the result
def ensures2 (s : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ s → x ∈ result

-- Postcondition clause 3: The result has no duplicates
def ensures3 (result : List Int) : Prop :=
  result.Nodup

-- Postcondition clause 4: Order preservation - result is a subsequence of s
-- This ensures that the relative order of elements in result matches their order in s
def ensures4 (s : List Int) (result : List Int) : Prop :=
  result.Sublist s

def precondition (s : List Int) : Prop :=
  True  -- no preconditions

def postcondition (s : List Int) (result : List Int) : Prop :=
  ensures1 s result ∧ ensures2 s result ∧ ensures3 result ∧ ensures4 s result

end Specs

section Impl

method SetToSeq (s : List Int)
  return (result : List Int)
  require precondition s
  ensures postcondition s result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem - list with duplicates
def test1_s : List Int := [1, 2, 2, 3, 1]
def test1_Expected : List Int := [1, 2, 3]

-- Test case 2: All same elements
def test2_s : List Int := [5, 5, 5, 5]
def test2_Expected : List Int := [5]

-- Test case 3: Empty list
def test3_s : List Int := []
def test3_Expected : List Int := []

-- Test case 4: All distinct elements
def test4_s : List Int := [11, 22, 33]
def test4_Expected : List Int := [11, 22, 33]

-- Test case 5: Multiple duplicates scattered
def test5_s : List Int := [3, 1, 4, 1, 5, 9, 2, 6, 5]
def test5_Expected : List Int := [3, 1, 4, 5, 9, 2, 6]

-- Test case 6: Single element
def test6_s : List Int := [42]
def test6_Expected : List Int := [42]

-- Test case 7: Two elements, one duplicate
def test7_s : List Int := [7, 7]
def test7_Expected : List Int := [7]

-- Test case 8: Alternating duplicates
def test8_s : List Int := [1, 2, 1, 2, 1, 2]
def test8_Expected : List Int := [1, 2]

-- Test case 9: Negative numbers with duplicates
def test9_s : List Int := [-1, -2, -1, 3, -2]
def test9_Expected : List Int := [-1, -2, 3]

-- Test case 10: Large consecutive duplicates
def test10_s : List Int := [1, 1, 1, 2, 2, 2, 3, 3, 3]
def test10_Expected : List Int := [1, 2, 3]

-- Recommend to validate: 1, 2, 3

end TestCases
