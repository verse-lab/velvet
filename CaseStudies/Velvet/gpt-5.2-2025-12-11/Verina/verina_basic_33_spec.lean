import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    verina_basic_33: Return the smallest natural number missing from a sorted list of natural numbers.

    Natural language breakdown:
    1. The input is a list s : List Nat.
    2. The input list is assumed to be sorted in non-decreasing order.
    3. The result r : Nat is the smallest natural number (starting from 0) that does not appear in s.
    4. Therefore, r is not a member of s.
    5. Every natural number m smaller than r must appear in s.
    6. These two properties uniquely determine r because Nat is well-ordered.
-/

section Specs

-- Helper: predicate that a number is missing from the list
-- Using standard membership notation (List.instMembership).
def MissingFrom (s : List Nat) (n : Nat) : Prop := n ∉ s

-- Precondition: input list is sorted in non-decreasing order.
def precondition (s : List Nat) : Prop :=
  s.Sorted (· ≤ ·)

-- Postcondition: result is the least natural number not in s.
-- Characterization:
-- (1) result is missing from s
-- (2) every smaller number is present in s
def postcondition (s : List Nat) (result : Nat) : Prop :=
  MissingFrom s result ∧
  (∀ m : Nat, m < result → m ∈ s)

end Specs

section Impl

method smallestMissingNumber (s : List Nat)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
  pure 0  -- placeholder body

end Impl

section TestCases

-- Test case 1: example from prompt
-- s = [0, 1, 2, 6, 9] => smallest missing is 3
def test1_s : List Nat := [0, 1, 2, 6, 9]
def test1_Expected : Nat := 3

-- Test case 2: list starts above 0 => missing is 0
def test2_s : List Nat := [4, 5, 10, 11]
def test2_Expected : Nat := 0

-- Test case 3: complete prefix from 0 to 5 => missing is 6
def test3_s : List Nat := [0, 1, 2, 3, 4, 5]
def test3_Expected : Nat := 6

-- Test case 4: empty list => missing is 0
def test4_s : List Nat := []
def test4_Expected : Nat := 0

-- Test case 5: gap at 1
def test5_s : List Nat := [0, 2, 3, 4]
def test5_Expected : Nat := 1

-- Test case 6: single element [0] => missing is 1
def test6_s : List Nat := [0]
def test6_Expected : Nat := 1

-- Test case 7: duplicates allowed, still least missing
def test7_s : List Nat := [0, 0, 1, 1, 3]
def test7_Expected : Nat := 2

-- Test case 8: long initial gap (no 0)
def test8_s : List Nat := [2, 2, 2]
def test8_Expected : Nat := 0

-- Test case 9: missing in middle with duplicates
def test9_s : List Nat := [0, 1, 1, 2, 4, 4]
def test9_Expected : Nat := 3

-- Recommend to validate: 1, 3, 7

end TestCases
