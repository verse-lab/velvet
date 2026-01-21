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
    BubbleSort: Sort an array of integers in non-decreasing order, preserving the multiset of elements.
    Natural language breakdown:
    1. Input is an array of integers; it may be empty or non-empty.
    2. Output is an array of integers with the same size as the input.
    3. Output is sorted in non-decreasing order: for any indices i < j within bounds,
       output[i]! ≤ output[j]!. 
    4. Output is a rearrangement (permutation) of the input: it contains exactly the same elements
       with the same multiplicities (multiset/bag of elements is preserved).
    5. No special preconditions are required; the function must handle all arrays.
-/

section Specs

-- Helper: array sortedness in non-decreasing order (index-based, using safe access `a[i]!`).
-- This is the direct requirement from the prompt.
def arraySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- Helper: multiset preservation encoded via List permutation.
-- `List.Perm` is in Mathlib and avoids needing `List.toMultiset`.
def arrayPerm (a : Array Int) (b : Array Int) : Prop :=
  a.toList.Perm b.toList

-- No preconditions.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  arraySorted result ∧
  arrayPerm a result

end Specs

section Impl

method BubbleSort (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
    pure a  -- placeholder body

end Impl

section TestCases

-- Test case 1: example from prompt (reverse sorted)
def test1_a : Array Int := #[5, 4, 3, 2, 1]
def test1_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 2: already sorted
def test2_a : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 3: duplicates and unsorted
def test3_a : Array Int := #[3, 1, 2, 1, 5]
def test3_Expected : Array Int := #[1, 1, 2, 3, 5]

-- Test case 4: singleton
def test4_a : Array Int := #[10]
def test4_Expected : Array Int := #[10]

-- Test case 5: multiple duplicates
def test5_a : Array Int := #[4, 4, 4, 2, 2, 8]
def test5_Expected : Array Int := #[2, 2, 4, 4, 4, 8]

-- Test case 6: empty array
def test6_a : Array Int := #[]
def test6_Expected : Array Int := #[]

-- Test case 7: contains negative and positive values
def test7_a : Array Int := #[-2, 0, 5, -1]
def test7_Expected : Array Int := #[-2, -1, 0, 5]

-- Test case 8: all elements equal
def test8_a : Array Int := #[7, 7, 7]
def test8_Expected : Array Int := #[7, 7, 7]

-- Test case 9: two elements swapped
def test9_a : Array Int := #[2, 1]
def test9_Expected : Array Int := #[1, 2]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 7

end TestCases
