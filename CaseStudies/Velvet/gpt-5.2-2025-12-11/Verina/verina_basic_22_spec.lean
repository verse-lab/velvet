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
    dissimilarElements: return the sorted array of all distinct integers that occur in exactly one of the two input arrays.
    Natural language breakdown:
    1. Inputs are two arrays of integers a and b.
    2. An integer x is considered part of the result iff it appears in a or b, but not in both.
    3. The output contains no duplicate elements.
    4. The output is sorted in nondecreasing order.
    5. The order is otherwise irrelevant (but since sortedness is required, the output order is uniquely determined up to duplicates, which are forbidden).
    6. There are no restrictions on input sizes or contents (may contain duplicates, negatives, or be empty).
-/

section Specs

-- Helper: membership predicate for an Int in an Array Int
-- Uses array indexing semantics via existence of an index.
def memArray (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: output is sorted in nondecreasing order (Int ≤)
def arraySorted (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: no duplicates in an array
-- Stated via list nodup on the underlying list.
def arrayNodup (arr : Array Int) : Prop :=
  arr.toList.Nodup

-- The symmetric-difference membership condition for output array.
def symmDiffSpec (a : Array Int) (b : Array Int) (out : Array Int) : Prop :=
  ∀ (x : Int), memArray out x ↔ ((memArray a x ∧ ¬ memArray b x) ∨ (memArray b x ∧ ¬ memArray a x))

-- Preconditions: none

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postconditions: out contains exactly the symmetric difference elements, is duplicate-free, and sorted.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  symmDiffSpec a b result ∧
  arrayNodup result ∧
  arraySorted result

end Specs

section Impl

method dissimilarElements (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure (#[])

end Impl

section TestCases

-- Test case 1: example from prompt
-- a = #[1,2,3,4], b = #[3,4,5,6] => symmetric difference = {1,2,5,6}, sorted

def test1_a : Array Int := #[1, 2, 3, 4]
def test1_b : Array Int := #[3, 4, 5, 6]
def test1_Expected : Array Int := #[1, 2, 5, 6]

-- Test case 2: duplicates in input should not duplicate output

def test2_a : Array Int := #[1, 1, 2]
def test2_b : Array Int := #[2, 3]
def test2_Expected : Array Int := #[1, 3]

-- Test case 3: left empty

def test3_a : Array Int := #[]
def test3_b : Array Int := #[4, 5]
def test3_Expected : Array Int := #[4, 5]

-- Test case 4: right empty

def test4_a : Array Int := #[7, 8]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[7, 8]

-- Test case 5: identical arrays -> empty symmetric difference

def test5_a : Array Int := #[1, 2, 3]
def test5_b : Array Int := #[1, 2, 3]
def test5_Expected : Array Int := #[]

-- Test case 6: disjoint arrays -> union, sorted

def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[4, 5, 6]
def test6_Expected : Array Int := #[1, 2, 3, 4, 5, 6]

-- Test case 7: includes negative numbers and cancellation of common element

def test7_a : Array Int := #[-1, 0, 1]
def test7_b : Array Int := #[0]
def test7_Expected : Array Int := #[-1, 1]

-- Test case 8: unsorted inputs; output still must be sorted and deduped

def test8_a : Array Int := #[3, 1, 2]
def test8_b : Array Int := #[2, 4, 3]
def test8_Expected : Array Int := #[1, 4]

-- Test case 9: many duplicates and overlap

def test9_a : Array Int := #[5, 5, 5]
def test9_b : Array Int := #[5, 6, 6]
def test9_Expected : Array Int := #[6]

-- Recommend to validate: 1, 2, 7

end TestCases
