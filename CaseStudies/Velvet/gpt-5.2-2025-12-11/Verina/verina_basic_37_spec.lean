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
    findFirstOccurrence: locate the first occurrence index of a target integer in a sorted array.
    Natural language breakdown:
    1. Input is an array of integers `arr` and an integer `target`.
    2. The array is assumed to be sorted in non-decreasing order.
    3. If `target` appears in `arr`, return the smallest index (0-based) where `arr[i] = target`.
    4. If `target` does not appear in `arr`, return -1.
    5. The method does not modify the array (arrays are immutable values in this setting).
-/

section Specs

-- Helper: array is sorted in non-decreasing order.
-- Uses natural-number indices and safe access `arr[i]!` guarded by bounds.
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: `target` occurs in `arr` at some index.
def occurs (arr : Array Int) (target : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = target

-- Helper: `idx : Int` corresponds to a valid Nat index.
def intIndexInBounds (arr : Array Int) (idx : Int) : Prop :=
  0 ≤ idx ∧ (idx.toNat) < arr.size

-- Precondition: input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedNonDecreasing arr

-- Postcondition: returns -1 iff target absent; otherwise returns the first index of target.
-- Characterization is via bounds + pointwise conditions and minimality.
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ↔ ¬ occurs arr target) ∧
  (result ≠ (-1) →
    intIndexInBounds arr result ∧
    arr[result.toNat]! = target ∧
    (∀ (j : Nat), j < result.toNat → arr[j]! ≠ target))

end Specs

section Impl

method findFirstOccurrence (arr : Array Int) (target : Int) return (result : Int)
  require precondition arr target
  ensures postcondition arr target result
  do
  pure (-1)  -- placeholder

end Impl

section TestCases

-- Test case 1: example with duplicates; first occurrence should be index 1
-- From prompt tests

def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_target : Int := 2
def test1_Expected : Int := 1

-- Test case 2: target absent (larger than all)

def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_target : Int := 6
def test2_Expected : Int := (-1)

-- Test case 3: target present at first index

def test3_arr : Array Int := #[1, 2, 3, 4, 5]
def test3_target : Int := 1
def test3_Expected : Int := 0

-- Test case 4: target present at last index

def test4_arr : Array Int := #[1, 2, 3, 4, 5]
def test4_target : Int := 5
def test4_Expected : Int := 4

-- Test case 5: target absent (smaller than all)

def test5_arr : Array Int := #[1, 2, 3, 4, 5]
def test5_target : Int := 0
def test5_Expected : Int := (-1)

-- Test case 6: empty array

def test6_arr : Array Int := #[]
def test6_target : Int := 10
def test6_Expected : Int := (-1)

-- Test case 7: all elements equal to target

def test7_arr : Array Int := #[7, 7, 7]
def test7_target : Int := 7
def test7_Expected : Int := 0

-- Test case 8: negative numbers with duplicates

def test8_arr : Array Int := #[-5, -3, -3, 0, 2]
def test8_target : Int := (-3)
def test8_Expected : Int := 1

-- Test case 9: single-element array, absent

def test9_arr : Array Int := #[4]
def test9_target : Int := 3
def test9_Expected : Int := (-1)

-- Recommend to validate: 1, 6, 8

end TestCases
