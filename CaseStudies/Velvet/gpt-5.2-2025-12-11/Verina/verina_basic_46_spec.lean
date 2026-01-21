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
    lastPosition: find the last occurrence of an element in a sorted array of integers.
    Natural language breakdown:
    1. Input is an array `arr : Array Int` and an integer `elem : Int`.
    2. The array is assumed to be sorted in non-decreasing order.
    3. The method returns an integer index `result`.
    4. If `elem` occurs in the array, `result` is the greatest index (0-based) where `arr[result] = elem`.
    5. If `elem` does not occur in the array, the method returns -1.
    6. If `result` is not -1, it must be a valid index: 0 ≤ result < arr.size.
    7. All indices strictly larger than `result` (but still in bounds) must not contain `elem`.
    8. The input array is not modified by the method.
-/

section Specs

-- Helper: array sorted in non-decreasing order (by Nat indices)
def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: element occurs in array
def occurs (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: no occurrence of element in array
def notOccurs (arr : Array Int) (x : Int) : Prop :=
  ∀ (i : Nat), i < arr.size → arr[i]! ≠ x

-- Helper: an Int is a valid in-bounds array index
-- Note: we relate the Int index to Nat bounds via Int.toNat.
def isValidIndexInt (arr : Array Int) (idx : Int) : Prop :=
  0 ≤ idx ∧ Int.toNat idx < arr.size

-- Helper: map an Int index to a Nat index (used only when in-bounds)
def idxNat (idx : Int) : Nat :=
  Int.toNat idx

-- Preconditions
-- The only required assumption is sortedness (rejects unsorted inputs like #[3,2,1]).
def precondition (arr : Array Int) (elem : Int) : Prop :=
  isSortedNondecreasing arr

-- Postconditions
-- If present: result is the last index containing elem.
-- If absent: result is -1.
def postcondition (arr : Array Int) (elem : Int) (result : Int) : Prop :=
  (result = (-1) ∧ notOccurs arr elem) ∨
  (isValidIndexInt arr result ∧
    arr[idxNat result]! = elem ∧
    (∀ (j : Nat), idxNat result < j → j < arr.size → arr[j]! ≠ elem) ∧
    (∀ (i : Nat), i < arr.size → arr[i]! = elem → i ≤ idxNat result))

end Specs

section Impl

method lastPosition (arr : Array Int) (elem : Int)
  return (result : Int)
  require precondition arr elem
  ensures postcondition arr elem result
  do
  pure (-1)  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt, element appears multiple times
-- arr = #[1,2,2,3,4,5], elem = 2, last index = 2
def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_elem : Int := 2
def test1_Expected : Int := 2

-- Test case 2: example, element absent
def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_elem : Int := 6
def test2_Expected : Int := -1

-- Test case 3: example, element is the last element
def test3_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test3_elem : Int := 5
def test3_Expected : Int := 5

-- Test case 4: example, single element present
def test4_arr : Array Int := #[1]
def test4_elem : Int := 1
def test4_Expected : Int := 0

-- Test case 5: example, all elements equal to elem
def test5_arr : Array Int := #[1, 1, 1, 1]
def test5_elem : Int := 1
def test5_Expected : Int := 3

-- Test case 6: example, duplicates at end
def test6_arr : Array Int := #[2, 2, 3, 3, 3]
def test6_elem : Int := 3
def test6_Expected : Int := 4

-- Test case 7: empty array (sorted), element absent
def test7_arr : Array Int := #[]
def test7_elem : Int := 10
def test7_Expected : Int := -1

-- Test case 8: sorted array with negative values and duplicates
def test8_arr : Array Int := #[-3, -1, -1, 0, 7]
def test8_elem : Int := -1
def test8_Expected : Int := 2

-- Test case 9: sorted array, element smaller than all values (absent)
def test9_arr : Array Int := #[0, 1, 2, 3]
def test9_elem : Int := -5
def test9_Expected : Int := -1

-- Recommend to validate: 1, 4, 8

end TestCases
