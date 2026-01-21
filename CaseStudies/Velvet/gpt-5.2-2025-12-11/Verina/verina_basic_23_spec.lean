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
    differenceMinMax: compute the difference between the maximum and minimum values of a nonempty array of Int.
    Natural language breakdown:
    1. The input is an array `a : Array Int`.
    2. The input array is assumed to be non-empty.
    3. Let `mn` be the minimum value occurring in `a` and `mx` be the maximum value occurring in `a`.
    4. The returned integer is `mx - mn`.
    5. The result must be 0 when all elements are equal or when the array has exactly one element.
    6. The specification should describe `mn` and `mx` as bounds achieved by some array elements.
-/

section Specs

-- Helper predicate: value occurs in array
def InArray (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

-- Helper predicate: `mn` is a minimum value achieved in the array
def IsMinOfArray (a : Array Int) (mn : Int) : Prop :=
  InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)

-- Helper predicate: `mx` is a maximum value achieved in the array
def IsMaxOfArray (a : Array Int) (mx : Int) : Prop :=
  InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)

-- Precondition: array is nonempty
-- We use `a.size ≠ 0` which is equivalent to `a ≠ #[]` via `Array.size_eq_zero_iff`.
def precondition (a : Array Int) : Prop :=
  a.size ≠ 0

-- Postcondition: result equals (max - min) for some achieved max/min bounds.
-- We avoid specifying an algorithm; instead we characterize the unique value via existence of
-- extremal witnesses and defining equation.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (mn : Int) (mx : Int),
    IsMinOfArray a mn ∧
    IsMaxOfArray a mx ∧
    result = mx - mn

end Specs

section Impl

method differenceMinMax (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt
-- max = 9, min = 1, difference = 8
def test1_a : Array Int := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
def test1_Expected : Int := 8

-- Test case 2: increasing positives
def test2_a : Array Int := #[10, 20, 30, 40, 50]
def test2_Expected : Int := 40

-- Test case 3: decreasing negatives
def test3_a : Array Int := #[-10, -20, -30, -40, -50]
def test3_Expected : Int := 40

-- Test case 4: singleton array
def test4_a : Array Int := #[7]
def test4_Expected : Int := 0

-- Test case 5: all equal
def test5_a : Array Int := #[5, 5, 5, 5]
def test5_Expected : Int := 0

-- Test case 6: mixed signs
def test6_a : Array Int := #[1, -1, 2, -2]
def test6_Expected : Int := 4

-- Test case 7: two elements, already ordered
def test7_a : Array Int := #[2, 10]
def test7_Expected : Int := 8

-- Test case 8: two elements, reversed order
def test8_a : Array Int := #[10, 2]
def test8_Expected : Int := 8

-- Test case 9: includes Int.min/Int.max like extremes (small manageable)
-- Here: max = 0, min = -2147483648, difference = 2147483648
def test9_a : Array Int := #[-2147483648, 0, -1]
def test9_Expected : Int := 2147483648

-- Reject input (documented): empty array should violate precondition
def reject1_a : Array Int := #[]

-- Recommend to validate: 1, 4, 6

end TestCases
