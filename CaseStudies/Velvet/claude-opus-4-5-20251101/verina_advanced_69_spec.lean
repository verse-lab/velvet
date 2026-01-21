import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
--   searchInsert: Given a sorted list of distinct integers and a target value, return the index
--   if the target is found, or the index where it should be inserted to maintain sorted order.
--
-- Natural language breakdown:
-- 1. The input list xs is sorted in strictly increasing order (no duplicates)
-- 2. We need to find the position where target either exists or should be inserted
-- 3. The result is the count of elements in xs that are strictly less than target
-- 4. If target exists in xs, the result is its index
-- 5. If target doesn't exist, the result is where it would be inserted
-- 6. The result is always in the range [0, xs.length]
-- 7. Key property: result equals the number of elements strictly less than target
-- 8. For empty list, result is always 0
-- 9. If target is smaller than all elements, result is 0
-- 10. If target is larger than all elements, result is xs.length

section Specs

-- Helper: Check if a list is sorted in strictly increasing order
def isStrictlyIncreasing (xs : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length → xs[i]! < xs[j]!

-- Helper: Count elements in list strictly less than a given value
def countLessThan (xs : List Int) (target : Int) : Nat :=
  xs.countP (· < target)

-- Precondition: The list must be sorted in strictly increasing order (implies no duplicates)
def precondition (xs : List Int) (target : Int) : Prop :=
  isStrictlyIncreasing xs

-- Postcondition clauses:
-- 1. Result is in valid range [0, xs.length]
def ensures1 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result ≤ xs.length

-- 2. All elements before result index are strictly less than target
def ensures2 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ∀ i : Nat, i < result → i < xs.length → xs[i]! < target

-- 3. All elements from result index onwards are greater than or equal to target
def ensures3 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ∀ i : Nat, result ≤ i → i < xs.length → xs[i]! ≥ target

-- 4. Result equals the count of elements strictly less than target
def ensures4 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result = countLessThan xs target

def postcondition (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ensures1 xs target result ∧
  ensures2 xs target result ∧
  ensures3 xs target result ∧
  ensures4 xs target result

end Specs

section Impl

method searchInsert (xs : List Int) (target : Int)
  return (result : Nat)
  require precondition xs target
  ensures postcondition xs target result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Target found in middle of list (from problem example)
def test1_xs : List Int := [1, 3, 5, 6]
def test1_target : Int := 5
def test1_Expected : Nat := 2

-- Test case 2: Target not in list, should be inserted in middle
def test2_xs : List Int := [1, 3, 5, 6]
def test2_target : Int := 2
def test2_Expected : Nat := 1

-- Test case 3: Target larger than all elements
def test3_xs : List Int := [1, 3, 5, 6]
def test3_target : Int := 7
def test3_Expected : Nat := 4

-- Test case 4: Target smaller than all elements
def test4_xs : List Int := [1, 3, 5, 6]
def test4_target : Int := 0
def test4_Expected : Nat := 0

-- Test case 5: Empty list
def test5_xs : List Int := []
def test5_target : Int := 3
def test5_Expected : Nat := 0

-- Test case 6: Single element list, target smaller
def test6_xs : List Int := [10]
def test6_target : Int := 5
def test6_Expected : Nat := 0

-- Test case 7: Single element list, target larger
def test7_xs : List Int := [10]
def test7_target : Int := 15
def test7_Expected : Nat := 1

-- Test case 8: Target equals first element
def test8_xs : List Int := [1, 3, 5, 6]
def test8_target : Int := 1
def test8_Expected : Nat := 0

-- Test case 9: Target equals last element
def test9_xs : List Int := [1, 3, 5, 6]
def test9_target : Int := 6
def test9_Expected : Nat := 3

-- Test case 10: Negative numbers in list
def test10_xs : List Int := [-5, -2, 0, 3, 7]
def test10_target : Int := -1
def test10_Expected : Nat := 2

-- Recommend to validate: 1, 2, 5

end TestCases
