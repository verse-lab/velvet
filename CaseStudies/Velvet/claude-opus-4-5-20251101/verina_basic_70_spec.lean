import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LinearSearch3: Find the first index in an array where a given predicate holds true
    Natural language breakdown:
    1. Given an array of integers and a predicate function P
    2. We need to find the index of the first element that satisfies P
    3. The returned index must be less than the size of the array
    4. The element at the returned index must satisfy the predicate P
    5. All elements before the returned index must NOT satisfy P
    6. Precondition: at least one element in the array satisfies P
-/

section Specs

-- Precondition: array is non-empty and at least one element satisfies P
def precondition (a : Array Int) (P : Int → Bool) :=
  ∃ i : Nat, i < a.size ∧ P (a[i]!) = true

-- Postcondition: result is the first index where P holds
-- 1. result is a valid index (less than array size)
-- 2. the element at result satisfies P
-- 3. all elements before result do not satisfy P
def postcondition (a : Array Int) (P : Int → Bool) (result : Nat) :=
  result < a.size ∧
  P (a[result]!) = true ∧
  (∀ j : Nat, j < result → P (a[j]!) = false)

end Specs

section Impl

method LinearSearch3 (a : Array Int) (P : Int → Bool)
  return (result : Nat)
  require precondition a P
  ensures postcondition a P result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Find first element > 5 in [4, 7, 2, 9] (example from problem)
def test1_a : Array Int := #[4, 7, 2, 9]
def test1_P : Int → Bool := fun x => x > 5
def test1_Expected : Nat := 1

-- Test case 2: Find first element < 5 in [10, 8, 6, 4, 2]
def test2_a : Array Int := #[10, 8, 6, 4, 2]
def test2_P : Int → Bool := fun x => x < 5
def test2_Expected : Nat := 3

-- Test case 3: Find first element equal to 1 in [5, 3, 1, 2]
def test3_a : Array Int := #[5, 3, 1, 2]
def test3_P : Int → Bool := fun x => x == 1
def test3_Expected : Nat := 2

-- Test case 4: Find first element equal to 0 in [0, 1, 2, 3] (first position)
def test4_a : Array Int := #[0, 1, 2, 3]
def test4_P : Int → Bool := fun x => x == 0
def test4_Expected : Nat := 0

-- Test case 5: Find first element equal to 9 in [9, 9, 9, 9] (all same)
def test5_a : Array Int := #[9, 9, 9, 9]
def test5_P : Int → Bool := fun x => x == 9
def test5_Expected : Nat := 0

-- Test case 6: Find first negative element in [-1, 2, 3, 4]
def test6_a : Array Int := #[-1, 2, 3, 4]
def test6_P : Int → Bool := fun x => x < 0
def test6_Expected : Nat := 0

-- Test case 7: Find first element > 100 in [1, 2, 3, 101, 102]
def test7_a : Array Int := #[1, 2, 3, 101, 102]
def test7_P : Int → Bool := fun x => x > 100
def test7_Expected : Nat := 3

-- Test case 8: Single element array [42], find 42
def test8_a : Array Int := #[42]
def test8_P : Int → Bool := fun x => x == 42
def test8_Expected : Nat := 0

-- Test case 9: Find first even number in [1, 3, 5, 7, 8]
def test9_a : Array Int := #[1, 3, 5, 7, 8]
def test9_P : Int → Bool := fun x => x % 2 == 0
def test9_Expected : Nat := 4

-- Test case 10: Find last position element in [1, 2, 3, 4, 5], element = 5
def test10_a : Array Int := #[1, 2, 3, 4, 5]
def test10_P : Int → Bool := fun x => x == 5
def test10_Expected : Nat := 4

-- Recommend to validate: 1, 4, 9

end TestCases
