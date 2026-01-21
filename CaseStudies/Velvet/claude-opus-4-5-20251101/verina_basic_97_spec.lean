import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    TestArrayElements: Update an array such that the element at a specified index is set to 60
    while all other elements remain unchanged.
    
    Natural language breakdown:
    1. We are given an array of integers and an index j
    2. The index j must be valid (j < a.size)
    3. The result array should have the same size as the input array
    4. The element at index j in the result should be 60
    5. All other elements (at indices different from j) should remain unchanged
    6. This is essentially the Array.set! operation with the value 60
-/

section Specs

-- Precondition: j must be a valid index
def precondition (a : Array Int) (j : Nat) :=
  j < a.size

-- Postcondition: result has same size, element at j is 60, all other elements unchanged
def postcondition (a : Array Int) (j : Nat) (result : Array Int) :=
  result.size = a.size ∧
  result[j]! = 60 ∧
  (∀ i : Nat, i < a.size → i ≠ j → result[i]! = a[i]!)

end Specs

section Impl

method TestArrayElements (a : Array Int) (j : Nat)
  return (result : Array Int)
  require precondition a j
  ensures postcondition a j result
  do
  pure #[]  -- placeholder

end Impl

section TestCases

-- Test case 1: Update middle element (example from problem)
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_j : Nat := 2
def test1_Expected : Array Int := #[1, 2, 60, 4, 5]

-- Test case 2: Update element when array already contains 60
def test2_a : Array Int := #[60, 30, 20]
def test2_j : Nat := 1
def test2_Expected : Array Int := #[60, 60, 20]

-- Test case 3: Update first element (index 0)
def test3_a : Array Int := #[10, 20, 30]
def test3_j : Nat := 0
def test3_Expected : Array Int := #[60, 20, 30]

-- Test case 4: Update last element
def test4_a : Array Int := #[5, 10, 15]
def test4_j : Nat := 2
def test4_Expected : Array Int := #[5, 10, 60]

-- Test case 5: Single element array
def test5_a : Array Int := #[0]
def test5_j : Nat := 0
def test5_Expected : Array Int := #[60]

-- Test case 6: Update element that is already 60
def test6_a : Array Int := #[10, 60, 30, 40]
def test6_j : Nat := 1
def test6_Expected : Array Int := #[10, 60, 30, 40]

-- Test case 7: Array with negative numbers
def test7_a : Array Int := #[-5, -10, -15, -20]
def test7_j : Nat := 2
def test7_Expected : Array Int := #[-5, -10, 60, -20]

-- Test case 8: Larger array, update near end
def test8_a : Array Int := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def test8_j : Nat := 8
def test8_Expected : Array Int := #[1, 2, 3, 4, 5, 6, 7, 8, 60, 10]

-- Test case 9: Array with duplicate values
def test9_a : Array Int := #[5, 5, 5, 5]
def test9_j : Nat := 2
def test9_Expected : Array Int := #[5, 5, 60, 5]

-- Recommend to validate: 1, 3, 5

end TestCases
