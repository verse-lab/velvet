import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    modify_array_element: Update a specific element in a 2D array
    Natural language breakdown:
    1. We have a 2D array (array of arrays) of natural numbers
    2. We are given two indices: index1 for the outer array and index2 for the inner array
    3. We are given a new value val to set at the specified position
    4. The result should have the same overall structure as the input
    5. All inner arrays except the one at index1 should remain unchanged
    6. In the inner array at index1, only the element at index2 should be replaced with val
    7. All other elements in the modified inner array should remain the same
    8. Preconditions ensure index1 and index2 are valid indices
-/

section Specs

-- Precondition: indices must be valid
def precondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧ index2 < (arr[index1]!).size

-- Postcondition: result has same structure with only the specified element changed
def postcondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result : Array (Array Nat)) : Prop :=
  -- Same outer array size
  result.size = arr.size ∧
  -- For all outer indices, inner array sizes are preserved
  (∀ i : Nat, i < arr.size → (result[i]!).size = (arr[i]!).size) ∧
  -- For outer indices different from index1, inner arrays are unchanged
  (∀ i : Nat, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  -- For the modified inner array at index1, element at index2 is val
  ((result[index1]!)[index2]! = val) ∧
  -- For the modified inner array at index1, all other elements are unchanged
  (∀ j : Nat, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!)

end Specs

section Impl

method modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat)
  return (result : Array (Array Nat))
  require precondition arr index1 index2 val
  ensures postcondition arr index1 index2 val result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Modify element in first inner array (example from problem)
def test1_arr : Array (Array Nat) := #[#[1, 2, 3], #[4, 5, 6]]
def test1_index1 : Nat := 0
def test1_index2 : Nat := 1
def test1_val : Nat := 99
def test1_Expected : Array (Array Nat) := #[#[1, 99, 3], #[4, 5, 6]]

-- Test case 2: Modify first element in second inner array
def test2_arr : Array (Array Nat) := #[#[7, 8], #[9, 10]]
def test2_index1 : Nat := 1
def test2_index2 : Nat := 0
def test2_val : Nat := 0
def test2_Expected : Array (Array Nat) := #[#[7, 8], #[0, 10]]

-- Test case 3: Modify last element in single inner array
def test3_arr : Array (Array Nat) := #[#[0, 0, 0]]
def test3_index1 : Nat := 0
def test3_index2 : Nat := 2
def test3_val : Nat := 5
def test3_Expected : Array (Array Nat) := #[#[0, 0, 5]]

-- Test case 4: Modify element in last inner array of 3x3 structure
def test4_arr : Array (Array Nat) := #[#[3, 4, 5], #[6, 7, 8], #[9, 10, 11]]
def test4_index1 : Nat := 2
def test4_index2 : Nat := 1
def test4_val : Nat := 100
def test4_Expected : Array (Array Nat) := #[#[3, 4, 5], #[6, 7, 8], #[9, 100, 11]]

-- Test case 5: Single element array (edge case)
def test5_arr : Array (Array Nat) := #[#[1]]
def test5_index1 : Nat := 0
def test5_index2 : Nat := 0
def test5_val : Nat := 42
def test5_Expected : Array (Array Nat) := #[#[42]]

-- Test case 6: Modify middle element in middle array
def test6_arr : Array (Array Nat) := #[#[1, 2], #[3, 4, 5], #[6, 7]]
def test6_index1 : Nat := 1
def test6_index2 : Nat := 1
def test6_val : Nat := 50
def test6_Expected : Array (Array Nat) := #[#[1, 2], #[3, 50, 5], #[6, 7]]

-- Test case 7: Replace with same value (no change in content)
def test7_arr : Array (Array Nat) := #[#[10, 20, 30]]
def test7_index1 : Nat := 0
def test7_index2 : Nat := 0
def test7_val : Nat := 10
def test7_Expected : Array (Array Nat) := #[#[10, 20, 30]]

-- Test case 8: Large value replacement
def test8_arr : Array (Array Nat) := #[#[1, 2], #[3, 4]]
def test8_index1 : Nat := 0
def test8_index2 : Nat := 1
def test8_val : Nat := 999999
def test8_Expected : Array (Array Nat) := #[#[1, 999999], #[3, 4]]

-- Recommend to validate: 1, 2, 5

end TestCases

