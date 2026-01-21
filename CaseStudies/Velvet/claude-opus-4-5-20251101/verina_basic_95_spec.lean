import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    swap: Swap two elements in an array at specified positions
    Natural language breakdown:
    1. We are given an array of integers and two indices i and j
    2. The indices i and j are given as Int but represent valid array positions
    3. Both indices must be non-negative and within bounds of the array
    4. The result array has the same size as the input array
    5. The element at position i in the result equals the element at position j in the input
    6. The element at position j in the result equals the element at position i in the input
    7. All other elements remain unchanged at their original positions
    8. If i equals j, the array remains unchanged
    9. Mathlib provides Array.swap which directly implements this operation
-/

section Specs

-- Precondition: indices must be non-negative and within bounds
def precondition (arr : Array Int) (i : Int) (j : Int) :=
  i ≥ 0 ∧ j ≥ 0 ∧ i.toNat < arr.size ∧ j.toNat < arr.size

-- Postcondition: result has same size, elements at i and j are swapped, others unchanged
def postcondition (arr : Array Int) (i : Int) (j : Int) (result : Array Int) :=
  result.size = arr.size ∧
  result[i.toNat]! = arr[j.toNat]! ∧
  result[j.toNat]! = arr[i.toNat]! ∧
  (∀ k : Nat, k < arr.size → k ≠ i.toNat → k ≠ j.toNat → result[k]! = arr[k]!)

end Specs

section Impl

method swap (arr: Array Int) (i: Int) (j: Int)
  return (result: Array Int)
  require precondition arr i j
  ensures postcondition arr i j result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Swap middle elements (from problem description)
def test1_arr : Array Int := #[1, 2, 3, 4, 5]
def test1_i : Int := 1
def test1_j : Int := 3
def test1_Expected : Array Int := #[1, 4, 3, 2, 5]

-- Test case 2: Swap first and last elements
def test2_arr : Array Int := #[10, 20, 30, 40]
def test2_i : Int := 0
def test2_j : Int := 3
def test2_Expected : Array Int := #[40, 20, 30, 10]

-- Test case 3: Swap adjacent elements
def test3_arr : Array Int := #[7, 8, 9]
def test3_i : Int := 1
def test3_j : Int := 2
def test3_Expected : Array Int := #[7, 9, 8]

-- Test case 4: Swap same index (no change)
def test4_arr : Array Int := #[1, 2, 3, 4]
def test4_i : Int := 0
def test4_j : Int := 0
def test4_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 5: Swap with negative numbers
def test5_arr : Array Int := #[-1, -2, -3]
def test5_i : Int := 0
def test5_j : Int := 2
def test5_Expected : Array Int := #[-3, -2, -1]

-- Test case 6: Two element array
def test6_arr : Array Int := #[100, 200]
def test6_i : Int := 0
def test6_j : Int := 1
def test6_Expected : Array Int := #[200, 100]

-- Test case 7: Swap with indices in reverse order
def test7_arr : Array Int := #[5, 10, 15, 20, 25]
def test7_i : Int := 4
def test7_j : Int := 1
def test7_Expected : Array Int := #[5, 25, 15, 20, 10]

-- Test case 8: Single element array with same indices
def test8_arr : Array Int := #[42]
def test8_i : Int := 0
def test8_j : Int := 0
def test8_Expected : Array Int := #[42]

-- Test case 9: Mixed positive and negative numbers
def test9_arr : Array Int := #[-5, 0, 5, -10, 10]
def test9_i : Int := 1
def test9_j : Int := 4
def test9_Expected : Array Int := #[-5, 10, 5, -10, 0]

-- Test case 10: Swap middle index with same index
def test10_arr : Array Int := #[1, 2, 3, 4, 5]
def test10_i : Int := 2
def test10_j : Int := 2
def test10_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Recommend to validate: 1, 2, 4

end TestCases
