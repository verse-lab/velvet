import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replace: Replace elements greater than threshold k with -1
    Natural language breakdown:
    1. We are given an array of integers and a threshold value k
    2. We need to create a new array of the same size
    3. For each index i, if arr[i] > k, then result[i] = -1
    4. For each index i, if arr[i] ≤ k, then result[i] = arr[i] (unchanged)
    5. The output array has the same length as the input array
    6. Edge cases:
       - Empty array: return empty array
       - All elements ≤ k: return array unchanged
       - All elements > k: return array of all -1s
       - Negative threshold k: works with any integer comparison
-/

section Specs

-- Postcondition clause 1: result has same size as input
def ensures1 (arr : Array Int) (k : Int) (result : Array Int) :=
  result.size = arr.size

-- Postcondition clause 2: for each index, element is replaced correctly
def ensures2 (arr : Array Int) (k : Int) (result : Array Int) :=
  ∀ i : Nat, i < arr.size →
    (arr[i]! > k → result[i]! = -1) ∧
    (arr[i]! ≤ k → result[i]! = arr[i]!)

def precondition (arr : Array Int) (k : Int) :=
  True  -- no preconditions needed

def postcondition (arr : Array Int) (k : Int) (result : Array Int) :=
  ensures1 arr k result ∧ ensures2 arr k result

end Specs

section Impl

method replace (arr : Array Int) (k : Int)
  return (result : Array Int)
  require precondition arr k
  ensures postcondition arr k result
  do
  pure #[]  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic example from problem (mix of values above and below threshold)
def test1_arr : Array Int := #[1, 5, 3, 10]
def test1_k : Int := 4
def test1_Expected : Array Int := #[1, -1, 3, -1]

-- Test case 2: All elements at or below threshold (no replacements)
def test2_arr : Array Int := #[-1, 0, 1, 2]
def test2_k : Int := 2
def test2_Expected : Array Int := #[-1, 0, 1, 2]

-- Test case 3: Elements equal to threshold stay unchanged
def test3_arr : Array Int := #[100, 50, 100]
def test3_k : Int := 100
def test3_Expected : Array Int := #[100, 50, 100]

-- Test case 4: Negative threshold
def test4_arr : Array Int := #[-5, -2, 0, 3]
def test4_k : Int := -3
def test4_Expected : Array Int := #[-5, -1, -1, -1]

-- Test case 5: All elements below threshold
def test5_arr : Array Int := #[1, 2, 3]
def test5_k : Int := 5
def test5_Expected : Array Int := #[1, 2, 3]

-- Test case 6: Empty array
def test6_arr : Array Int := #[]
def test6_k : Int := 10
def test6_Expected : Array Int := #[]

-- Test case 7: Single element above threshold
def test7_arr : Array Int := #[10]
def test7_k : Int := 5
def test7_Expected : Array Int := #[-1]

-- Test case 8: Single element equal to threshold
def test8_arr : Array Int := #[5]
def test8_k : Int := 5
def test8_Expected : Array Int := #[5]

-- Test case 9: All elements above threshold
def test9_arr : Array Int := #[10, 20, 30]
def test9_k : Int := 5
def test9_Expected : Array Int := #[-1, -1, -1]

-- Test case 10: Mixed with zero threshold
def test10_arr : Array Int := #[-2, -1, 0, 1, 2]
def test10_k : Int := 0
def test10_Expected : Array Int := #[-2, -1, 0, -1, -1]

-- Recommend to validate: 1, 4, 6

end TestCases
