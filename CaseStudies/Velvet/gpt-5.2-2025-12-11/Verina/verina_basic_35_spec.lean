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
    MoveZeroesToEnd: Rearrange an array of integers by moving all zero values to the end while preserving
    the relative order of non-zero elements.

    Natural language breakdown:
    1. Input is an Array Int; output is an Array Int of the same size.
    2. The output contains the same multiset of elements as the input, but with all 0 values moved to the end.
    3. The relative order of the non-zero elements is preserved (stable with respect to non-zeros).
    4. In the output, there is a split point k such that indices < k are non-zero and indices ≥ k are zero.
    5. There are no preconditions; the method must work for any array.
-/

section Specs

-- Helper: list of non-zero elements in array order (stable).
-- We use the list view to talk about order.
def nonzerosList (arr : Array Int) : List Int :=
  arr.toList.filter (fun x => x ≠ 0)

-- Helper: all elements from index k onward are zero.
def allZeroFrom (arr : Array Int) (k : Nat) : Prop :=
  ∀ i : Nat, i < arr.size → k ≤ i → arr[i]! = 0

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) size is preserved
-- 2) there is a split point k = number of non-zeros in input
-- 3) prefix (0..k-1) equals the input's nonzero list index-wise (order preserved)
-- 4) the suffix (k..end) is all zeros
-- These properties uniquely determine the output.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∃ k : Nat,
    k = (nonzerosList arr).length ∧
    k ≤ result.size ∧
    (∀ i : Nat, i < k → result[i]! = (nonzerosList arr)[i]!) ∧
    allZeroFrom result k)

end Specs

section Impl

method MoveZeroesToEnd (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: example from prompt
-- Input: #[0, 1, 0, 3, 12] -> #[1, 3, 12, 0, 0]
def test1_arr : Array Int := #[0, 1, 0, 3, 12]
def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: leading zeros then one element
-- #[0,0,1] -> #[1,0,0]
def test2_arr : Array Int := #[0, 0, 1]
def test2_Expected : Array Int := #[1, 0, 0]

-- Test case 3: already has no zeros
-- #[1,2,3] -> unchanged
def test3_arr : Array Int := #[1, 2, 3]
def test3_Expected : Array Int := #[1, 2, 3]

-- Test case 4: all zeros
-- #[0,0,0] -> unchanged
def test4_arr : Array Int := #[0, 0, 0]
def test4_Expected : Array Int := #[0, 0, 0]

-- Test case 5: empty array
-- #[] -> #[]
def test5_arr : Array Int := #[]
def test5_Expected : Array Int := #[]

-- Test case 6: zeros already at end
-- #[1,2,0,0] -> #[1,2,0,0]
def test6_arr : Array Int := #[1, 2, 0, 0]
def test6_Expected : Array Int := #[1, 2, 0, 0]

-- Test case 7: interleaved zeros with negatives
-- #[0,-1,0,-2,3,0] -> #[-1,-2,3,0,0,0]
def test7_arr : Array Int := #[0, -1, 0, -2, 3, 0]
def test7_Expected : Array Int := #[-1, -2, 3, 0, 0, 0]

-- Test case 8: single element non-zero
-- #[5] -> #[5]
def test8_arr : Array Int := #[5]
def test8_Expected : Array Int := #[5]

-- Test case 9: single element zero
-- #[0] -> #[0]
def test9_arr : Array Int := #[0]
def test9_Expected : Array Int := #[0]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test3, test7

end TestCases
