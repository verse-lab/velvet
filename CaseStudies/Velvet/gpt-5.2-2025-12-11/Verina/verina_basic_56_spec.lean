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
    copy: Replace a segment of a destination array with a segment from a source array.
    Natural language breakdown:
    1. Inputs are two arrays of integers: src and dest.
    2. We are given starting indices sStart (into src) and dStart (into dest), and a length len.
    3. The output is a new array result with the same size as dest.
    4. Only the segment of dest from indices dStart .. dStart+len-1 is replaced.
    5. For every offset i with 0 ≤ i < len, result[dStart+i] equals src[sStart+i].
    6. For indices j < dStart, result[j] equals dest[j] (prefix unchanged).
    7. For indices j with dStart+len ≤ j < dest.size, result[j] equals dest[j] (suffix unchanged).
    8. The operation is only required to behave this way when src.size ≥ sStart + len and dest.size ≥ dStart + len.
-/

section Specs

-- Preconditions from the problem statement.
-- These ensure that the copied source slice and the overwritten destination segment are in-bounds.
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  sStart + len ≤ src.size ∧ dStart + len ≤ dest.size

-- Postcondition: size preserved and elementwise behavior is specified by cases.
-- The specification is extensional over indices < dest.size.
-- We inline the segment-membership test so Lean can synthesize its decidability.
def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
    (result : Array Int) : Prop :=
  result.size = dest.size ∧
  (∀ j : Nat, j < dest.size →
    (if h : (dStart ≤ j ∧ j < dStart + len) then
      result[j]! = src[sStart + (j - dStart)]!
    else
      result[j]! = dest[j]!))

end Specs

section Impl

method copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
  return (result : Array Int)
  require precondition src sStart dest dStart len
  ensures postcondition src sStart dest dStart len result
  do
  pure dest  -- placeholder body

end Impl

section TestCases

-- Test case 1: Provided example: replace dest[3..4] with src[1..2]
def test1_src : Array Int := #[10, 20, 30, 40, 50]
def test1_sStart : Nat := 1
def test1_dest : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_dStart : Nat := 3
def test1_len : Nat := 2
def test1_Expected : Array Int := #[1, 2, 3, 20, 30, 6]

-- Test case 2: Provided example: middle replacement length 3
def test2_src : Array Int := #[5, 6, 7, 8]
def test2_sStart : Nat := 0
def test2_dest : Array Int := #[9, 9, 9, 9, 9]
def test2_dStart : Nat := 1
def test2_len : Nat := 3
def test2_Expected : Array Int := #[9, 5, 6, 7, 9]

-- Test case 3: Provided example: len = 0 means unchanged
def test3_src : Array Int := #[100, 200]
def test3_sStart : Nat := 0
def test3_dest : Array Int := #[1, 2, 3]
def test3_dStart : Nat := 1
def test3_len : Nat := 0
def test3_Expected : Array Int := #[1, 2, 3]

-- Test case 4: Provided example: full overwrite
def test4_src : Array Int := #[10, 20, 30, 40, 50]
def test4_sStart : Nat := 0
def test4_dest : Array Int := #[0, 0, 0, 0, 0]
def test4_dStart : Nat := 0
def test4_len : Nat := 5
def test4_Expected : Array Int := #[10, 20, 30, 40, 50]

-- Test case 5: Provided example: overwrite last two positions using src starting at 2
def test5_src : Array Int := #[7, 8, 9, 10]
def test5_sStart : Nat := 2
def test5_dest : Array Int := #[1, 2, 3, 4, 5, 6]
def test5_dStart : Nat := 4
def test5_len : Nat := 2
def test5_Expected : Array Int := #[1, 2, 3, 4, 9, 10]

-- Test case 6: Edge: dest is empty, len = 0, result must be empty
def test6_src : Array Int := #[1, 2, 3]
def test6_sStart : Nat := 0
def test6_dest : Array Int := #[]
def test6_dStart : Nat := 0
def test6_len : Nat := 0
def test6_Expected : Array Int := #[]

-- Test case 7: Replace prefix of dest with a slice from src
def test7_src : Array Int := #[11, 12, 13, 14]
def test7_sStart : Nat := 1
def test7_dest : Array Int := #[0, 1, 2, 3, 4]
def test7_dStart : Nat := 0
def test7_len : Nat := 3
def test7_Expected : Array Int := #[12, 13, 14, 3, 4]

-- Test case 8: Replace suffix (dStart at last index), len = 1
def test8_src : Array Int := #[99, 100]
def test8_sStart : Nat := 1
def test8_dest : Array Int := #[5, 6, 7]
def test8_dStart : Nat := 2
def test8_len : Nat := 1
def test8_Expected : Array Int := #[5, 6, 100]

-- Test case 9: No-op in the middle with len = 0 (different starts)
def test9_src : Array Int := #[3, 4, 5]
def test9_sStart : Nat := 2
def test9_dest : Array Int := #[8, 9]
def test9_dStart : Nat := 1
def test9_len : Nat := 0
def test9_Expected : Array Int := #[8, 9]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 7

end TestCases
