import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    copy: Replace a segment in destination array with values from source array
    Natural language breakdown:
    1. Given two arrays (src and dest), starting positions (sStart and dStart), and a length (len)
    2. The result array has the same size as the destination array
    3. Elements at indices less than dStart remain unchanged from dest
    4. Elements at indices greater than or equal to dStart + len remain unchanged from dest
    5. For each index i with 0 ≤ i < len, the element at index dStart + i in result equals src[sStart + i]
    6. Preconditions ensure both arrays have sufficient elements:
       - src.size ≥ sStart + len (source has enough elements to copy from)
       - dest.size ≥ dStart + len (destination has enough space to copy to)
-/

section Specs

-- Precondition: source and destination arrays have sufficient elements
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) :=
  src.size ≥ sStart + len ∧ dest.size ≥ dStart + len

-- Postcondition: result is dest with segment replaced
def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result : Array Int) :=
  -- Result has same size as dest
  result.size = dest.size ∧
  -- Elements before the copied segment are unchanged
  (∀ i : Nat, i < dStart → i < result.size → result[i]! = dest[i]!) ∧
  -- Elements in the copied segment come from src
  (∀ i : Nat, i < len → result[dStart + i]! = src[sStart + i]!) ∧
  -- Elements after the copied segment are unchanged
  (∀ i : Nat, i ≥ dStart + len → i < result.size → result[i]! = dest[i]!)

end Specs

section Impl

method copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
  return (result : Array Int)
  require precondition src sStart dest dStart len
  ensures postcondition src sStart dest dStart len result
  do
    pure #[]  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - copy 2 elements from src[1..3] to dest[3..5]
def test1_src : Array Int := #[10, 20, 30, 40, 50]
def test1_sStart : Nat := 1
def test1_dest : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_dStart : Nat := 3
def test1_len : Nat := 2
def test1_Expected : Array Int := #[1, 2, 3, 20, 30, 6]

-- Test case 2: Copy 3 elements from src[0..3] to dest[1..4]
def test2_src : Array Int := #[5, 6, 7, 8]
def test2_sStart : Nat := 0
def test2_dest : Array Int := #[9, 9, 9, 9, 9]
def test2_dStart : Nat := 1
def test2_len : Nat := 3
def test2_Expected : Array Int := #[9, 5, 6, 7, 9]

-- Test case 3: Copy 0 elements (no change)
def test3_src : Array Int := #[100, 200]
def test3_sStart : Nat := 0
def test3_dest : Array Int := #[1, 2, 3]
def test3_dStart : Nat := 1
def test3_len : Nat := 0
def test3_Expected : Array Int := #[1, 2, 3]

-- Test case 4: Copy entire array to overwrite dest completely
def test4_src : Array Int := #[10, 20, 30, 40, 50]
def test4_sStart : Nat := 0
def test4_dest : Array Int := #[0, 0, 0, 0, 0]
def test4_dStart : Nat := 0
def test4_len : Nat := 5
def test4_Expected : Array Int := #[10, 20, 30, 40, 50]

-- Test case 5: Copy from middle of src to end of dest
def test5_src : Array Int := #[7, 8, 9, 10]
def test5_sStart : Nat := 2
def test5_dest : Array Int := #[1, 2, 3, 4, 5, 6]
def test5_dStart : Nat := 4
def test5_len : Nat := 2
def test5_Expected : Array Int := #[1, 2, 3, 4, 9, 10]

-- Test case 6: Copy single element
def test6_src : Array Int := #[100, 200, 300]
def test6_sStart : Nat := 1
def test6_dest : Array Int := #[1, 2, 3, 4]
def test6_dStart : Nat := 2
def test6_len : Nat := 1
def test6_Expected : Array Int := #[1, 2, 200, 4]

-- Test case 7: Copy to beginning of dest
def test7_src : Array Int := #[10, 20, 30]
def test7_sStart : Nat := 0
def test7_dest : Array Int := #[1, 2, 3, 4, 5]
def test7_dStart : Nat := 0
def test7_len : Nat := 2
def test7_Expected : Array Int := #[10, 20, 3, 4, 5]

-- Test case 8: Empty arrays with len 0
def test8_src : Array Int := #[]
def test8_sStart : Nat := 0
def test8_dest : Array Int := #[1, 2, 3]
def test8_dStart : Nat := 0
def test8_len : Nat := 0
def test8_Expected : Array Int := #[1, 2, 3]

-- Test case 9: Negative integers
def test9_src : Array Int := #[-10, -20, -30]
def test9_sStart : Nat := 0
def test9_dest : Array Int := #[1, 2, 3, 4]
def test9_dStart : Nat := 1
def test9_len : Nat := 2
def test9_Expected : Array Int := #[1, -10, -20, 4]

-- Test case 10: Copy from end of source
def test10_src : Array Int := #[1, 2, 3, 4, 5]
def test10_sStart : Nat := 3
def test10_dest : Array Int := #[0, 0, 0]
def test10_dStart : Nat := 0
def test10_len : Nat := 2
def test10_Expected : Array Int := #[4, 5, 0]

-- Recommend to validate: 1, 2, 4

end TestCases
