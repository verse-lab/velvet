import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- removeElement: Remove an element from an array at a specified index
-- Natural language breakdown:
-- 1. Given an array of integers s and an index k
-- 2. Remove the element at index k from the array
-- 3. The resulting array should have length one less than the original
-- 4. Elements before index k remain unchanged (at their original positions)
-- 5. Elements after index k are shifted one position to the left
-- 6. Precondition: k must be a valid index (0 ≤ k < s.size)
-- 7. The order of all remaining elements is preserved

section Specs

-- Precondition: k must be a valid index within the array bounds
def precondition (s : Array Int) (k : Nat) :=
  k < s.size

-- Postcondition clauses:
-- 1. Result has length one less than original
def ensures1 (s : Array Int) (k : Nat) (result : Array Int) :=
  result.size = s.size - 1

-- 2. Elements before index k are unchanged
def ensures2 (s : Array Int) (k : Nat) (result : Array Int) :=
  ∀ i : Nat, i < k → result[i]! = s[i]!

-- 3. Elements after index k are shifted left by one position
def ensures3 (s : Array Int) (k : Nat) (result : Array Int) :=
  ∀ i : Nat, k ≤ i → i < result.size → result[i]! = s[i + 1]!

def postcondition (s : Array Int) (k : Nat) (result : Array Int) :=
  ensures1 s k result ∧
  ensures2 s k result ∧
  ensures3 s k result

end Specs

section Impl

method removeElement (s : Array Int) (k : Nat)
  return (result : Array Int)
  require precondition s k
  ensures postcondition s k result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Remove element from middle of array (example from problem)
def test1_s : Array Int := #[1, 2, 3, 4, 5]
def test1_k : Nat := 2
def test1_Expected : Array Int := #[1, 2, 4, 5]

-- Test case 2: Remove first element (index 0)
def test2_s : Array Int := #[10, 20, 30, 40]
def test2_k : Nat := 0
def test2_Expected : Array Int := #[20, 30, 40]

-- Test case 3: Remove last element
def test3_s : Array Int := #[10, 20, 30, 40]
def test3_k : Nat := 3
def test3_Expected : Array Int := #[10, 20, 30]

-- Test case 4: Remove only element from single-element array
def test4_s : Array Int := #[7]
def test4_k : Nat := 0
def test4_Expected : Array Int := #[]

-- Test case 5: Remove from two-element array (first element)
def test5_s : Array Int := #[100, 200]
def test5_k : Nat := 0
def test5_Expected : Array Int := #[200]

-- Test case 6: Remove from two-element array (second element)
def test6_s : Array Int := #[100, 200]
def test6_k : Nat := 1
def test6_Expected : Array Int := #[100]

-- Test case 7: Remove element with negative integers
def test7_s : Array Int := #[-5, -3, -1, 0, 2, 4]
def test7_k : Nat := 2
def test7_Expected : Array Int := #[-5, -3, 0, 2, 4]

-- Test case 8: Remove from array with duplicate values
def test8_s : Array Int := #[5, 5, 5, 5]
def test8_k : Nat := 1
def test8_Expected : Array Int := #[5, 5, 5]

-- Test case 9: Remove second-to-last element
def test9_s : Array Int := #[1, 2, 3, 4, 5, 6]
def test9_k : Nat := 4
def test9_Expected : Array Int := #[1, 2, 3, 4, 6]

-- Test case 10: Remove from larger array
def test10_s : Array Int := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def test10_k : Nat := 5
def test10_Expected : Array Int := #[0, 1, 2, 3, 4, 6, 7, 8, 9]

-- Recommend to validate: 1, 2, 4

end TestCases
