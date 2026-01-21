import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Find: Find the first occurrence of a key in an array of integers
    Natural language breakdown:
    1. Given an array of integers and a key integer to search for
    2. Return the index of the first occurrence of the key in the array
    3. If the key is not found in the array, return -1
    4. The result is in range [0, a.size) if the key is found
    5. If the result is not -1, then the element at that index equals the key
    6. If the result is not -1, all elements before that index are not equal to the key
    7. The array can be empty or non-empty (no preconditions on array)
    8. Linear search from index 0 to find first occurrence
-/

section Specs

-- Precondition: No restrictions on input
def precondition (a : Array Int) (key : Int) : Prop :=
  True

-- Postcondition: Result is either -1 (not found) or the index of first occurrence
def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  -- Case 1: key not found - result is -1 and key does not appear in array
  (result = -1 ∧ ∀ i : Nat, i < a.size → a[i]! ≠ key) ∨
  -- Case 2: key found - result is valid index, element at result equals key,
  -- and all elements before result are not equal to key
  (result ≥ 0 ∧
   result < a.size ∧
   a[result.toNat]! = key ∧
   ∀ i : Nat, i < result.toNat → a[i]! ≠ key)

end Specs

section Impl

method Find (a : Array Int) (key : Int)
  return (result : Int)
  require precondition a key
  ensures postcondition a key result
  do
  pure (-1)

end Impl

section TestCases

-- Test case 1: Key found in middle of array
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_key : Int := 3
def test1_Expected : Int := 2

-- Test case 2: Key is the first element (with duplicates)
def test2_a : Array Int := #[5, 7, 5, 9]
def test2_key : Int := 5
def test2_Expected : Int := 0

-- Test case 3: Key not found in array
def test3_a : Array Int := #[2, 4, 6, 8]
def test3_key : Int := 5
def test3_Expected : Int := -1

-- Test case 4: Empty array
def test4_a : Array Int := #[]
def test4_key : Int := 10
def test4_Expected : Int := -1

-- Test case 5: Negative key found
def test5_a : Array Int := #[0, -3, -1, -3]
def test5_key : Int := -3
def test5_Expected : Int := 1

-- Test case 6: Single element array, key found
def test6_a : Array Int := #[42]
def test6_key : Int := 42
def test6_Expected : Int := 0

-- Test case 7: Single element array, key not found
def test7_a : Array Int := #[42]
def test7_key : Int := 10
def test7_Expected : Int := -1

-- Test case 8: Key is the last element
def test8_a : Array Int := #[1, 2, 3, 4, 5]
def test8_key : Int := 5
def test8_Expected : Int := 4

-- Test case 9: All elements are the same as key
def test9_a : Array Int := #[7, 7, 7, 7]
def test9_key : Int := 7
def test9_Expected : Int := 0

-- Test case 10: Key is zero
def test10_a : Array Int := #[-1, 0, 1, 2]
def test10_key : Int := 0
def test10_Expected : Int := 1

-- Recommend to validate: 1, 2, 5

end TestCases
