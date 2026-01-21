import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isGreater: Determine if a given integer is strictly greater than every element in an array
    Natural language breakdown:
    1. We have an integer n and an array of integers a
    2. We need to check if n is strictly greater than ALL elements in the array
    3. Return true if n > x for every x in the array
    4. Return false if there exists at least one element x in the array such that x >= n
    5. Edge case: Empty array - vacuously true (no elements to compare against)
       However, based on reject_inputs, empty array is not a valid input
    6. Key properties:
       - result = true ↔ every element in the array is strictly less than n
       - result = false ↔ there exists at least one element >= n
-/

section Specs

-- Precondition: The array must be non-empty
def precondition (n : Int) (a : Array Int) :=
  a.size > 0

-- Postcondition: result is true iff n is strictly greater than all elements in the array
def postcondition (n : Int) (a : Array Int) (result : Bool) :=
  result = true ↔ ∀ i : Nat, i < a.size → a[i]! < n

end Specs

section Impl

method isGreater (n : Int) (a : Array Int)
  return (result : Bool)
  require precondition n a
  ensures postcondition n a result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: n is greater than all elements
def test1_n : Int := 6
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: n is not greater than all elements (some elements >= n)
def test2_n : Int := 3
def test2_a : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Bool := false

-- Test case 3: n equals all elements (not strictly greater)
def test3_n : Int := 5
def test3_a : Array Int := #[5, 5, 5]
def test3_Expected : Bool := false

-- Test case 4: Negative numbers, n greater than all
def test4_n : Int := -1
def test4_a : Array Int := #[-10, -5, -3]
def test4_Expected : Bool := true

-- Test case 5: Negative numbers, n not greater than all
def test5_n : Int := -3
def test5_a : Array Int := #[-1, -2, -3]
def test5_Expected : Bool := false

-- Test case 6: n equals smallest element in array
def test6_n : Int := 0
def test6_a : Array Int := #[0, -1, -2]
def test6_Expected : Bool := false

-- Test case 7: n is greater than all elements in mixed array
def test7_n : Int := 10
def test7_a : Array Int := #[1, 2, 9, 3]
def test7_Expected : Bool := true

-- Test case 8: Single element array, n is greater
def test8_n : Int := 5
def test8_a : Array Int := #[4]
def test8_Expected : Bool := true

-- Test case 9: Single element array, n equals element
def test9_n : Int := 5
def test9_a : Array Int := #[5]
def test9_Expected : Bool := false

-- Test case 10: Large positive n with mixed positive and negative elements
def test10_n : Int := 100
def test10_a : Array Int := #[-50, 0, 50, 99]
def test10_Expected : Bool := true

-- Recommend to validate: 1, 2, 4

end TestCases
