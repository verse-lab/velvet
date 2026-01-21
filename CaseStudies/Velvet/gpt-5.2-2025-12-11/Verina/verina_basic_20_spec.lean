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
    uniqueProduct: product of all distinct integers in an array
    Natural language breakdown:
    1. Input is an array of integers.
    2. Consider the set of distinct integer values that occur in the array.
    3. Multiply each distinct value exactly once; order does not matter.
    4. If the array is empty, there are no distinct values, so the product is 1.
    5. Duplicates in the array do not change the result.
    6. Zero is handled normally: if 0 occurs in the array, the unique-product is 0.
-/

section Specs

-- Helper: the finset of values appearing in the array (deduplicated).
-- We use Mathlib's List.toFinset to represent distinct elements.

def distinctVals (arr : Array Int) : Finset Int :=
  arr.toList.toFinset

-- Helper: product over the distinct values (order-independent).
-- Finset.prod uses commutative multiplication on Int with identity 1.

def distinctProduct (arr : Array Int) : Int :=
  (distinctVals arr).prod (fun x => x)

-- No preconditions.

def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result equals the product of all distinct values in the array.
-- This captures: empty array -> product over empty finset -> 1.

def postcondition (arr : Array Int) (result : Int) : Prop :=
  result = distinctProduct arr

end Specs

section Impl

method uniqueProduct (arr : Array Int) return (result : Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure 1

end Impl

section TestCases

-- Test case 1: example from prompt
-- distinct values {2,3,4} -> 2*3*4 = 24

def test1_arr : Array Int := #[2, 3, 2, 4]

def test1_Expected : Int := 24

-- Test case 2: all elements same

def test2_arr : Array Int := #[5, 5, 5, 5]

def test2_Expected : Int := 5

-- Test case 3: empty array -> 1

def test3_arr : Array Int := #[]

def test3_Expected : Int := 1

-- Test case 4: already unique

def test4_arr : Array Int := #[1, 2, 3]

def test4_Expected : Int := 6

-- Test case 5: contains zero -> product is zero

def test5_arr : Array Int := #[0, 2, 3]

def test5_Expected : Int := 0

-- Test case 6: negative numbers with duplicates
-- distinct values {-1,-2,-3} -> (-1)*(-2)*(-3) = -6

def test6_arr : Array Int := #[-1, -2, -1, -3]

def test6_Expected : Int := -6

-- Test case 7: larger positive values with duplicates
-- distinct values {10,20,30} -> 6000

def test7_arr : Array Int := #[10, 10, 20, 20, 30]

def test7_Expected : Int := 6000

-- Test case 8: mixture with sign and duplicates
-- distinct values {-2,0,2} -> 0

def test8_arr : Array Int := #[-2, 0, 2, -2, 2]

def test8_Expected : Int := 0

-- Test case 9: single element

def test9_arr : Array Int := #[7]

def test9_Expected : Int := 7

-- Recommend to validate: 1, 3, 6

end TestCases
