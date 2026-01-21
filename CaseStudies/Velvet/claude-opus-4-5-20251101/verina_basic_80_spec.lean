import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    only_once: Determine whether a specified key appears exactly once in an array
    Natural language breakdown:
    1. We are given an array of integers and a key (integer) to search for
    2. We need to check if the key appears exactly once in the array
    3. The result is true if and only if the count of key in the array equals 1
    4. If the key appears zero times, return false
    5. If the key appears two or more times, return false
    6. Edge cases:
       - Empty array: no elements, so key cannot appear, return false
       - Single element array equal to key: appears exactly once, return true
       - Single element array not equal to key: appears zero times, return false
       - Multiple occurrences of key: return false
       - Key not in array: return false
-/

-- Using Mathlib's Array.count function which counts occurrences of an element

section Specs

-- Precondition: no restrictions on input
def precondition (a : Array Int) (key : Int) :=
  True

-- Postcondition: result is true iff key appears exactly once in array
def postcondition (a : Array Int) (key : Int) (result : Bool) :=
  result = (a.count key == 1)

end Specs

section Impl

method only_once (a : Array Int) (key : Int)
  return (result : Bool)
  require precondition a key
  ensures postcondition a key result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Key appears exactly once (from problem example)
def test1_a : Array Int := #[1, 2, 3, 4]
def test1_key : Int := 2
def test1_Expected : Bool := true

-- Test case 2: Key appears twice (from problem example)
def test2_a : Array Int := #[1, 2, 2, 3, 4]
def test2_key : Int := 2
def test2_Expected : Bool := false

-- Test case 3: Key appears multiple times (all same element)
def test3_a : Array Int := #[1, 1, 1, 1]
def test3_key : Int := 1
def test3_Expected : Bool := false

-- Test case 4: Single element array equal to key
def test4_a : Array Int := #[10]
def test4_key : Int := 10
def test4_Expected : Bool := true

-- Test case 5: Empty array
def test5_a : Array Int := #[]
def test5_key : Int := 5
def test5_Expected : Bool := false

-- Test case 6: Key not in array
def test6_a : Array Int := #[1, 2, 3, 4, 5]
def test6_key : Int := 10
def test6_Expected : Bool := false

-- Test case 7: Single element array not equal to key
def test7_a : Array Int := #[7]
def test7_key : Int := 3
def test7_Expected : Bool := false

-- Test case 8: Key at beginning and end
def test8_a : Array Int := #[5, 1, 2, 3, 5]
def test8_key : Int := 5
def test8_Expected : Bool := false

-- Test case 9: Negative numbers, key appears once
def test9_a : Array Int := #[-1, -2, -3, 0, 1]
def test9_key : Int := -2
def test9_Expected : Bool := true

-- Test case 10: Large array with key appearing once
def test10_a : Array Int := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def test10_key : Int := 7
def test10_Expected : Bool := true

-- Recommend to validate: 1, 2, 5

end TestCases
