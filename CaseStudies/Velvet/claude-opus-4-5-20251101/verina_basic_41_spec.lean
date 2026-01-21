import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasOnlyOneDistinctElement: Determine whether an array contains only one distinct element
    Natural language breakdown:
    1. We have an input array of integers
    2. "Only one distinct element" means all elements in the array are identical
    3. The function should return true if the array is empty (vacuously true - no distinct elements)
    4. The function should return true if all elements equal the first element
    5. The function should return false if there exist at least two different elements
    6. Example: [1, 1, 1] → all elements are 1 → true
    7. Example: [1, 2, 1] → contains 1 and 2 → false
    8. Example: [7] → single element → true
    9. Example: [3, 4, 5, 6] → contains multiple distinct values → false

    Property-oriented specification:
    - If result is true: for any two indices i and j in the array, a[i] = a[j]
    - If result is false: there exist two indices i and j such that a[i] ≠ a[j]
    - Equivalently: all elements equal the first element (when array is non-empty)
-/

section Specs

-- Helper Functions

-- Predicate: all elements in the array are equal to each other
def allElementsEqual (a : Array Int) : Prop :=
  ∀ i j : Nat, i < a.size → j < a.size → a[i]! = a[j]!

-- Postcondition clauses
def ensures1 (a : Array Int) (result : Bool) :=
  result = true ↔ allElementsEqual a

def precondition (a : Array Int) :=
  a.size > 0

def postcondition (a : Array Int) (result : Bool) :=
  ensures1 a result

end Specs

section Impl

method hasOnlyOneDistinctElement (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure true

end Impl

section TestCases

-- Test case 1: All elements are the same (from problem examples)
def test1_a : Array Int := #[1, 1, 1]
def test1_Expected : Bool := true

-- Test case 2: Contains different elements
def test2_a : Array Int := #[1, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: Multiple distinct elements in sequence
def test3_a : Array Int := #[3, 4, 5, 6]
def test3_Expected : Bool := false

-- Test case 4: Single element array
def test4_a : Array Int := #[7]
def test4_Expected : Bool := true

-- Test case 5: All zeros
def test5_a : Array Int := #[0, 0, 0, 0]
def test5_Expected : Bool := true

-- Test case 6: Zeros with one different element
def test6_a : Array Int := #[0, 0, 1, 0]
def test6_Expected : Bool := false

-- Test case 7: Negative numbers all same
def test7_a : Array Int := #[-5, -5, -5]
def test7_Expected : Bool := true

-- Test case 8: Negative and positive numbers
def test8_a : Array Int := #[-1, 1, -1]
def test8_Expected : Bool := false

-- Test case 9: Large same values
def test9_a : Array Int := #[1000000, 1000000]
def test9_Expected : Bool := true

-- Test case 10: Two different elements
def test10_a : Array Int := #[42, 43]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 4

end TestCases
