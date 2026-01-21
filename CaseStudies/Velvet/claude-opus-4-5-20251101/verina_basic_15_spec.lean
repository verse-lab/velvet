import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsConsecutiveNumbers: Determine whether an array contains at least one pair of consecutive numbers
    Natural language breakdown:
    1. We have an input array of integers
    2. "Consecutive numbers" means two adjacent elements where the first element plus one equals the second
    3. We need to check if there exists any index i such that a[i] + 1 = a[i+1]
    4. The function returns true if at least one such consecutive pair exists
    5. The function returns false if no consecutive pair exists
    6. Edge case: Empty array returns false (no pairs to check)
    7. Edge case: Single element array returns false (no adjacent pairs)
    8. The check is about values being consecutive integers, not about array positions
-/

section Specs

-- Helper Functions

-- Predicate: check if there exists a consecutive pair in the array
-- A consecutive pair is when a[i] + 1 = a[i+1] for some valid index i
def hasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

-- Postcondition clause
def ensures1 (a : Array Int) (result : Bool) :=
  result = true ↔ hasConsecutivePair a

def precondition (a : Array Int) :=
  True  -- no preconditions

def postcondition (a : Array Int) (result : Bool) :=
  ensures1 a result

end Specs

section Impl

method containsConsecutiveNumbers (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
    pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: Array with consecutive pair at the beginning (from problem example)
def test1_a : Array Int := #[1, 2, 3, 5]
def test1_Expected : Bool := true

-- Test case 2: Array with no consecutive pairs
def test2_a : Array Int := #[1, 3, 5, 7]
def test2_Expected : Bool := false

-- Test case 3: Empty array
def test3_a : Array Int := #[]
def test3_Expected : Bool := false

-- Test case 4: Single element array
def test4_a : Array Int := #[10]
def test4_Expected : Bool := false

-- Test case 5: Two element array with consecutive pair
def test5_a : Array Int := #[5, 6]
def test5_Expected : Bool := true

-- Test case 6: Consecutive pair in the middle
def test6_a : Array Int := #[5, 7, 8, 10]
def test6_Expected : Bool := true

-- Test case 7: Consecutive pair with duplicate before it
def test7_a : Array Int := #[9, 9, 10]
def test7_Expected : Bool := true

-- Test case 8: All same elements (no consecutive pair)
def test8_a : Array Int := #[3, 3, 3]
def test8_Expected : Bool := false

-- Test case 9: Negative consecutive numbers
def test9_a : Array Int := #[-3, -2, 0, 5]
def test9_Expected : Bool := true

-- Test case 10: Descending order (no consecutive pairs in forward direction)
def test10_a : Array Int := #[5, 4, 3, 2]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 5

end TestCases

