import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasCommonElement: Check whether two arrays of integers have any elements in common
    Natural language breakdown:
    1. We have two input arrays of integers, a and b
    2. The function should return true if there exists at least one element that appears in both arrays
    3. The function should return false if no element appears in both arrays
    4. "Common element" means there exists some integer x such that x is in array a AND x is in array b
    5. Both arrays are assumed to be non-null (non-empty based on reject inputs)
    6. The position of elements doesn't matter - we only check for existence
    7. Duplicate elements within an array don't affect the result
    
    Property-oriented specification:
    - If result is true: there exists some element x such that x ∈ a.toList and x ∈ b.toList
    - If result is false: for all elements x, if x ∈ a.toList then x ∉ b.toList
-/

section Specs

-- Helper Functions

-- Predicate: check if two arrays have at least one common element
def hasCommon (a : Array Int) (b : Array Int) : Prop :=
  ∃ x : Int, x ∈ a.toList ∧ x ∈ b.toList

-- Postcondition clauses
def ensures1 (a : Array Int) (b : Array Int) (result : Bool) :=
  result = true ↔ hasCommon a b

-- Precondition: both arrays must be non-empty
def precondition (a : Array Int) (b : Array Int) :=
  a.size > 0 ∧ b.size > 0

def postcondition (a : Array Int) (b : Array Int) (result : Bool) :=
  ensures1 a b result

end Specs

section Impl

method hasCommonElement (a : Array Int) (b : Array Int)
  return (result : Bool)
  require precondition a b
  ensures postcondition a b result
  do
  pure false

end Impl

section TestCases

-- Test case 1: No common elements between disjoint arrays
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Bool := false

-- Test case 2: Common element at the boundary (3 appears in both)
def test2_a : Array Int := #[1, 2, 3]
def test2_b : Array Int := #[3, 4, 5]
def test2_Expected : Bool := true

-- Test case 3: Common element in different positions
def test3_a : Array Int := #[7, 8, 9]
def test3_b : Array Int := #[10, 11, 7]
def test3_Expected : Bool := true

-- Test case 4: Larger disjoint arrays
def test4_a : Array Int := #[1, 2, 3, 4]
def test4_b : Array Int := #[5, 6, 7, 8]
def test4_Expected : Bool := false

-- Test case 5: Common element at the end of first array
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[4, 5, 6]
def test5_Expected : Bool := true

-- Test case 6: Arrays with duplicate elements, common element exists
def test6_a : Array Int := #[1, 1, 1]
def test6_b : Array Int := #[1, 2, 1]
def test6_Expected : Bool := true

-- Test case 7: Single element arrays with same value
def test7_a : Array Int := #[0]
def test7_b : Array Int := #[0]
def test7_Expected : Bool := true

-- Test case 8: Single element array vs two elements, no common
def test8_a : Array Int := #[0]
def test8_b : Array Int := #[-1, 1]
def test8_Expected : Bool := false

-- Test case 9: Negative numbers with common element
def test9_a : Array Int := #[-5, -3, -1]
def test9_b : Array Int := #[-3, 0, 3]
def test9_Expected : Bool := true

-- Test case 10: Mixed positive and negative, no common
def test10_a : Array Int := #[-2, -1, 0]
def test10_b : Array Int := #[1, 2, 3]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 7

end TestCases

