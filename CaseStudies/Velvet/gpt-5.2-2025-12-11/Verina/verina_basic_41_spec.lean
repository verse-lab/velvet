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
    hasOnlyOneDistinctElement: determine whether an array of integers contains only one distinct element.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. The output is a Boolean.
    3. The result is true if the array is empty.
    4. The result is true if the array is nonempty and every element equals the first element.
    5. The result is false if there exist two indices in range whose elements are different.
    6. Arrays are assumed non-null (always true in Lean); no additional input validity is required.
-/

section Specs

-- `atMostOneDistinct a` means: `a` has at most one distinct value.
-- This is characterized observationally:
-- - if the array is empty, the property holds;
-- - otherwise every element equals the first element.
-- (This matches “only one distinct element” while also treating empty as true.)
def atMostOneDistinct (a : Array Int) : Prop :=
  a.size = 0 ∨ (∀ (i : Nat), i < a.size → a[i]! = a[0]!)

-- No preconditions: empty arrays are allowed by the problem statement.
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is true iff the array is empty or all elements equal the first element.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  result ↔ atMostOneDistinct a

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

-- Test case 1: provided example, all equal
-- IMPORTANT: If the problem description contains an example, this must be test case 1.
def test1_a : Array Int := #[1, 1, 1]
def test1_Expected : Bool := true

-- Test case 2: provided example, has at least two distinct elements
def test2_a : Array Int := #[1, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: provided example, many distinct
def test3_a : Array Int := #[3, 4, 5, 6]
def test3_Expected : Bool := false

-- Test case 4: provided example, single element
def test4_a : Array Int := #[7]
def test4_Expected : Bool := true

-- Test case 5: provided example, all zeros
def test5_a : Array Int := #[0, 0, 0, 0]
def test5_Expected : Bool := true

-- Test case 6: provided example, one different among equals
def test6_a : Array Int := #[0, 0, 1, 0]
def test6_Expected : Bool := false

-- Test case 7: empty array (edge case; per description result should be true)
def test7_a : Array Int := #[]
def test7_Expected : Bool := true

-- Test case 8: negative values all equal
def test8_a : Array Int := #[-2, -2, -2]
def test8_Expected : Bool := true

-- Test case 9: two elements different (includes negative)
def test9_a : Array Int := #[5, -5]
def test9_Expected : Bool := false

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test2, test7

end TestCases
