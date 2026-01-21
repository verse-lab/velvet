import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

import Init.Data.Array.Lemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasCommonElement: Check whether two arrays of integers share any common element.
    Natural language breakdown:
    1. Inputs are two arrays `a` and `b` containing integers.
    2. The result is a boolean.
    3. The result is true exactly when there exists at least one integer value `x`
       that is an element of `a` and also an element of `b`.
    4. The result is false exactly when there is no integer value present in both arrays.
    5. Reject inputs: both arrays empty are considered invalid for this task.
-/

section Specs

-- Preconditions are intentionally minimal:
-- the only rejected input mentioned is the case where both arrays are empty.

def precondition (a : Array Int) (b : Array Int) : Prop :=
  ¬(a.size = 0 ∧ b.size = 0)

-- Make the precondition decidable so tests can use `decide`.
instance (a : Array Int) (b : Array Int) : Decidable (precondition a b) := by
  dsimp [precondition]
  infer_instance

-- Postcondition: the boolean result matches existence of a common element.
-- We keep `result = true ↔ ...` to avoid relying on any coercion from Bool to Prop.

def postcondition (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  (result = true ↔ (∃ x : Int, x ∈ a ∧ x ∈ b))

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

-- Test case 1: disjoint arrays (example from prompt)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Bool := false

-- Test case 2: common element 3 (example from prompt)
def test2_a : Array Int := #[1, 2, 3]
def test2_b : Array Int := #[3, 4, 5]
def test2_Expected : Bool := true

-- Test case 3: common element 7 (example from prompt)
def test3_a : Array Int := #[7, 8, 9]
def test3_b : Array Int := #[10, 11, 7]
def test3_Expected : Bool := true

-- Test case 4: larger disjoint arrays (example from prompt)
def test4_a : Array Int := #[1, 2, 3, 4]
def test4_b : Array Int := #[5, 6, 7, 8]
def test4_Expected : Bool := false

-- Test case 5: common element 4 (example from prompt)
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[4, 5, 6]
def test5_Expected : Bool := true

-- Test case 6: duplicates in arrays still count as common (example from prompt)
def test6_a : Array Int := #[1, 1, 1]
def test6_b : Array Int := #[1, 2, 1]
def test6_Expected : Bool := true

-- Test case 7: singleton arrays with same element (example from prompt)
def test7_a : Array Int := #[0]
def test7_b : Array Int := #[0]
def test7_Expected : Bool := true

-- Test case 8: singleton vs two elements, no common (example from prompt)
def test8_a : Array Int := #[0]
def test8_b : Array Int := #[-1, 1]
def test8_Expected : Bool := false

-- Test case 9: reject-input example (both empty) as a precondition check
-- Here we test the precondition computation rather than a function output.
def test9_a : Array Int := #[]
def test9_b : Array Int := #[]
def test9_PreconditionHolds : Bool := decide (precondition test9_a test9_b)
def test9_Expected : Bool := false

-- Recommend to validate: 1, 2, 7

end TestCases
