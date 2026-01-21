import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    has_close_elements: Determine whether there exists at least one pair of different
    floating-point numbers in a list such that the absolute difference between them
    is less than a given threshold.

    Natural language breakdown:
    1. We have an input list of floating-point numbers
    2. We have a threshold value that defines "closeness"
    3. We need to check if any two distinct elements (at different positions) are "close"
    4. Two elements are "close" if the absolute difference between them is less than threshold
    5. The result is true if at least one such pair exists, false otherwise
    6. An empty list or single-element list has no pairs, so result is false
    7. Preconditions: threshold must be non-negative, all numbers must be valid (non-NaN, non-infinite)

    Property-oriented specification:
    - If result is true: there exist two distinct indices i and j in the list such that
      the absolute difference between the elements at those positions is less than threshold
    - If result is false: for all pairs of distinct indices i and j, the absolute difference
      is greater than or equal to the threshold
-/

section Specs

-- Helper: Check if a Float is valid (not NaN and not infinite)
def isValidFloat (f : Float) : Prop :=
  ¬f.isNaN ∧ ¬f.isInf

-- Helper: Check if all floats in a list are valid
def allValidFloats (numbers : List Float) : Prop :=
  ∀ i, i < numbers.length → isValidFloat numbers[i]!

-- Helper: Check if threshold is valid (non-negative and valid float)
def isValidThreshold (threshold : Float) : Prop :=
  isValidFloat threshold ∧ threshold ≥ 0.0

-- Helper: Absolute difference between two floats
def floatAbsDiff (a : Float) (b : Float) : Float :=
  Float.abs (a - b)

-- Helper: Check if a pair of elements at distinct indices are close
def hasClosePair (numbers : List Float) (threshold : Float) : Prop :=
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧
    floatAbsDiff numbers[i]! numbers[j]! < threshold

-- Precondition: threshold is valid and all numbers are valid floats
def precondition (numbers : List Float) (threshold : Float) :=
  isValidThreshold threshold ∧ allValidFloats numbers

-- Postcondition: result is true iff there exists a close pair
def postcondition (numbers : List Float) (threshold : Float) (result : Bool) :=
  result = true ↔ hasClosePair numbers threshold

end Specs

section Impl

method has_close_elements (numbers : List Float) (threshold : Float)
  return (result : Bool)
  require precondition numbers threshold
  ensures postcondition numbers threshold result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic case with close elements (from problem description)
def test1_numbers : List Float := [1.0, 2.0, 3.0]
def test1_threshold : Float := 1.5
def test1_Expected : Bool := true

-- Test case 2: No close elements
def test2_numbers : List Float := [10.0, 12.0, 15.0]
def test2_threshold : Float := 1.5
def test2_Expected : Bool := false

-- Test case 3: Duplicate elements (difference is 0)
def test3_numbers : List Float := [5.0, 5.0]
def test3_threshold : Float := 0.1
def test3_Expected : Bool := true

-- Test case 4: Empty list
def test4_numbers : List Float := []
def test4_threshold : Float := 2.0
def test4_Expected : Bool := false

-- Test case 5: Multiple elements with one close pair
def test5_numbers : List Float := [0.0, 0.5, 1.1, 2.2]
def test5_threshold : Float := 0.6
def test5_Expected : Bool := true

-- Test case 6: Single element list (no pairs possible)
def test6_numbers : List Float := [42.0]
def test6_threshold : Float := 1.0
def test6_Expected : Bool := false

-- Test case 7: Threshold is zero, no identical elements
def test7_numbers : List Float := [1.0, 2.0, 3.0]
def test7_threshold : Float := 0.0
def test7_Expected : Bool := false

-- Test case 8: Threshold is zero, with identical elements
def test8_numbers : List Float := [1.0, 2.0, 1.0]
def test8_threshold : Float := 0.0
def test8_Expected : Bool := false

-- Test case 9: Exactly at threshold boundary (not close - difference equals threshold)
def test9_numbers : List Float := [1.0, 2.0]
def test9_threshold : Float := 1.0
def test9_Expected : Bool := false

-- Test case 10: Negative numbers with close elements
def test10_numbers : List Float := [-1.0, -0.5, 2.0]
def test10_threshold : Float := 0.6
def test10_Expected : Bool := true

-- Recommend to validate: 1, 3, 4

end TestCases
