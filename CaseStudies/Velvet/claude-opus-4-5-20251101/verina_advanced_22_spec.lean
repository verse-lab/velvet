import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPeakValley: Determine if a list of integers follows a peak-valley pattern
    Natural language breakdown:
    1. A list follows the peak-valley pattern if it strictly increases first, then strictly decreases
    2. Both the increasing part and decreasing part must be non-empty
    3. This means there must be a peak index k where:
       - All elements before k are strictly increasing (indices 0 to k)
       - All elements after k are strictly decreasing (indices k to end)
    4. The list must have at least 3 elements (at least one element in increasing part before peak,
       the peak itself, and at least one element in decreasing part after peak)
    5. No consecutive equal elements are allowed (must be strictly increasing then strictly decreasing)
    6. Examples:
       - [1, 3, 5, 4, 2] -> true (increases: 1<3<5, decreases: 5>4>2)
       - [1, 2, 3] -> false (only increasing, no decreasing part)
       - [5, 4, 3] -> false (only decreasing, no increasing part)
       - [1, 2, 2, 1] -> false (contains equal consecutive elements)
-/

section Specs

-- Helper: Check if a portion of a list is strictly increasing (from index i to j inclusive)
def isStrictlyIncreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! < lst[k + 1]!

-- Helper: Check if a portion of a list is strictly decreasing (from index i to j inclusive)
def isStrictlyDecreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! > lst[k + 1]!

-- Helper: Check if there exists a valid peak index
def hasPeakValleyStructure (lst : List Int) : Prop :=
  ∃ peakIdx : Nat, 
    peakIdx > 0 ∧ 
    peakIdx < lst.length - 1 ∧
    isStrictlyIncreasingRange lst 0 peakIdx ∧
    isStrictlyDecreasingRange lst peakIdx (lst.length - 1)

def precondition (lst : List Int) :=
  True  -- no preconditions

def postcondition (lst : List Int) (result : Bool) :=
  result = true ↔ hasPeakValleyStructure lst

end Specs

section Impl

method isPeakValley (lst : List Int)
  return (result : Bool)
  require precondition lst
  ensures postcondition lst result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic peak-valley pattern (from problem examples)
def test1_lst : List Int := [1, 3, 5, 2, 1]
def test1_Expected : Bool := true

-- Test case 2: Only increasing, no decreasing part
def test2_lst : List Int := [1, 2, 3, 4, 5]
def test2_Expected : Bool := false

-- Test case 3: Empty list
def test3_lst : List Int := []
def test3_Expected : Bool := false

-- Test case 4: Single element
def test4_lst : List Int := [1]
def test4_Expected : Bool := false

-- Test case 5: All equal elements (no strict increase/decrease)
def test5_lst : List Int := [1, 1, 1, 1, 1]
def test5_Expected : Bool := false

-- Test case 6: Valid peak-valley with large jump
def test6_lst : List Int := [1, 10, 100, 1]
def test6_Expected : Bool := true

-- Test case 7: Only decreasing, no increasing part
def test7_lst : List Int := [5, 4, 3, 2, 1]
def test7_Expected : Bool := false

-- Test case 8: Two elements (cannot have both increasing and decreasing parts)
def test8_lst : List Int := [1, 2]
def test8_Expected : Bool := false

-- Test case 9: Three elements forming valid peak
def test9_lst : List Int := [1, 3, 2]
def test9_Expected : Bool := true

-- Test case 10: Has equal consecutive elements (from problem examples)
def test10_lst : List Int := [1, 2, 2, 1]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 6, 9

end TestCases
