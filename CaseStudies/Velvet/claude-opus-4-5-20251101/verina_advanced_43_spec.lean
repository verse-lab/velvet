import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxStrength: Given a non-empty list of integers representing student scores,
    find the maximum product of any non-empty subset of scores.
    
    Natural language breakdown:
    1. We have a non-empty list of integers (student scores)
    2. We need to consider all possible non-empty subsets of this list
    3. For each non-empty subset, compute the product of all elements in it
    4. The result is the maximum product among all these non-empty subsets
    5. A subset is characterized by a selector function on indices
    6. Key properties:
       - The result must be achievable: there exists some non-empty subset whose product equals result
       - The result must be maximal: no non-empty subset has a larger product
    7. Edge cases:
       - Single element list: result is that element
       - All negative numbers: result could be product of even count or the largest negative
       - Contains zeros: zeros might be excluded to maximize product
       - Mix of positive and negative: select all positives and even number of negatives
-/

section Specs

-- Helper function to compute product of selected elements based on a selector
-- selector i = true means element at index i is selected
def selectedProduct (nums : List Int) (selector : Nat → Bool) : Int :=
  (List.range nums.length).foldl 
    (fun acc i => if selector i then acc * nums[i]! else acc) 
    1

-- A selection is non-empty if at least one index is selected
def isNonEmptySelection (nums : List Int) (selector : Nat → Bool) : Prop :=
  ∃ i : Nat, i < nums.length ∧ selector i = true

-- Property: result is achievable (equals the product of some non-empty subset)
def isAchievable (nums : List Int) (result : Int) : Prop :=
  ∃ selector : Nat → Bool, 
    isNonEmptySelection nums selector ∧ 
    selectedProduct nums selector = result

-- Property: result is maximal (greater than or equal to all non-empty subset products)
def isMaximal (nums : List Int) (result : Int) : Prop :=
  ∀ selector : Nat → Bool, 
    isNonEmptySelection nums selector → 
    selectedProduct nums selector ≤ result

-- Precondition: the list must be non-empty
def precondition (nums : List Int) : Prop :=
  nums.length > 0

-- Postcondition: result is the maximum product of any non-empty subset
def postcondition (nums : List Int) (result : Int) : Prop :=
  isAchievable nums result ∧ isMaximal nums result

end Specs

section Impl

method maxStrength (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Single negative element
def test1_nums : List Int := [-2]
def test1_Expected : Int := -2

-- Test case 2: Mix of positive and negative numbers
def test2_nums : List Int := [3, -1, -5, 2, 5, -9]
def test2_Expected : Int := 1350

-- Test case 3: All negative numbers
def test3_nums : List Int := [-4, -5, -4]
def test3_Expected : Int := 20

-- Test case 4: Contains zero
def test4_nums : List Int := [0, -3, 4]
def test4_Expected : Int := 4

-- Test case 5: Small values with mixed signs
def test5_nums : List Int := [1, -1, -1]
def test5_Expected : Int := 1

-- Test case 6: Single positive element
def test6_nums : List Int := [7]
def test6_Expected : Int := 7

-- Test case 7: All positive numbers
def test7_nums : List Int := [2, 3, 4]
def test7_Expected : Int := 24

-- Test case 8: Two negative numbers (product is positive)
def test8_nums : List Int := [-3, -5]
def test8_Expected : Int := 15

-- Test case 9: Contains zero with negatives (zero is the best choice)
def test9_nums : List Int := [0, -1]
def test9_Expected : Int := 0

-- Test case 10: Large mix
def test10_nums : List Int := [1, 2, -3, 4, -5]
def test10_Expected : Int := 120

-- Recommend to validate: 1, 2, 4

end TestCases
