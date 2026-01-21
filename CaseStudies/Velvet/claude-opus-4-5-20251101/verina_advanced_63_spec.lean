import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    removeDuplicates: Count the unique elements from a sorted array
    Natural language breakdown:
    1. We are given a list of integers sorted in non-decreasing order
    2. We need to count how many distinct/unique values are in the list
    3. Since the list is sorted, duplicate values will be adjacent
    4. The result is the number of unique elements (k)
    5. For example: [1, 1, 2] has 2 unique elements (1 and 2)
    6. For example: [0, 0, 1, 1, 1, 2, 2, 3, 3, 4] has 5 unique elements (0, 1, 2, 3, 4)
    7. An empty list has 0 unique elements
    8. A list with all same elements has 1 unique element
    9. A list with all distinct elements has length equal to unique count
    10. Key insight: We use Finset.card to count distinct elements declaratively
    11. The precondition requires the list to be sorted in non-decreasing order
-/

section Specs

-- Helper: Check if list is sorted in non-decreasing order
def isSortedNonDecreasing (nums : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < nums.length → nums[i]! ≤ nums[j]!

-- Precondition: The input list must be sorted in non-decreasing order
def precondition (nums : List Int) : Prop :=
  isSortedNonDecreasing nums

-- Postcondition: The result is the count of unique elements
-- Using Finset.card which gives the cardinality of the set of distinct elements
-- This is a declarative specification that describes what "unique count" means
-- without encoding a specific algorithm for computing it
def postcondition (nums : List Int) (result : Nat) : Prop :=
  result = nums.toFinset.card

end Specs

section Impl

method removeDuplicates (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - [1, 1, 2] has 2 unique elements
def test1_nums : List Int := [1, 1, 2]
def test1_Expected : Nat := 2

-- Test case 2: Example from problem - [0, 0, 1, 1, 1, 2, 2, 3, 3, 4] has 5 unique elements
def test2_nums : List Int := [0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
def test2_Expected : Nat := 5

-- Test case 3: Mixed negative and positive - [-1, -1, 0, 1, 2, 2, 3] has 5 unique elements
def test3_nums : List Int := [-1, -1, 0, 1, 2, 2, 3]
def test3_Expected : Nat := 5

-- Test case 4: All unique elements - [1, 2, 3, 4, 5] has 5 unique elements
def test4_nums : List Int := [1, 2, 3, 4, 5]
def test4_Expected : Nat := 5

-- Test case 5: All same elements - [1, 1, 1, 1] has 1 unique element
def test5_nums : List Int := [1, 1, 1, 1]
def test5_Expected : Nat := 1

-- Test case 6: Empty list - [] has 0 unique elements
def test6_nums : List Int := []
def test6_Expected : Nat := 0

-- Test case 7: Single element - [1] has 1 unique element
def test7_nums : List Int := [1]
def test7_Expected : Nat := 1

-- Test case 8: All negative same elements - [-100, -100, -100] has 1 unique element
def test8_nums : List Int := [-100, -100, -100]
def test8_Expected : Nat := 1

-- Test case 9: Mixed range - [-100, -99, -99, -50, 0, 0, 100, 100] has 5 unique elements
def test9_nums : List Int := [-100, -99, -99, -50, 0, 0, 100, 100]
def test9_Expected : Nat := 5

-- Test case 10: Another mixed case - [-1, 0, 0, 0, 1, 2, 2, 3, 4, 4, 5] has 7 unique elements
def test10_nums : List Int := [-1, 0, 0, 0, 1, 2, 2, 3, 4, 4, 5]
def test10_Expected : Nat := 7

-- Recommend to validate: 1, 2, 6

end TestCases
