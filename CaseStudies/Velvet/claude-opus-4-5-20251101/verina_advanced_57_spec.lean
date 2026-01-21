import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- nextGreaterElement: Find the next greater element for each element in nums1 as it appears in nums2
--
-- Natural language breakdown:
-- 1. We are given two distinct 0-indexed integer arrays nums1 and nums2
-- 2. nums1 is a subset of nums2 (every element in nums1 appears in nums2)
-- 3. All integers in both arrays are unique (no duplicates within each array)
-- 4. For each element x in nums1, we find its position in nums2
-- 5. The next greater element of x is the first element greater than x that appears to the right of x in nums2
-- 6. If no such element exists, the result is -1
-- 7. The output has the same length as nums1
-- 8. Example: nums1 = [4, 1, 2], nums2 = [1, 3, 4, 2]
--    - 4 is at index 2 in nums2, elements to the right are [2], none > 4, so result is -1
--    - 1 is at index 0 in nums2, elements to the right are [3, 4, 2], first > 1 is 3
--    - 2 is at index 3 in nums2, no elements to the right, so result is -1
--    - Output: [-1, 3, -1]

section Specs

-- Helper: check if all elements in list are unique
def allUnique (l : List Int) : Prop :=
  l.Nodup

-- Helper: check if list1 is a subset of list2
def isSubsetOf (l1 : List Int) (l2 : List Int) : Prop :=
  ∀ x, x ∈ l1 → x ∈ l2

-- Precondition clauses
def require1 (nums1 : List Int) (_nums2 : List Int) :=
  allUnique nums1

def require2 (_nums1 : List Int) (nums2 : List Int) :=
  allUnique nums2

def require3 (nums1 : List Int) (nums2 : List Int) :=
  isSubsetOf nums1 nums2

-- Postcondition clauses
-- The result has the same length as nums1
def ensures1 (nums1 : List Int) (_nums2 : List Int) (result : List Int) :=
  result.length = nums1.length

-- Property-based specification for next greater element
-- For each index i in result:
-- Case 1: result[i] = -1 means no element greater than nums1[i] exists after nums1[i]'s position in nums2
-- Case 2: result[i] ≠ -1 means result[i] is the first element greater than nums1[i] after its position in nums2
def ensures2 (nums1 : List Int) (nums2 : List Int) (result : List Int) :=
  ∀ i : Nat, i < nums1.length →
    let x := nums1[i]!
    let xPos := nums2.findIdx (· == x)
    -- Either result is -1 and no greater element exists after xPos
    (result[i]! = -1 ∧ 
     ∀ j : Nat, xPos < j → j < nums2.length → nums2[j]! ≤ x) ∨
    -- Or result is the first greater element after xPos
    (result[i]! ≠ -1 ∧ 
     ∃ k : Nat, xPos < k ∧ k < nums2.length ∧ 
          nums2[k]! = result[i]! ∧ 
          result[i]! > x ∧
          ∀ j : Nat, xPos < j → j < k → nums2[j]! ≤ x)

def precondition (nums1 : List Int) (nums2 : List Int) :=
  require1 nums1 nums2 ∧ require2 nums1 nums2 ∧ require3 nums1 nums2

def postcondition (nums1 : List Int) (nums2 : List Int) (result : List Int) :=
  ensures1 nums1 nums2 result ∧ ensures2 nums1 nums2 result

end Specs

section Impl

method nextGreaterElement (nums1 : List Int) (nums2 : List Int)
  return (result : List Int)
  require precondition nums1 nums2
  ensures postcondition nums1 nums2 result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem description
def test1_nums1 : List Int := [4, 1, 2]
def test1_nums2 : List Int := [1, 3, 4, 2]
def test1_Expected : List Int := [-1, 3, -1]

-- Test case 2: Sequential elements with next greater
def test2_nums1 : List Int := [2, 4]
def test2_nums2 : List Int := [1, 2, 3, 4]
def test2_Expected : List Int := [3, -1]

-- Test case 3: Single element with next greater
def test3_nums1 : List Int := [1]
def test3_nums2 : List Int := [1, 2]
def test3_Expected : List Int := [2]

-- Test case 4: Single element, descending sequence (no next greater)
def test4_nums1 : List Int := [5]
def test4_nums2 : List Int := [5, 4, 3, 2, 1]
def test4_Expected : List Int := [-1]

-- Test case 5: All elements in descending order, none have next greater
def test5_nums1 : List Int := [1, 3, 5, 2, 4]
def test5_nums2 : List Int := [6, 5, 4, 3, 2, 1]
def test5_Expected : List Int := [-1, -1, -1, -1, -1]

-- Test case 6: Multiple elements all have the same next greater
def test6_nums1 : List Int := [1, 2, 3]
def test6_nums2 : List Int := [3, 2, 1, 4]
def test6_Expected : List Int := [4, 4, 4]

-- Test case 7: nums1 equals nums2, descending order
def test7_nums1 : List Int := [4, 3, 2, 1]
def test7_nums2 : List Int := [4, 3, 2, 1]
def test7_Expected : List Int := [-1, -1, -1, -1]

-- Test case 8: Ascending sequence where each has next greater
def test8_nums1 : List Int := [1, 2, 3, 4]
def test8_nums2 : List Int := [1, 2, 3, 4, 5]
def test8_Expected : List Int := [2, 3, 4, 5]

-- Test case 9: Mixed case with interleaved elements
def test9_nums1 : List Int := [3, 1]
def test9_nums2 : List Int := [1, 5, 3, 4, 2]
def test9_Expected : List Int := [4, 5]

-- Test case 10: Single element arrays
def test10_nums1 : List Int := [7]
def test10_nums2 : List Int := [7]
def test10_Expected : List Int := [-1]

-- Recommend to validate: 1, 2, 6

end TestCases
