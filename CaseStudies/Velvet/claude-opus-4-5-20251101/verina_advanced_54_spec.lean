import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- missingNumber: Find the one missing number in a list of distinct natural numbers from 0 to n
--
-- Natural language breakdown:
-- 1. We have a list of n distinct natural numbers
-- 2. The numbers are from the range [0, n], where n = nums.length
-- 3. Exactly one number in the range [0, n] is missing from the list
-- 4. All numbers in the list are distinct (no duplicates)
-- 5. All numbers in the list are within the valid range [0, n]
-- 6. The result is the unique number in [0, n] that is not in the list
--
-- Key properties:
-- - The list has length n, and valid range is [0, n] (n+1 numbers total, one missing)
-- - The missing number must not be in the list
-- - The missing number must be in the range [0, nums.length]
-- - All other numbers in [0, nums.length] must be in the list

section Specs

-- Helper definition: all elements in list are distinct (no duplicates)
def allDistinct (nums : List Nat) : Prop :=
  nums.Nodup

-- Helper definition: all elements are within valid range [0, n]
def allInRange (nums : List Nat) (n : Nat) : Prop :=
  ∀ x, x ∈ nums → x ≤ n

-- Precondition: the list contains distinct elements all in range [0, n]
def precondition (nums : List Nat) :=
  allDistinct nums ∧ allInRange nums nums.length

-- Postcondition clauses
-- 1. The result is not in the list
def ensures1 (nums : List Nat) (result : Nat) :=
  result ∉ nums

-- 2. The result is in the valid range [0, n]
def ensures2 (nums : List Nat) (result : Nat) :=
  result ≤ nums.length

-- 3. Every other number in [0, n] is in the list (uniqueness)
def ensures3 (nums : List Nat) (result : Nat) :=
  ∀ k, k ≤ nums.length → k ≠ result → k ∈ nums

def postcondition (nums : List Nat) (result : Nat) :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result

end Specs

section Impl

method missingNumber (nums : List Nat)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: [3, 0, 1] missing 2 (from problem description)
def test1_nums : List Nat := [3, 0, 1]
def test1_Expected : Nat := 2

-- Test case 2: [0, 1] missing 2
def test2_nums : List Nat := [0, 1]
def test2_Expected : Nat := 2

-- Test case 3: [9, 6, 4, 2, 3, 5, 7, 0, 1] missing 8
def test3_nums : List Nat := [9, 6, 4, 2, 3, 5, 7, 0, 1]
def test3_Expected : Nat := 8

-- Test case 4: [0] missing 1 (smallest non-trivial case, missing at end)
def test4_nums : List Nat := [0]
def test4_Expected : Nat := 1

-- Test case 5: [1] missing 0 (smallest non-trivial case, missing at start)
def test5_nums : List Nat := [1]
def test5_Expected : Nat := 0

-- Test case 6: [1, 2, 3, 4, 5] missing 0 (missing at start of longer list)
def test6_nums : List Nat := [1, 2, 3, 4, 5]
def test6_Expected : Nat := 0

-- Test case 7: [0, 1, 2, 3, 4] missing 5 (missing at end of longer list)
def test7_nums : List Nat := [0, 1, 2, 3, 4]
def test7_Expected : Nat := 5

-- Test case 8: [0, 1, 3, 4, 5, 6, 7] missing in middle
def test8_nums : List Nat := [0, 1, 3, 4, 5, 6, 7]
def test8_Expected : Nat := 2

-- Test case 9: [2, 0] missing 1 (small case with middle missing)
def test9_nums : List Nat := [2, 0]
def test9_Expected : Nat := 1

-- Recommend to validate: 1, 4, 5

end TestCases
