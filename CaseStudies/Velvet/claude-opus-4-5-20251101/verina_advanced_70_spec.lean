import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    semiOrderedPermutation: Determine the minimum number of adjacent swaps needed to make a permutation semi-ordered
    
    Natural language breakdown:
    1. Input is a permutation of [1, 2, ..., n] where n is the length of the list
    2. A permutation is semi-ordered if the first element is 1 and the last element is n
    3. We can only perform adjacent swaps (swap elements at positions i and i+1)
    4. The goal is to find the minimum number of such swaps needed
    5. Key insight for the formula:
       - Element 1 must move from its current position (idx1) to position 0
       - Element n must move from its current position (idxN) to position n-1
       - Moving 1 to the front requires exactly idx1 swaps
       - Moving n to the end requires exactly (n - 1 - idxN) swaps
       - If idx1 > idxN (1 appears after n in the original list), moving them causes them to cross
       - When they cross, one swap accomplishes movement for both, saving 1 swap
    6. Preconditions:
       - List must be non-empty
       - List must be a valid permutation of [1..n]
       - All elements are distinct and in range [1, n]
    7. Postconditions (property-based):
       - The result is non-negative
       - The result is 0 if and only if the permutation is already semi-ordered
       - The result equals the sum of distances 1 and n must travel, minus 1 if they cross
-/

section Specs

-- Helper: Check if list contains all integers from 1 to n exactly once (valid permutation)
def isValidPermutation (nums : List Int) : Prop :=
  let n := nums.length
  n > 0 ∧
  (∀ x, x ∈ nums → 1 ≤ x ∧ x ≤ n) ∧
  nums.Nodup ∧
  (∀ k : Nat, 1 ≤ k ∧ k ≤ n → (k : Int) ∈ nums)

-- Helper: Find the index of an element in the list
def findIndex (nums : List Int) (val : Int) : Nat :=
  nums.findIdx (· == val)

-- Helper: Check if permutation is already semi-ordered
def isSemiOrdered (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums[0]! = 1 ∧ nums[nums.length - 1]! = (nums.length : Int)

-- Helper: Perform one adjacent swap at position i (swap elements at i and i+1)
def swapAt (nums : List Int) (i : Nat) : List Int :=
  if i + 1 < nums.length then
    nums.set i (nums[i + 1]!) |>.set (i + 1) (nums[i]!)
  else
    nums

-- Precondition: nums must be a valid permutation of [1..n]
def precondition (nums : List Int) : Prop :=
  isValidPermutation nums

-- Postcondition: result is the minimum number of adjacent swaps to make permutation semi-ordered
-- Property-based specification using positions of 1 and n:
-- 1. Result is non-negative
-- 2. Result is 0 iff already semi-ordered
-- 3. Let idx1 = position of 1, idxN = position of n
--    - Distance for 1 to reach front = idx1
--    - Distance for n to reach end = (n - 1) - idxN  
--    - If idx1 > idxN, they cross during movement, saving 1 swap
-- 4. Result equals idx1 + ((n-1) - idxN) - (if idx1 > idxN then 1 else 0)
def postcondition (nums : List Int) (result : Int) : Prop :=
  let n := nums.length
  let idx1 := findIndex nums 1
  let idxN := findIndex nums (n : Int)
  -- Result is non-negative
  result ≥ 0 ∧
  -- Result is 0 iff already semi-ordered (1 at front, n at end)
  (result = 0 ↔ isSemiOrdered nums) ∧
  -- Position constraints: idx1 steps to move 1 to front, (n-1-idxN) steps to move n to end
  -- If 1 is to the right of n (idx1 > idxN), they cross, saving 1 swap
  (idx1 ≤ idxN → result = (idx1 : Int) + ((n - 1 : Int) - (idxN : Int))) ∧
  (idx1 > idxN → result = (idx1 : Int) + ((n - 1 : Int) - (idxN : Int)) - 1)

end Specs

section Impl

method semiOrderedPermutation (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: [2, 1, 4, 3] - example from problem
-- 1 is at index 1, 4 is at index 2, n = 4
-- idx1 = 1, idxN = 2, no crossing (idx1 < idxN)
-- result = 1 + (4 - 1 - 2) - 0 = 1 + 1 = 2
def test1_nums : List Int := [2, 1, 4, 3]
def test1_Expected : Int := 2

-- Test case 2: [2, 4, 1, 3] - another example from problem
-- 1 is at index 2, 4 is at index 1, n = 4
-- idx1 = 2, idxN = 1, crossing (idx1 > idxN)
-- result = 2 + (4 - 1 - 1) - 1 = 2 + 2 - 1 = 3
def test2_nums : List Int := [2, 4, 1, 3]
def test2_Expected : Int := 3

-- Test case 3: [1, 3, 4, 2, 5] - already semi-ordered
-- 1 is at index 0, 5 is at index 4, n = 5
-- idx1 = 0, idxN = 4, no crossing
-- result = 0 + (5 - 1 - 4) - 0 = 0 + 0 = 0
def test3_nums : List Int := [1, 3, 4, 2, 5]
def test3_Expected : Int := 0

-- Test case 4: [3, 1, 2] - from test cases
-- 1 is at index 1, 3 is at index 0, n = 3
-- idx1 = 1, idxN = 0, crossing (idx1 > idxN)
-- result = 1 + (3 - 1 - 0) - 1 = 1 + 2 - 1 = 2
def test4_nums : List Int := [3, 1, 2]
def test4_Expected : Int := 2

-- Test case 5: [2, 3, 1, 5, 4] - from test cases
-- 1 is at index 2, 5 is at index 3, n = 5
-- idx1 = 2, idxN = 3, no crossing (idx1 < idxN)
-- result = 2 + (5 - 1 - 3) - 0 = 2 + 1 = 3
def test5_nums : List Int := [2, 3, 1, 5, 4]
def test5_Expected : Int := 3

-- Test case 6: [1, 2] - minimal already semi-ordered
-- 1 at index 0, 2 at index 1, n = 2
-- idx1 = 0, idxN = 1, no crossing
-- result = 0 + (2 - 1 - 1) - 0 = 0 + 0 = 0
def test6_nums : List Int := [1, 2]
def test6_Expected : Int := 0

-- Test case 7: [2, 1] - minimal needing swaps with crossing
-- 1 at index 1, 2 at index 0, n = 2
-- idx1 = 1, idxN = 0, crossing (idx1 > idxN)
-- result = 1 + (2 - 1 - 0) - 1 = 1 + 1 - 1 = 1
def test7_nums : List Int := [2, 1]
def test7_Expected : Int := 1

-- Test case 8: [5, 4, 3, 2, 1] - reverse order
-- 1 at index 4, 5 at index 0, n = 5
-- idx1 = 4, idxN = 0, crossing (idx1 > idxN)
-- result = 4 + (5 - 1 - 0) - 1 = 4 + 4 - 1 = 7
def test8_nums : List Int := [5, 4, 3, 2, 1]
def test8_Expected : Int := 7

-- Test case 9: [1] - single element (already semi-ordered)
-- Element 1 is both the first and last, n = 1
-- idx1 = 0, idxN = 0, no crossing (equal)
-- result = 0 + (1 - 1 - 0) - 0 = 0 + 0 = 0
def test9_nums : List Int := [1]
def test9_Expected : Int := 0

-- Test case 10: [3, 2, 1, 4] - 1 at end of first half, n at last position
-- 1 at index 2, 4 at index 3, n = 4
-- idx1 = 2, idxN = 3, no crossing (idx1 < idxN)
-- result = 2 + (4 - 1 - 3) - 0 = 2 + 0 = 2
def test10_nums : List Int := [3, 2, 1, 4]
def test10_Expected : Int := 2

-- Recommend to validate: 1, 2, 4

end TestCases
