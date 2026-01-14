import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 34: Write a Velvet function to find the missing number in a sorted array
--
-- **SPECIFICATION ASSUMPTIONS:**
-- This specification assumes the array contains consecutive integers with exactly one missing element,
-- where the missing element lies strictly between the minimum and maximum values present in the array.
--
-- **IMPORTANT LIMITATION:**
-- This specification cannot detect missing numbers at sequence boundaries:
-- - Example 1: [2, 3, 4] missing 1 (before the first element) - NOT DETECTED
-- - Example 2: [1, 2, 3] missing 4 (after the last element) - NOT DETECTED
-- - Example 3: [1, 3, 4, 5] missing 2 (between min and max) - DETECTED ✓
--
-- This is an intentional design choice: without additional context about the expected range,
-- boundary missing numbers cannot be uniquely determined. The specification focuses on the
-- unambiguous case where the missing number lies strictly within the observed range.
--
-- Natural language breakdown:
-- 1. We have a sorted array containing consecutive integers with exactly one number missing
-- 2. The array should contain n elements representing n+1 consecutive integers with one gap
-- 3. For example: [1, 2, 4, 5, 6] is missing 3, [0, 1, 3, 4] is missing 2
-- 4. The consecutive integers form an arithmetic sequence with difference 1
-- 5. Key properties that define the problem:
--    a. The array must be sorted in ascending order
--    b. The array must have at least 2 elements (to uniquely determine the sequence)
--    c. Adjacent elements differ by 1 or 2 (where difference is 2, the missing number lies between)
--    d. There is exactly one position where adjacent elements differ by 2
-- 6. The missing number must satisfy:
--    a. It lies strictly between the minimum and maximum values in the array
--    b. It does not appear in the array
--    c. When inserted, it would maintain the consecutive integer property
-- 7. This is a property-oriented specification: we specify what the missing number must satisfy,
--    not how to find it (e.g., binary search, arithmetic formula, or linear scan)
-- 8. Edge cases handled:
--    - Array with 2 elements: Minimum valid size, uniquely determines missing number
--    - Negative numbers: Specification works for any integer range
--    - Large numbers: No assumption on the magnitude of values

-- Helper definition: check if a value is in the array

section Specs

-- Helper Functions

def inArray (arr: Array Int) (val: Int) : Prop :=
  ∃ i, i < arr.size ∧ arr[i]! = val

-- Helper definition: check if array is sorted in ascending order
def isSorted (arr: Array Int) : Prop :=
  ∀ i j, i < j → j < arr.size → arr[i]! < arr[j]!

-- Helper definition: check if array elements differ by at most 2
def adjacentDiffAtMostTwo (arr: Array Int) : Prop :=
  ∀ i, i + 1 < arr.size → arr[i + 1]! - arr[i]! ≤ 2

-- Helper definition: check if array elements differ by at least 1
def adjacentDiffAtLeastOne (arr: Array Int) : Prop :=
  ∀ i, i + 1 < arr.size → arr[i + 1]! - arr[i]! ≥ 1

-- Helper definition: there exists exactly one position where adjacent elements differ by 2
def hasExactlyOneGap (arr: Array Int) : Prop :=
  (∃ k, k + 1 < arr.size ∧ arr[k + 1]! - arr[k]! = 2) ∧
  (∀ i j, i + 1 < arr.size → j + 1 < arr.size →
    arr[i + 1]! - arr[i]! = 2 → arr[j + 1]! - arr[j]! = 2 → i = j)

def require1 (arr : Array Int) :=
  arr.size ≥ 2  -- Need at least 2 elements to determine the sequence
def require2 (arr : Array Int) :=
  isSorted arr  -- Array must be sorted
def require3 (arr : Array Int) :=
  adjacentDiffAtLeastOne arr  -- Elements are distinct (strictly increasing)
def require4 (arr : Array Int) :=
  adjacentDiffAtMostTwo arr  -- Adjacent elements differ by at most 2
def require5 (arr : Array Int) :=
  hasExactlyOneGap arr  -- Exactly one gap of size 2
  -- The missing number is not in the array

-- Postcondition clauses
def ensures1 (arr : Array Int) (missing : Int) :=
  ¬inArray arr missing
def ensures2 (arr : Array Int) (missing : Int) :=
  arr[0]! < missing ∧ missing < arr[arr.size - 1]!
def ensures3 (arr : Array Int) (missing : Int) :=
  ∃ k, k + 1 < arr.size ∧ arr[k + 1]! - arr[k]! = 2 ∧ missing = arr[k]! + 1

def precondition (arr : Array Int) :=
  require1 arr ∧require2 arr ∧require3 arr ∧require4 arr ∧require5 arr
def postcondition (arr : Array Int) (missing : Int) :=
  ensures1 arr missing ∧
  ensures2 arr missing ∧
  ensures3 arr missing

end Specs

section Impl

method FindMissingNumber (arr: Array Int)
  return (missing: Int)
  require precondition arr
  ensures postcondition arr missing
  do
    sorry

prove_correct FindMissingNumber by sorry

-- Test cases for specification validation
end Impl

section TestCases

-- Test case 0
def test0_arr : Array Int := #[1, 2, 3, 5]
def test0_Expected : Int := 4

-- Test case 1
def test1_arr : Array Int := #[1, 2, 4, 5, 6]
def test1_Expected : Int := 3

-- Test case 2
def test2_arr : Array Int := #[0, 1, 3, 4, 5]
def test2_Expected : Int := 2

-- Test case 3
def test3_arr : Array Int := #[10, 11, 12, 13, 15]
def test3_Expected : Int := 14

-- Test case 4
def test4_arr : Array Int := #[-5, -3, -2, -1]
def test4_Expected : Int := -4

-- Test case 5
def test5_arr : Array Int := #[1, 2, 3, 4, 5, 7, 8, 9, 10]
def test5_Expected : Int := 6

-- Test case 6
def test6_arr : Array Int := #[0, 2, 3, 4, 5]
def test6_Expected : Int := 1

-- Test case 7
def test7_arr : Array Int := #[100, 101, 102, 104, 105, 106]
def test7_Expected : Int := 103

-- Test case 8
def test8_arr : Array Int := #[5, 7]
def test8_Expected : Int := 6

-- Recommend to validate: 0,1,2,3,4,8

-- Verification that our specification captures the correct behavior:
-- 1. The result is not in the array (it's the missing number)
-- 2. The result lies strictly between the min and max of the array
-- 3. The result fills exactly the one gap where adjacent elements differ by 2
-- 4. Works correctly with negative numbers, zero, and positive numbers
-- 5. Works correctly regardless of where the missing number is (near start, middle, near end)
-- 6. Works correctly with the minimum valid array size (2 elements) - Test case 8
-- 7. The specification is property-oriented: it defines what properties the missing number
--    must have (not in array, fills the unique gap of size 2), rather than prescribing
--    a particular algorithm (e.g., binary search, arithmetic sum, or linear scan)
-- 8. Limitation acknowledged: Cannot detect missing numbers at sequence boundaries
--    (before first element or after last element) without additional context

end TestCases
