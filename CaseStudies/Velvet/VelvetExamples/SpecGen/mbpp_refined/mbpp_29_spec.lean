import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 29: Write a Velvet function to find the element occurring odd number of times
--
-- Natural language breakdown:
-- 1. We are given a list (or array) of elements
-- 2. We need to find THE element that occurs an odd number of times
-- 3. Key assumption: there exists exactly one element that occurs an odd number of times
--    (This is a common assumption in such problems, otherwise the result would be ambiguous)
-- 4. An element occurs an odd number of times if its count in the list is odd (1, 3, 5, 7, ...)
-- 5. The function should return this unique element
-- 6. We need to count occurrences of each distinct element in the list
-- 7. Among all distinct elements, exactly one should have an odd count
--
-- Edge cases to consider:
-- - Single element list: that element occurs once (odd), so return it
-- - All elements the same: if list length is odd, return that element
-- - Multiple distinct elements: exactly one should appear odd times
-- - The precondition ensures the list is non-empty (since an empty list cannot have
--   an element with odd occurrence)



-- Helper function to count occurrences of an element in a list

specdef GetOddOccurrenceSpec

-- Helper Functions

def hasUniqueOddOccurrence (lst : List Nat) : Prop :=
  ∃! x, x ∈ lst ∧ lst.count x % 2 = 1

-- Predicate: an element is the unique odd-occurrence element
def isOddOccurrenceElement (lst : List Nat) (result: Nat) : Prop :=
  result ∈ lst ∧
  lst.count result % 2 = 1

def require1 (lst : List Nat) :=
  hasUniqueOddOccurrence lst

-- Postcondition clauses
def ensures1 (lst : List Nat) (result: Nat) :=
  isOddOccurrenceElement lst result

def_pre (lst : List Nat) :=
  require1 lst
def_post (lst : List Nat) (result: Nat) :=
  ensures1 lst result

specend GetOddOccurrenceSpec

method GetOddOccurrence (lst : List Nat)
  return (result: Nat)
  require GetOddOccurrenceSpec.pre lst
  ensures GetOddOccurrenceSpec.post lst result
  do
    sorry

prove_correct GetOddOccurrence by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0: Single element (occurs once)
def test0_Lst : List Nat := [5]
def test0_Expected : Nat := 5

-- Test case 1: Three occurrences of same element
def test1_Lst : List Nat := [3,3,3]
def test1_Expected : Nat := 3

-- Test case 2: One element appears once, others even times
def test2_Lst : List Nat := [1,2,3,2,3,1,3]
def test2_Expected : Nat := 3

-- Test case 3: Multiple elements, one appears 5 times
def test3_Lst : List Nat := [2,3,5,4,5,2,4,3,5,2,4,4,2]
def test3_Expected : Nat := 5

-- Test case 4: Element appears 7 times among many elements
def test4_Lst : List Nat := [1,1,2,2,3,3,4,4,5,5,6,6,7,7,7,7,7,7,7]
def test4_Expected : Nat := 7

-- Test case 5: Small list with element appearing 3 times
def test5_Lst : List Nat := [10,20,10,20,10]
def test5_Expected : Nat := 10

-- Test case 6: Element appearing once among many even occurrences
def test6_Lst : List Nat := [1,1,2,2,3,3,4]
def test6_Expected : Nat := 4

-- Test case 7: Large scale test - element 42 appears 101 times
def test7_Lst : List Nat := List.replicate 101 42 ++ List.replicate 100 13 ++ List.replicate 100 7
def test7_Expected : Nat := 42

-- Test case 8: Large scale test with many distinct elements
def test8_Lst : List Nat := List.replicate 50 1 ++ List.replicate 50 2 ++ List.replicate 50 3 ++ List.replicate 50 4 ++ List.replicate 51 5
def test8_Expected : Nat := 5

-- Test case 9: String type test - character appearing odd times
def test9_Lst : List String := ["apple","banana","cherry","apple","banana","cherry","apple"]
def test9_Expected : String := "apple"

-- Test case 10: Large dataset with element appearing once
def test10_Lst : List Nat := List.replicate 1000 10 ++ List.replicate 1000 20 ++ List.replicate 1000 30 ++ [999]
def test10_Expected : Nat := 999

-- Test case 11: Element appearing 9 times in long list
def test11_Lst : List Nat := List.replicate 9 100 ++ List.replicate 200 200 ++ List.replicate 200 300
def test11_Expected : Nat := 100

-- Test case 12: Negative numbers test
def test12_Lst : List Int := [-1,-2,-1,-2,-1]
def test12_Expected : Int := -1

-- Test case 13: Mixed positive and negative numbers
def test13_Lst : List Int := [1,-1,2,-2,1,-1,2,-2,3,3,3]
def test13_Expected : Int := 3

-- Test case 14: Large scale with element appearing 1001 times
def test14_Lst : List Nat := List.replicate 1001 77 ++ List.replicate 500 88 ++ List.replicate 500 99
def test14_Expected : Nat := 77

-- Test case 15: Element appearing once in a very long list of pairs
def test15_Lst : List Nat := List.replicate 5000 1 ++ List.replicate 5000 2 ++ List.replicate 5000 3 ++ [777]
def test15_Expected : Nat := 777

-- Test case 16: Element appearing 999 times in very long list
def test16_Lst : List Nat := List.replicate 999 55 ++ List.replicate 10000 66 ++ List.replicate 10000 77
def test16_Expected : Nat := 55

-- Recommend to validate: 0, 3, 7, 10, 14

end TestCases
