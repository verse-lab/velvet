import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    mostFrequent: Return the integer that appears most frequently in the input list.
    If multiple integers have the same maximum frequency, return the one that appears first.
    
    Natural language breakdown:
    1. Input: A non-empty list of integers (possibly with duplicates)
    2. We need to count the frequency of each integer in the list
    3. Find the maximum frequency among all integers
    4. Return the integer that has this maximum frequency
    5. If there are ties (multiple integers with the same max frequency),
       return the one that appears first in the original list
    6. "Appears first" means the element whose first occurrence has the smallest index
-/

section Specs

-- Helper Functions

-- Count occurrences of an element in a list
def countFreq (x : Int) (xs : List Int) : Nat :=
  xs.count x

-- Check if an element has the maximum frequency in the list
def hasMaxFrequency (x : Int) (xs : List Int) : Prop :=
  ∀ y ∈ xs, countFreq y xs ≤ countFreq x xs

-- Find the index of the first occurrence of an element
def firstOccurrenceIdx (x : Int) (xs : List Int) : Nat :=
  match xs.findIdx? (· == x) with
  | some idx => idx
  | none => xs.length

-- Check if x appears before y in the list (by first occurrence)
def appearsBeforeOrEqual (x : Int) (y : Int) (xs : List Int) : Prop :=
  firstOccurrenceIdx x xs ≤ firstOccurrenceIdx y xs

-- Precondition: list must be non-empty
def precondition (xs : List Int) :=
  xs ≠ []

-- Postcondition clauses
-- 1. Result must be an element of the list
def ensures1 (xs : List Int) (result : Int) :=
  result ∈ xs

-- 2. Result has the maximum frequency
def ensures2 (xs : List Int) (result : Int) :=
  hasMaxFrequency result xs

-- 3. Among all elements with max frequency, result appears first
def ensures3 (xs : List Int) (result : Int) :=
  ∀ y ∈ xs, countFreq y xs = countFreq result xs → appearsBeforeOrEqual result y xs

def postcondition (xs : List Int) (result : Int) :=
  ensures1 xs result ∧ ensures2 xs result ∧ ensures3 xs result

end Specs

section Impl

method mostFrequent (xs : List Int)
  return (result : Int)
  require precondition xs
  ensures postcondition xs result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Basic case with one clear winner (from problem)
def test1_xs : List Int := [1, 2, 2, 3]
def test1_Expected : Int := 2

-- Test case 2: Multiple occurrences of winner
def test2_xs : List Int := [4, 4, 5, 5, 4]
def test2_Expected : Int := 4

-- Test case 3: Single element list (edge case)
def test3_xs : List Int := [9]
def test3_Expected : Int := 9

-- Test case 4: Multiple elements with same frequency, 2 appears most
def test4_xs : List Int := [1, 2, 3, 1, 2, 3, 2]
def test4_Expected : Int := 2

-- Test case 5: Three-way tie initially, 7 wins by extra occurrence
def test5_xs : List Int := [7, 7, 8, 8, 9, 9, 7]
def test5_Expected : Int := 7

-- Test case 6: All elements same
def test6_xs : List Int := [5, 5, 5, 5]
def test6_Expected : Int := 5

-- Test case 7: Tie-breaker case - first appearing wins
def test7_xs : List Int := [1, 2, 1, 2]
def test7_Expected : Int := 1

-- Test case 8: Negative integers
def test8_xs : List Int := [-1, -2, -1, -3, -1]
def test8_Expected : Int := -1

-- Test case 9: Mixed positive and negative with tie
def test9_xs : List Int := [3, -3, 3, -3, 5]
def test9_Expected : Int := 3

-- Test case 10: Long sequence with clear winner at end
def test10_xs : List Int := [1, 2, 3, 4, 5, 5, 5, 5]
def test10_Expected : Int := 5

-- Recommend to validate: 1, 3, 7

end TestCases
