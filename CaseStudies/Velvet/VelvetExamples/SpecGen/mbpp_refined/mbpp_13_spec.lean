import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Top4FrequentWords: Return the 4 most common words from a list with their counts
    Natural language breakdown:
    1. Given a list of words (strings), count the frequency of each word
    2. Find the top 4 most frequent words
    3. Return these words as (word, count) pairs
    4. The output should be sorted by frequency in descending order (highest first)
    5. For ties (words with equal frequency), break ties by the word's first occurrence in the input list
    6. If there are fewer than 4 unique words, return all of them
    7. Empty input returns empty result
    8. The specification uses existential quantification over all word-count pairs:
       - There exists a complete list of (word, count) pairs for all unique words
       - Each word appears exactly once in this list
       - The list is sorted by count (descending), then by first occurrence (ascending)
       - The result is the first 4 elements from this sorted list
-/

-- Helper Functions

-- Count occurrences of a word in the List

section Specs

-- Helper Functions

def countWord (list : List String) (w : String) : Nat :=
  list.count w

def firstIndex (list : List String) (w : String) : Nat :=
  match list.findIdx? (· = w) with
  | some idx => idx
  | none => list.length

def isSortedByCountAndOccurrence
  (words : List String)
  (result : List (String × Nat)) : Prop :=
  ∀ i j, i < j → j < result.length →
    let wi := result[i]!.1
    let wj := result[j]!.1
    let fi := result[i]!.2
    let fj := result[j]!.2
    let idxi := firstIndex words wi
    let idxj := firstIndex words wj
    (fi > fj) ∨ (fi = fj ∧ idxi < idxj)

-- Postcondition clauses
def ensures1 (words : List String) (result : List (String × Nat)) : Prop :=
  ∃ sorted : List (String × Nat),
    (∀ p ∈ sorted, p.2 = countWord words p.1) ∧
    (∀ p ∈ words, ∃! q ∈ sorted, q.1 = p) ∧
    (∀ p ∈ sorted, p.1 ∈ words) ∧
    isSortedByCountAndOccurrence words sorted ∧
    result = sorted.take 4

def precondition (words : List String) :=
  True  -- no preconditions
def postcondition (words : List String) (result : List (String × Nat)) :=
  ensures1 words result

end Specs

method Top4FrequentWords (words: List String)
  return (result: List (String × Nat))
  require precondition words
  ensures postcondition words result
  do
    sorry

prove_correct Top4FrequentWords by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_words : List String :=
  ["red","green","black","pink","black","white","black","eyes","white","black",
   "orange","pink","pink","red","red","white","orange","white","black","pink",
   "green","green","pink","green","pink","white","orange","orange","red"]
def test1_Expected : List (String × Nat) :=
  [("pink", 6), ("black", 5), ("white", 5), ("red", 4)]

-- Test case 2: Empty list
def test2_words : List String := []
def test2_Expected : List (String × Nat) := []

-- Test case 3: Single word
def test3_words : List String := ["hello"]
def test3_Expected : List (String × Nat) := [("hello", 1)]

-- Test case 4: Fewer than 4 unique words
def test4_words : List String := ["red", "green", "red", "blue"]
def test4_Expected : List (String × Nat) := [("red", 2), ("green", 1), ("blue", 1)]

-- Test case 5: Exactly 4 unique words with different frequencies
def test5_words : List String := ["cat", "dog", "cat", "bird", "cat", "dog", "fish"]
def test5_Expected : List (String × Nat) := [("cat", 3), ("dog", 2), ("bird", 1), ("fish", 1)]

-- Test case 6: More than 4 unique words
def test6_words : List String := ["apple", "banana", "apple", "cherry", "banana", "apple", "date", "elderberry", "fig"]
def test6_Expected : List (String × Nat) := [("apple", 3), ("banana", 2), ("cherry", 1), ("date", 1)]

-- Test case 7: All words with same frequency - ordered by first occurrence
def test7_words : List String := ["alpha", "beta", "gamma", "delta", "epsilon"]
def test7_Expected : List (String × Nat) := [("alpha", 1), ("beta", 1), ("gamma", 1), ("delta", 1)]

-- Test case 8: Tie-breaking by first occurrence
def test8_words : List String := ["dog", "bird", "cat", "dog", "cat", "fish"]
def test8_Expected : List (String × Nat) := [("dog", 2), ("cat", 2), ("bird", 1), ("fish", 1)]

-- Test case 9: All words with same frequency - first occurrence order
def test9_words : List String := ["zebra", "apple", "banana", "cherry", "date"]
def test9_Expected : List (String × Nat) := [("zebra", 1), ("apple", 1), ("banana", 1), ("cherry", 1)]

-- Test case 10: Case sensitivity test
def test10_words : List String := ["Cat", "cat", "CAT", "Cat", "dog"]
def test10_Expected : List (String × Nat) := [("Cat", 2), ("cat", 1), ("CAT", 1), ("dog", 1)]

-- Test case 11: Multiple ties at different frequency levels
def test11_words : List String := ["a", "b", "a", "c", "a", "d", "b", "c", "e"]
def test11_Expected : List (String × Nat) := [("a", 3), ("b", 2), ("c", 2), ("d", 1)]

-- Test case 12: Single word repeated multiple times
def test12_words : List String := ["hello", "hello", "hello", "hello"]
def test12_Expected : List (String × Nat) := [("hello", 4)]

-- Test case 13: Complex tie scenario with mixed frequencies
def test13_words : List String := ["x", "y", "x", "x", "z", "x", "w", "y", "z"]
def test13_Expected : List (String × Nat) := [("x", 4), ("y", 2), ("z", 2), ("w", 1)]

-- Test case 14: Large example with many ties
def test14_words : List String :=
  ["first", "second", "third", "fourth", "fifth",
   "first", "second", "third", "fourth",
   "first", "second", "third",
   "first", "second",
   "first"]
def test14_Expected : List (String × Nat) := [("first", 5), ("second", 4), ("third", 3), ("fourth", 2)]

-- Test case 15: All different words (more than 4)
def test15_words : List String := ["one", "two", "three", "four", "five", "six", "seven"]
def test15_Expected : List (String × Nat) := [("one", 1), ("two", 1), ("three", 1), ("four", 1)]

-- Recommend to validate: test cases 1, 2, 3, 7, 8, 11
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Empty list edge case
-- - Test 3: Single word edge case
-- - Test 7: All equal frequency tie-breaking
-- - Test 8: Tie-breaking with count 2
-- - Test 11: Multiple ties at different levels

end TestCases
