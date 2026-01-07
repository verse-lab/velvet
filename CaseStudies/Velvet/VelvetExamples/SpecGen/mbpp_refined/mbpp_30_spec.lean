import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Mathlib.SetTheory.Cardinal.Finite

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 30: Count all substrings starting and ending with same characters
--
-- Natural language breakdown:
-- 1. Given a List Char s, we want to count all possible substrings (contiguous sequences)
--    that start and end with the same character
-- 2. A substring is defined by a starting position i and ending position j (inclusive)
--    where 0 ≤ i ≤ j < s.length
-- 3. For a substring s[i..j] to qualify, we need s[i] = s[j]
-- 4. All single-character substrings automatically qualify (s[i] = s[i])
-- 5. For multi-character substrings, we need the first and last characters to match
--
-- Mathematical approach:
-- - For each character c, count how many times it appears in the List Char
-- - If character c appears k times, it contributes k*(k+1)/2 valid substrings:
--   * k single-character substrings (one for each occurrence)
--   * k*(k-1)/2 multi-character substrings (one for each pair of occurrences)
-- - Sum contributions from all distinct characters
--
-- Examples:
-- - "abc": 'a' appears 1 time → 1 substring, 'b' → 1, 'c' → 1, total = 3
-- - "abcab": 'a' appears 2 times → 3 substrings, 'b' → 3, 'c' → 1, total = 7
-- - "aa": 'a' appears 2 times → 3 substrings ("a" at pos 0, "a" at pos 1, "aa")
--
-- Key properties:
-- - Result is always at least s.length (all single characters)
-- - Result is at most s.length * (s.length + 1) / 2 (all substrings, when all chars are same)
-- - For empty List Char, result is 0

-- Helper definition: Count occurrences of a character in a list

specdef CountMatchingSubstringsSpec

-- Helper Functions

-- For each distinct character, count occurrences k, contribute k*(k+1)/2

-- Postcondition clauses
def ensures1 (s : List Char) (count : Nat) :=
  count = Nat.card
    { p : Nat × Nat |
        let i := p.1
        let j := p.2
        i ≤ j ∧
        j < s.length ∧
        s[i]! = s[j]! }

def_pre (s : List Char) :=
  True  -- no preconditions
def_post (s : List Char) (count : Nat) :=
  ensures1 s count

specend CountMatchingSubstringsSpec

method CountMatchingSubstrings (s: List Char)
  return (count: Nat)
  require CountMatchingSubstringsSpec.pre s
  ensures CountMatchingSubstringsSpec.post s count
  do
    sorry

prove_correct CountMatchingSubstrings by sorry

-- Test cases for specification validation
section TestCases
-- Test dataset for counting substrings starting and ending with same character

-- Sample from problem description
def test0_s : List Char := ['a', 'b', 'c']
def test0_Expected : Nat := 3

def test1_s : List Char := []
def test1_Expected : Nat := 0

def test2_s : List Char := ['a']
def test2_Expected : Nat := 1

def test3_s : List Char := ['a', 'a']
def test3_Expected : Nat := 3

def test4_s : List Char := ['a', 'a', 'a', 'a']
def test4_Expected : Nat := 10

def test5_s : List Char := ['a', 'b', 'a', 'b']
def test5_Expected : Nat := 6

def test6_s : List Char := ['a', 'b', 'c', 'a', 'b', 'c']
def test6_Expected : Nat := 9

def test7_s : List Char := ['a', 'a', 'b', 'a', 'a']
def test7_Expected : Nat := 11

def test8_s : List Char := ['a', 'b', 'a', 'c', 'a', 'd']
def test8_Expected : Nat := 9

def test9_s : List Char := ['a', 'a', 'b', 'b', 'c', 'c', 'a', 'a']
def test9_Expected : Nat := 16

def test10_s : List Char := ['a', 'a', 'b', 'c', 'a', 'a']
def test10_Expected : Nat := 12

-- Recommend to validate: 0,1,2,3,4

end TestCases
