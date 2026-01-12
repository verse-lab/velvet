import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Init.Data.Char.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    SplitAtLowercase: Split a string into segments, where each segment starts at a lowercase letter
    Natural language breakdown:
    1. Given a string, we need to identify all positions where lowercase letters occur
    2. Each lowercase letter marks the start of a new segment
    3. A segment includes the lowercase letter and all following characters until (but not including) the next lowercase letter
    4. From the example "AbCd" → ['bC','d']:
       - 'A' is uppercase, not a segment start
       - 'b' is lowercase at position 1, starts segment "bC" (includes 'b' and 'C')
       - 'C' is uppercase, continues current segment
       - 'd' is lowercase at position 3, starts new segment "d" (includes only 'd')
    5. Edge cases:
       - Empty string returns empty list
       - String with no lowercase letters returns empty list
       - String starting with lowercase creates first segment immediately
       - Consecutive lowercase letters create multiple single-character segments
       - String ending with lowercase creates a single-character final segment
    6. The order of segments in the result matches the order of lowercase letters in the input
    7. Each character in the output appears exactly once (no overlap or gaps between segments that start with lowercase)
-/

-- Helper Functions

-- Check if a character is a lowercase ASCII letter

section Specs

-- Helper Functions

def isSegment (seg : List Char) : Prop :=
  ∃ c rest,
    seg = c :: rest ∧
    c.isLower ∧
    ∀ x ∈ rest, ¬ x.isLower

-- Postcondition clauses
def ensures1 (str : List Char) (result : List (List Char)) :=
  ∀ lst ∈ result, isSegment lst
def ensures2 (str : List Char) (result : List (List Char)) :=
  ∃ pre : List Char,
    (∀ x ∈ pre, ¬ x.isLower) ∧
    str = result.foldl (fun acc x => acc ++ x) pre

def precondition (str : List Char) :=
  True  -- no preconditions
def postcondition (str : List Char) (result : List (List Char)) :=
  ensures1 str result ∧ ensures2 str result

end Specs

method SplitAtLowercase (str: List Char)
  return (result: List (List Char))
  require precondition str
  ensures postcondition str result
  do
    sorry

prove_correct SplitAtLowercase by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_str : List Char := ['A', 'b', 'C', 'd']
def test1_Expected : List (List Char) := [['b', 'C'], ['d']]

-- Test case 2: Empty string
def test2_str : List Char := []
def test2_Expected : List (List Char) := []

-- Test case 3: All uppercase (no lowercase)
def test3_str : List Char := ['A', 'B', 'C', 'D']
def test3_Expected : List (List Char) := []

-- Test case 4: All lowercase
def test4_str : List Char := ['a', 'b', 'c', 'd']
def test4_Expected : List (List Char) := [['a'], ['b'], ['c'], ['d']]

-- Test case 5: Starting with lowercase
def test5_str : List Char := ['a', 'B', 'C', 'd', 'E']
def test5_Expected : List (List Char) := [['a', 'B', 'C'], ['d', 'E']]

-- Test case 6: Single lowercase letter
def test6_str : List Char := ['a']
def test6_Expected : List (List Char) := [['a']]

-- Test case 7: Single uppercase letter
def test7_str : List Char := ['A']
def test7_Expected : List (List Char) := []

-- Test case 8: Lowercase at end
def test8_str : List Char := ['A', 'B', 'C', 'd']
def test8_Expected : List (List Char) := [['d']]

-- Test case 9: Mixed pattern
def test9_str : List Char := ['X', 'y', 'Z', 'a', 'B', 'c', 'D', 'E']
def test9_Expected : List (List Char) := [['y', 'Z'], ['a', 'B'], ['c', 'D', 'E']]

-- Test case 10: Consecutive lowercase
def test10_str : List Char := ['A', 'b', 'c', 'd', 'E']
def test10_Expected : List (List Char) := [['b'], ['c'], ['d', 'E']]

-- Test case 11: Long segment
def test11_str : List Char := ['a', 'B', 'C', 'D', 'E', 'F', 'G']
def test11_Expected : List (List Char) := [['a', 'B', 'C', 'D', 'E', 'F', 'G']]

-- Test case 12: Alternating case
def test12_str : List Char := ['A', 'b', 'C', 'd', 'E', 'f']
def test12_Expected : List (List Char) := [['b', 'C'], ['d', 'E'], ['f']]

-- Test case 13: Only lowercase at beginning and end
def test13_str : List Char := ['a', 'B', 'C', 'D', 'e']
def test13_Expected : List (List Char) := [['a', 'B', 'C', 'D'], ['e']]

-- Test case 14: Multiple consecutive uppercase between lowercase
def test14_str : List Char := ['x', 'X', 'X', 'X', 'y', 'Y', 'Y', 'z']
def test14_Expected : List (List Char) := [['x', 'X', 'X', 'X'], ['y', 'Y', 'Y'], ['z']]

-- Test case 15: Long string with varied pattern
def test15_str : List Char := ['T', 'h', 'E', 'q', 'U', 'I', 'c', 'K', 'b', 'R', 'o', 'W', 'n']
def test15_Expected : List (List Char) := [['h', 'E'], ['q', 'U', 'I'], ['c', 'K'], ['b', 'R'], ['o', 'W'], ['n']]

-- Recommend to validate: test cases 1, 2, 4, 5, 9, 10
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Empty string edge case
-- - Test 4: All lowercase (consecutive splits)
-- - Test 5: Starting with lowercase
-- - Test 9: Complex mixed pattern
-- - Test 10: Consecutive lowercase in middle

end TestCases
