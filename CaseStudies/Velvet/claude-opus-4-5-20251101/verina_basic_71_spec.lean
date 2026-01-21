import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LongestCommonPrefix: Find the longest common prefix shared by two lists of characters
    Natural language breakdown:
    1. Given two lists of characters str1 and str2
    2. Find the maximal contiguous sequence of characters from the beginning of both lists that are identical
    3. The result must be a prefix of both str1 and str2
    4. The result length is at most the minimum of the two input lengths
    5. The result is the longest such common prefix (maximality condition)
    6. If the first characters differ or either list is empty, return empty list
    7. Use List.IsPrefix (<+:) from Mathlib for prefix relationship
-/

section Specs

-- Postcondition clauses

-- The result is a prefix of str1
def ensures1 (str1 : List Char) (str2 : List Char) (result : List Char) :=
  result <+: str1

-- The result is a prefix of str2
def ensures2 (str1 : List Char) (str2 : List Char) (result : List Char) :=
  result <+: str2

-- Maximality: any longer common prefix does not exist
-- i.e., for any list that is a common prefix of both, its length is at most result.length
def ensures3 (str1 : List Char) (str2 : List Char) (result : List Char) :=
  ∀ p : List Char, p <+: str1 → p <+: str2 → p.length ≤ result.length

def precondition (str1 : List Char) (str2 : List Char) :=
  True  -- no preconditions needed

def postcondition (str1 : List Char) (str2 : List Char) (result : List Char) :=
  ensures1 str1 str2 result ∧
  ensures2 str1 str2 result ∧
  ensures3 str1 str2 result

end Specs

section Impl

method LongestCommonPrefix (str1 : List Char) (str2 : List Char)
  return (result : List Char)
  require precondition str1 str2
  ensures postcondition str1 str2 result
  do
    pure []  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic case with partial match (from problem description)
def test1_str1 : List Char := ['a', 'b', 'c']
def test1_str2 : List Char := ['a', 'b', 'd']
def test1_Expected : List Char := ['a', 'b']

-- Test case 2: Identical lists - entire list is the common prefix
def test2_str1 : List Char := ['x', 'y', 'z']
def test2_str2 : List Char := ['x', 'y', 'z']
def test2_Expected : List Char := ['x', 'y', 'z']

-- Test case 3: One list is prefix of the other
def test3_str1 : List Char := ['w', 'o']
def test3_str2 : List Char := ['w', 'o', 'w']
def test3_Expected : List Char := ['w', 'o']

-- Test case 4: No common prefix - first characters differ
def test4_str1 : List Char := ['a', 'x']
def test4_str2 : List Char := ['b', 'y']
def test4_Expected : List Char := []

-- Test case 5: First list is empty
def test5_str1 : List Char := []
def test5_str2 : List Char := ['h', 'e', 'l', 'l', 'o']
def test5_Expected : List Char := []

-- Test case 6: Second list is empty
def test6_str1 : List Char := ['a', 'b', 'c']
def test6_str2 : List Char := []
def test6_Expected : List Char := []

-- Test case 7: Both lists empty
def test7_str1 : List Char := []
def test7_str2 : List Char := []
def test7_Expected : List Char := []

-- Test case 8: Single character match
def test8_str1 : List Char := ['a', 'b', 'c']
def test8_str2 : List Char := ['a', 'x', 'y']
def test8_Expected : List Char := ['a']

-- Test case 9: Single character lists that match
def test9_str1 : List Char := ['z']
def test9_str2 : List Char := ['z']
def test9_Expected : List Char := ['z']

-- Test case 10: Single character lists that differ
def test10_str1 : List Char := ['a']
def test10_str2 : List Char := ['b']
def test10_Expected : List Char := []

-- Recommend to validate: 1, 2, 5

end TestCases
