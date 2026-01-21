import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    reverseWords: Reverse the order of words in a string
    Natural language breakdown:
    1. A word is defined as a contiguous sequence of non-space characters
    2. The input string may contain leading, trailing, or multiple spaces between words
    3. The output should contain the words in reversed order
    4. Words in the output are separated by exactly one space
    5. The output has no leading or trailing spaces
    6. The characters within each word remain unchanged (not reversed)
    7. If the input contains only spaces, the output is an empty string
    8. If the input is empty, the output is an empty string
    9. Examples:
       - "the sky is blue" -> "blue is sky the"
       - "  hello world  " -> "world hello"
       - "a good   example" -> "example good a"
-/

section Specs

-- Helper Functions

-- Extract words from a string (splitting by spaces, filtering empty strings)
def extractWords (s : String) : List String :=
  (s.split (· = ' ')).filter (· ≠ "")

-- Check if a string has no leading spaces
def noLeadingSpaces (s : String) : Bool :=
  s.data.head? ≠ some ' '

-- Check if a string has no trailing spaces
def noTrailingSpaces (s : String) : Bool :=
  s.data.getLast? ≠ some ' '

-- Check if there are no consecutive spaces in a string
def noConsecutiveSpaces (s : String) : Bool :=
  let chars := s.data
  chars.length < 2 ∨ (List.zip chars chars.tail).all (fun (a, b) => ¬(a = ' ' ∧ b = ' '))

-- Check if the result is properly formatted (no leading/trailing/consecutive spaces)
def isProperlyFormatted (s : String) : Bool :=
  s = "" ∨ (noLeadingSpaces s ∧ noTrailingSpaces s ∧ noConsecutiveSpaces s)

-- Postcondition clauses

-- The words in result are the reverse of words in input
def ensures1 (words_str : String) (result : String) : Prop :=
  extractWords result = (extractWords words_str).reverse

-- The result is properly formatted (no extra spaces)
def ensures2 (words_str : String) (result : String) : Prop :=
  isProperlyFormatted result

def precondition (words_str : String) : Prop :=
  True  -- no preconditions

def postcondition (words_str : String) (result : String) : Prop :=
  ensures1 words_str result ∧
  ensures2 words_str result

end Specs

section Impl

method reverseWords (words_str: String)
  return (result: String)
  require precondition words_str
  ensures postcondition words_str result
  do
  pure ""  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic case with single spaces (from problem examples)
def test1_words_str : String := "the sky is blue"
def test1_Expected : String := "blue is sky the"

-- Test case 2: Leading and trailing spaces
def test2_words_str : String := "  hello world  "
def test2_Expected : String := "world hello"

-- Test case 3: Multiple spaces between words
def test3_words_str : String := "a good   example"
def test3_Expected : String := "example good a"

-- Test case 4: Mixed spacing patterns
def test4_words_str : String := "  Bob    Loves  Alice   "
def test4_Expected : String := "Alice Loves Bob"

-- Test case 5: Normal sentence
def test5_words_str : String := "this lab is interesting"
def test5_Expected : String := "interesting is lab this"

-- Test case 6: Empty string
def test6_words_str : String := ""
def test6_Expected : String := ""

-- Test case 7: Only spaces
def test7_words_str : String := "     "
def test7_Expected : String := ""

-- Test case 8: Single word
def test8_words_str : String := "hello"
def test8_Expected : String := "hello"

-- Test case 9: Single word with surrounding spaces
def test9_words_str : String := "   word   "
def test9_Expected : String := "word"

-- Test case 10: Two words
def test10_words_str : String := "first second"
def test10_Expected : String := "second first"

-- Recommend to validate: 1, 2, 3

end TestCases
