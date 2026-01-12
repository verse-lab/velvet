import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    FindLowercaseUnderscorePattern: Detect if a List Char contains sequences of lowercase letters joined with an underscore
    Natural language breakdown:
    1. Given an input List Char, we want to determine whether it contains at least one substring matching a specific pattern
    2. The pattern is: one or more lowercase letters, followed by exactly one underscore, followed by one or more lowercase letters
    3. A lowercase letter is a character in the range 'a' to 'z'
    4. Examples of valid patterns: "hello_world", "a_b", "test_case", "aab_cbbbc"
    5. Examples of invalid patterns: "Hello_world" (capital H), "test__case" (double underscore), "test_" (no letters after underscore), "_test" (no letters before underscore)
    6. The function returns a List Char message:
       - "Found a match!" if at least one valid pattern is found
       - "Not matched!" if no valid pattern exists
    7. This is a boolean-like decision problem expressed as a List Char result
    8. A valid pattern must be a contiguous substring where:
       - It starts with at least one lowercase letter
       - Followed by exactly one underscore character '_'
       - Followed by at least one lowercase letter
       - The pattern can appear anywhere in the input List Char, including embedded in non-lowercase context
       - For example, "123abc_def456" contains the pattern "abc_def" which is valid
    9. This problem is commonly solved using regex pattern matching, but here we specify it formally
-/

-- Helper Functions

-- Check if a character is a lowercase letter

section Specs

-- Helper Functions

def containsPattern (input : List Char) : Prop :=
  ∃ i j k,
    0 ≤ i ∧ i < j ∧ j < k ∧ k < input.length ∧
    (∀ p, i ≤ p → p < j → input[p]!.isLower) ∧
    input[j]! = '_' ∧
    (∀ p, j < p → p ≤ k → input[p]!.isLower)

-- Postcondition clauses
def ensures1 (input : List Char) (result : String) :=
  containsPattern input → result = "Found a match!"
def ensures2 (input : List Char) (result : String) :=
  ¬containsPattern input → result = "Not matched!"

def precondition (input : List Char) :=
  True  -- no preconditions
def postcondition (input : List Char) (result : String) :=
  ensures1 input result ∧
  ensures2 input result

end Specs

method FindLowercaseUnderscorePattern (input : List Char)
  return (result : String)
  require precondition input
  ensures postcondition input result
  do
    sorry

prove_correct FindLowercaseUnderscorePattern by sorry

section TestCases

-- Test case 0: Problem statement example (MUST be first)
def test0_input : List Char := ['a','a','b','_','c','b','b','b','c']
def test0_Expected : String := "Found a match!"

-- Test case 1: Simple valid pattern
def test1_input : List Char := ['h','e','l','l','o','_','w','o','r','l','d']
def test1_Expected : String := "Found a match!"

-- Test case 2: No underscore
def test2_input : List Char := ['h','e','l','l','o','w','o','r','l','d']
def test2_Expected : String := "Not matched!"

-- Test case 3: Underscore at start
def test3_input : List Char := ['_','t','e','s','t']
def test3_Expected : String := "Not matched!"

-- Test case 4: Underscore at end
def test4_input : List Char := ['t','e','s','t','_']
def test4_Expected : String := "Not matched!"

-- Test case 5: Double underscore
def test5_input : List Char := ['t','e','s','t','_','_','c','a','s','e']
def test5_Expected : String := "Not matched!"

-- Test case 6: Pattern embedded in non-lowercase context
def test6_input : List Char := ['1','2','3','a','b','c','_','d','e','f','4','5','6']
def test6_Expected : String := "Found a match!"

-- Recommend to validate: test cases 0, 1, 2, 3, 4, 5

end TestCases
