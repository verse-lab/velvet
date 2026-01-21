import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    runLengthEncoder: Compress a string using Run-Length Encoding (RLE)
    Natural language breakdown:
    1. Given a string consisting of non-digit characters, produce a compressed string
    2. Consecutive duplicate characters are replaced by the character followed by its count
    3. The output alternates between characters and their counts (e.g., "a3b2")
    4. When decoded, the output must reconstruct to the original input
    5. The result is non-empty if and only if the input is non-empty
    6. Input must not contain digit characters (would cause ambiguous encoding)
    7. Each run of identical characters produces exactly one character followed by digits
    8. Single characters get count 1 (e.g., "a" becomes "a1")
    
    Property-based specification approach:
    - The input can be uniquely decomposed into maximal runs of identical characters
    - A run is a pair (char, count) where count >= 1
    - Runs are maximal: adjacent runs have different characters
    - The result encodes each run as: character followed by decimal representation of count
    - The concatenation of expanded runs equals the original input
    - The result alternates between non-digit characters and digit sequences
-/

section Specs
register_specdef_allow_recursion

-- Helper Functions

-- Check if a character is a digit
def isDigitChar (c : Char) : Bool := c.isDigit

-- Check if input contains no digit characters (precondition)
def noDigitsInString (s : String) : Prop :=
  ∀ c, c ∈ s.toList → ¬isDigitChar c

-- A run is represented as (character, count)
-- Expand a single run into a list of characters
def expandRun (c : Char) (n : Nat) : List Char :=
  List.replicate n c

-- Expand a list of runs into a list of characters
def expandRuns (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => expandRun p.1 p.2)

-- Encode a single run as character followed by its decimal count
def encodeRun (c : Char) (n : Nat) : List Char :=
  c :: (Nat.repr n).toList

-- Encode a list of runs into RLE format
def encodeRuns (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => encodeRun p.1 p.2)

-- Check if runs are valid: each count >= 1
def validRunCounts (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i < runs.length → (runs[i]!).2 ≥ 1

-- Check if runs are maximal: adjacent runs have different characters
def maximalRuns (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i + 1 < runs.length → (runs[i]!).1 ≠ (runs[i+1]!).1

-- Check if runs contain no digit characters
def runsNoDigits (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i < runs.length → ¬isDigitChar (runs[i]!).1

-- Decode a result string back to original: expand each (char, count) pair
-- This is used to verify the round-trip property
def decodeRLE (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => List.replicate p.2 p.1)

-- Property 1: result correctly encodes input using RLE
-- There exists a valid run decomposition such that:
-- 1. The runs expand to the input
-- 2. The runs are maximal (no two adjacent runs have the same character)
-- 3. The result is the encoding of those runs
-- 4. The runs contain no digit characters (consistent with precondition)
def ensures1 (input : String) (result : String) :=
  ∃ (runs : List (Char × Nat)),
    -- Runs expand to input (decoding property)
    expandRuns runs = input.toList ∧
    -- All counts are positive
    validRunCounts runs ∧
    -- Runs are maximal (consecutive runs have different characters)
    maximalRuns runs ∧
    -- Runs contain no digit characters
    runsNoDigits runs ∧
    -- Result is the encoding of these runs
    result.toList = encodeRuns runs

-- Property 2: result is non-empty iff input is non-empty
def ensures2 (input : String) (result : String) :=
  (input.isEmpty ↔ result.isEmpty)

-- Precondition: input contains no digit characters
def precondition (input : String) :=
  noDigitsInString input

-- Combined postcondition
def postcondition (input : String) (result : String) :=
  ensures1 input result ∧ ensures2 input result

end Specs

section Impl

method runLengthEncoder (input: String)
  return (result: String)
  require precondition input
  ensures postcondition input result
  do
    pure ""

end Impl

section TestCases

-- Test case 1: Example from problem - basic RLE with multiple runs
def test1_input : String := "aaabbbcc"
def test1_Expected : String := "a3b3c2"

-- Test case 2: Special characters
def test2_input : String := "!!!$$$%%%"
def test2_Expected : String := "!3$3%3"

-- Test case 3: Single character repeated many times
def test3_input : String := "aaaaa"
def test3_Expected : String := "a5"

-- Test case 4: All distinct characters (no compression benefit)
def test4_input : String := "abcd"
def test4_Expected : String := "a1b1c1d1"

-- Test case 5: Empty string (edge case)
def test5_input : String := ""
def test5_Expected : String := ""

-- Test case 6: Mixed case characters (case sensitive)
def test6_input : String := "AaABb"
def test6_Expected : String := "A1a1A1B1b1"

-- Test case 7: Long run (17 characters)
def test7_input : String := "wwwwwwwwwwwwwwwww"
def test7_Expected : String := "w17"

-- Test case 8: Single character
def test8_input : String := "a"
def test8_Expected : String := "a1"

-- Test case 9: Spaces (whitespace handling)
def test9_input : String := "  "
def test9_Expected : String := " 2"

-- Recommend to validate: 1, 4, 5

end TestCases
