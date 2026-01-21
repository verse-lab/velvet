import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    letterCombinations: Generate all possible letter combinations from a string of digits based on telephone keypad mappings
    Natural language breakdown:
    1. Given a string of digits, we need to generate all possible letter combinations
    2. Each digit from 2-9 maps to a set of letters on a telephone keypad:
       - 2: a, b, c
       - 3: d, e, f
       - 4: g, h, i
       - 5: j, k, l
       - 6: m, n, o
       - 7: p, q, r, s
       - 8: t, u, v
       - 9: w, x, y, z
    3. Digits 0, 1, and any non-digit characters have no letter mappings
    4. If the input is empty, return an empty list
    5. If any digit in the input is invalid (not 2-9), return an empty list
    6. The result contains all possible combinations formed by taking one letter from each digit's mapping
    7. The order of combinations follows lexicographic order based on digit position
    8. Each resulting string has length equal to the number of input digits
    9. The total number of combinations is the product of the sizes of each digit's letter set
-/

section Specs

-- Helper Functions

-- Mapping from digit character to list of corresponding letters
def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

-- Check if a digit is valid (maps to letters)
def isValidDigit (c : Char) : Bool :=
  (digitToLetters c).length > 0

-- Check if all digits in the string are valid
def allValidDigits (s : String) : Bool :=
  s.data.all isValidDigit

-- Precondition: no restrictions on input
def precondition (digits : String) :=
  True

-- Postcondition: property-based specification without recursive reference implementation
def postcondition (digits : String) (result : List String) :=
  -- If input is empty, result is empty
  (digits.isEmpty → result = []) ∧
  -- If any digit is invalid, result is empty
  (¬digits.isEmpty → ¬allValidDigits digits → result = []) ∧
  -- If input is non-empty and all digits are valid:
  (¬digits.isEmpty → allValidDigits digits →
    -- Result length equals product of letter counts
    result.length = (digits.data.map (fun c => (digitToLetters c).length)).foldl (· * ·) 1 ∧
    -- Each result string has correct length
    (∀ i : Nat, i < result.length → (result[i]!).length = digits.length) ∧
    -- Each result string is a valid combination (each char comes from correct digit mapping)
    (∀ i : Nat, i < result.length →
      ∀ j : Nat, j < digits.length →
        (result[i]!).data[j]! ∈ digitToLetters (digits.data[j]!)) ∧
    -- No duplicates
    result.Nodup ∧
    -- All valid combinations are covered (every valid combination appears in result)
    (∀ combo : List Char, combo.length = digits.length →
      (∀ j : Nat, j < digits.length → combo[j]! ∈ digitToLetters (digits.data[j]!)) →
      combo.asString ∈ result))

end Specs

section Impl

method letterCombinations (digits : String)
  return (result : List String)
  require precondition digits
  ensures postcondition digits result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Empty string returns empty list
def test1_digits : String := ""
def test1_Expected : List String := []

-- Test case 2: Single digit '2' returns three letters
def test2_digits : String := "2"
def test2_Expected : List String := ["a", "b", "c"]

-- Test case 3: Single digit '9' returns four letters
def test3_digits : String := "9"
def test3_Expected : List String := ["w", "x", "y", "z"]

-- Test case 4: Two digits "23" returns 9 combinations
def test4_digits : String := "23"
def test4_Expected : List String := ["ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf"]

-- Test case 5: Two digits "27" returns 12 combinations (3 * 4)
def test5_digits : String := "27"
def test5_Expected : List String := ["ap", "aq", "ar", "as", "bp", "bq", "br", "bs", "cp", "cq", "cr", "cs"]

-- Test case 6: Invalid digit '0' returns empty list
def test6_digits : String := "0"
def test6_Expected : List String := []

-- Test case 7: Contains invalid digit '1' returns empty list
def test7_digits : String := "21"
def test7_Expected : List String := []

-- Test case 8: Single digit '7' returns four letters (p, q, r, s)
def test8_digits : String := "7"
def test8_Expected : List String := ["p", "q", "r", "s"]

-- Test case 9: Three digits "234" returns 27 combinations (3 * 3 * 3)
def test9_digits : String := "234"
def test9_Expected : List String := ["adg", "adh", "adi", "aeg", "aeh", "aei", "afg", "afh", "afi", "bdg", "bdh", "bdi", "beg", "beh", "bei", "bfg", "bfh", "bfi", "cdg", "cdh", "cdi", "ceg", "ceh", "cei", "cfg", "cfh", "cfi"]

-- Test case 10: Invalid character '*' returns empty list
def test10_digits : String := "2*3"
def test10_Expected : List String := []

-- Recommend to validate: 1, 2, 4

end TestCases
