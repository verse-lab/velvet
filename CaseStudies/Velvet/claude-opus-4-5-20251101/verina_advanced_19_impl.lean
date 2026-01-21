import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isCleanPalindrome: Check if a string is a palindrome ignoring non-alphabetic characters and case
    Natural language breakdown:
    1. A palindrome is a string that reads the same forwards and backwards
    2. The function should ignore all non-alphabetic characters (whitespace, punctuation, etc.)
    3. The function should treat uppercase and lowercase letters as equivalent
    4. First, filter the string to keep only alphabetic characters
    5. Convert all remaining characters to lowercase for comparison
    6. Check if the cleaned string equals its reverse
    7. Return true if it's a palindrome, false otherwise
    8. Empty strings and single characters are trivially palindromes
    9. Examples:
       - "A man, a plan, a canal, Panama" -> clean to "amanaplanacanalpanama" -> palindrome (true)
       - "No lemon, no melon" -> clean to "nolonemonelon" -> palindrome (true)
       - "OpenAI" -> clean to "openai" -> not a palindrome (false)
-/

section Specs
-- Helper Functions

-- Filter to keep only alphabetic characters and convert to lowercase
def cleanString (s : String) : List Char :=
  (s.toList.filter Char.isAlpha).map Char.toLower

-- Check if a list is a palindrome (equals its reverse)
def isPalindrome (chars : List Char) : Prop :=
  chars = chars.reverse

-- Postcondition clauses
-- The result is true if and only if the cleaned string is a palindrome
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ cleanString s = (cleanString s).reverse

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result
end Specs

section Impl
method isCleanPalindrome (s: String)
  return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  -- Clean the string: filter alphabetic chars and convert to lowercase
  let cleaned := (s.toList.filter Char.isAlpha).map Char.toLower
  let arr := cleaned.toArray
  
  -- Check if palindrome using two pointers
  let mut left := 0
  let mut right := arr.size
  let mut isPalin := true
  
  while left < right ∧ isPalin
    -- Invariant 1: left is bounded
    invariant "left_lower" 0 ≤ left
    invariant "left_upper" left ≤ arr.size
    -- Invariant 2: right is bounded
    invariant "right_upper" right ≤ arr.size
    -- Invariant 3: left and right relationship (they sum to arr.size when isPalin is true)
    invariant "sum_relation" isPalin = true → left + right = arr.size
    -- Invariant 4: left doesn't exceed right when isPalin is true
    invariant "left_le_right" isPalin = true → left ≤ right
    -- Invariant 5: If isPalin is true, all pairs checked so far match
    invariant "prefix_match" isPalin = true → (∀ i, i < left → arr[i]! = arr[arr.size - 1 - i]!)
    -- Invariant 6: If isPalin is false, there's a mismatch (the string is not a palindrome)
    invariant "mismatch_found" isPalin = false → arr.toList ≠ arr.toList.reverse
    -- Invariant 7: Relate arr to cleaned
    invariant "arr_is_cleaned" arr.toList = cleaned
    done_with (left >= right ∨ isPalin = false)
  do
    if right > 0 then
      let r := right - 1
      if arr[left]! != arr[r]! then
        isPalin := false
      else
        left := left + 1
        right := r
    else
      left := left + 1
  
  return isPalin
end Impl

section TestCases
-- Test case 1: Classic palindrome with spaces and punctuation (example from problem)
def test1_s : String := "A man, a plan, a canal, Panama"
def test1_Expected : Bool := true

-- Test case 2: Another classic palindrome phrase
def test2_s : String := "No lemon, no melon"
def test2_Expected : Bool := true

-- Test case 3: Non-palindrome word
def test3_s : String := "OpenAI"
def test3_Expected : Bool := false

-- Test case 4: Question form palindrome
def test4_s : String := "Was it a car or a cat I saw?"
def test4_Expected : Bool := true

-- Test case 5: Non-palindrome greeting
def test5_s : String := "Hello, World!"
def test5_Expected : Bool := false

-- Test case 6: Empty string (edge case - trivially a palindrome)
def test6_s : String := ""
def test6_Expected : Bool := true

-- Test case 7: Single character (edge case - trivially a palindrome)
def test7_s : String := "A"
def test7_Expected : Bool := true

-- Test case 8: Only non-alphabetic characters (edge case - empty after cleaning)
def test8_s : String := "12345!@#$%"
def test8_Expected : Bool := true

-- Test case 9: Simple palindrome word
def test9_s : String := "Racecar"
def test9_Expected : Bool := true

-- Test case 10: Two same characters
def test10_s : String := "aa"
def test10_Expected : Bool := true

-- Recommend to validate: 1, 3, 6
end TestCases


section Assertions
-- Test case 1

#assert_same_evaluation #[((isCleanPalindrome test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isCleanPalindrome test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isCleanPalindrome test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isCleanPalindrome test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isCleanPalindrome test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isCleanPalindrome test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isCleanPalindrome test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isCleanPalindrome test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isCleanPalindrome test9_s).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isCleanPalindrome test10_s).run), DivM.res test10_Expected ]
end Assertions

section Pbt
extract_program_for isCleanPalindrome
prove_precondition_decidable_for isCleanPalindrome
prove_postcondition_decidable_for isCleanPalindrome
derive_tester_for isCleanPalindrome
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := isCleanPalindromeTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isCleanPalindrome by
  -- loom_solve <;> (try simp at *; expose_names)


prove_correct isCleanPalindrome by
  loom_solve <;> (try simp at *; expose_names)
end Proof
