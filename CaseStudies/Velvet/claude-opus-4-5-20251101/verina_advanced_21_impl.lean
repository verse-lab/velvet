import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPalindrome: Check if a given string is a palindrome
    Natural language breakdown:
    1. A palindrome is a string that reads the same forward and backward
    2. The input is a string s
    3. The output is a boolean indicating whether s is a palindrome
    4. To check if a string is a palindrome, we compare the list of characters with its reverse
    5. An empty string is considered a palindrome (trivially true)
    6. A single character string is always a palindrome
    7. Examples:
       - "racecar" reversed is "racecar" -> true
       - "abba" reversed is "abba" -> true
       - "abc" reversed is "cba" -> false
       - "" reversed is "" -> true
       - "a" reversed is "a" -> true
-/

section Specs
-- Helper Functions
-- Using Mathlib's List.reverse and String.toList

-- A string is a palindrome if its character list equals its reverse
def isPalindromeProperty (s : String) : Prop :=
  s.toList = s.toList.reverse

-- Postcondition: result is true iff the string is a palindrome
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ isPalindromeProperty s

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result
end Specs

section Impl
method isPalindrome (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  let chars := s.toList.toArray
  let n := chars.size
  if n = 0 then
    return true
  else
    let mut left := 0
    let mut right := n - 1
    let mut isPalin := true
    while left < right ∧ isPalin
      -- Invariant 1: left is bounded
      -- Init: left = 0, so 0 ≤ left ≤ n holds
      -- Pres: left increases by 1 but stays ≤ right + 1 ≤ n
      invariant "left_bounds" 0 ≤ left ∧ left ≤ n
      -- Invariant 2: right is bounded
      -- Init: right = n - 1 < n holds
      -- Pres: right decreases but stays ≥ 0 (since left < right when decremented)
      invariant "right_bounds" right < n
      -- Invariant 3: chars array is derived from s
      invariant "chars_def" chars = s.toList.toArray
      -- Invariant 4: n is the size of chars
      invariant "n_def" n = chars.size
      -- Invariant 5: The pointers move symmetrically from ends toward center
      -- Init: left = 0, right = n - 1, so left + right = n - 1
      -- Pres: left + 1 + (right - 1) = left + right = n - 1
      invariant "symmetric" left + right = n - 1
      -- Invariant 6: If isPalin is true, all checked pairs match
      -- This captures that characters at positions < left and > right have matched their mirrors
      invariant "palin_property" isPalin = true → (∀ i, 0 ≤ i ∧ i < left → chars[i]! = chars[n - 1 - i]!)
      -- Invariant 7: If isPalin is false, there exists a mismatch
      invariant "mismatch_property" isPalin = false → (∃ i, 0 ≤ i ∧ i < n / 2 ∧ chars[i]! ≠ chars[n - 1 - i]!)
      done_with (left >= right ∨ isPalin = false)
    do
      if chars[left]! ≠ chars[right]! then
        isPalin := false
      else
        left := left + 1
        right := right - 1
    return isPalin
end Impl

section TestCases
-- Test case 1: "racecar" is a palindrome (odd length, classic example)
def test1_s : String := "racecar"
def test1_Expected : Bool := true

-- Test case 2: "abba" is a palindrome (even length)
def test2_s : String := "abba"
def test2_Expected : Bool := true

-- Test case 3: "abc" is not a palindrome
def test3_s : String := "abc"
def test3_Expected : Bool := false

-- Test case 4: empty string is a palindrome
def test4_s : String := ""
def test4_Expected : Bool := true

-- Test case 5: single character is a palindrome
def test5_s : String := "a"
def test5_Expected : Bool := true

-- Test case 6: two different characters is not a palindrome
def test6_s : String := "ab"
def test6_Expected : Bool := false

-- Test case 7: two same characters is a palindrome
def test7_s : String := "aa"
def test7_Expected : Bool := true

-- Test case 8: longer non-palindrome
def test8_s : String := "hello"
def test8_Expected : Bool := false

-- Test case 9: palindrome with spaces (treated as regular characters)
def test9_s : String := "a a"
def test9_Expected : Bool := true

-- Test case 10: case-sensitive check - "Aba" is not a palindrome (A != a)
def test10_s : String := "Aba"
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isPalindrome test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isPalindrome test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isPalindrome test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isPalindrome test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isPalindrome test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isPalindrome test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isPalindrome test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isPalindrome test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isPalindrome test9_s).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isPalindrome test10_s).run), DivM.res test10_Expected ]
end Assertions

section Pbt
extract_program_for isPalindrome
prove_precondition_decidable_for isPalindrome
prove_postcondition_decidable_for isPalindrome
derive_tester_for isPalindrome
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := isPalindromeTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break

end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isPalindrome by
  -- loom_solve <;> (try simp at *; expose_names)


prove_correct isPalindrome by
  loom_solve <;> (try simp at *; expose_names)
end Proof
