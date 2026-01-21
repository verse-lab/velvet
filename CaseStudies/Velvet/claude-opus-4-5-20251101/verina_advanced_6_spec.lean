import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    allVowels: Determine whether a given string contains all 5 English vowels (a, e, i, o, u)
    Natural language breakdown:
    1. The input is a string that may contain any characters
    2. The check is case-insensitive (both 'A' and 'a' count as the vowel 'a')
    3. All 5 vowels must be present: a, e, i, o, u
    4. Return true if all 5 vowels are found, false otherwise
    5. The vowels can appear anywhere in the string, in any order
    6. Each vowel only needs to appear at least once
    7. Use String.toLower for case-insensitive comparison
-/

section Specs

-- Define the set of vowels as lowercase characters
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']

-- Precondition: no restrictions on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff all 5 vowels appear in the string (case-insensitive)
-- Using property-based specification with List.all and membership
def postcondition (s : String) (result : Bool) : Prop :=
  result = (vowels.all (fun v => v ∈ s.toLower.toList))

end Specs

section Impl

method allVowels (s: String)
  return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: "education" contains all vowels (e, u, a, i, o)
def test1_s : String := "education"
def test1_Expected : Bool := true

-- Test case 2: "education123" contains all vowels with non-alpha chars
def test2_s : String := "education123"
def test2_Expected : Bool := true

-- Test case 3: "AEIOU" contains all vowels in uppercase
def test3_s : String := "AEIOU"
def test3_Expected : Bool := true

-- Test case 4: "hello" is missing some vowels (only has e, o)
def test4_s : String := "hello"
def test4_Expected : Bool := false

-- Test case 5: empty string has no vowels
def test5_s : String := ""
def test5_Expected : Bool := false

-- Test case 6: "apple orange union" contains all vowels across multiple words
def test6_s : String := "apple orange union"
def test6_Expected : Bool := true

-- Test case 7: "bcdfg" has no vowels at all
def test7_s : String := "bcdfg"
def test7_Expected : Bool := false

-- Test case 8: "aeiou" contains exactly all vowels in lowercase
def test8_s : String := "aeiou"
def test8_Expected : Bool := true

-- Test case 9: "AeIoU" mixed case vowels
def test9_s : String := "AeIoU"
def test9_Expected : Bool := true

-- Test case 10: "aaaa" only has one vowel repeated
def test10_s : String := "aaaa"
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4

end TestCases
