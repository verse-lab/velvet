import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsZ: Determine whether a string contains the character 'z' or 'Z'
    Natural language breakdown:
    1. Given a string s, check if it contains either lowercase 'z' or uppercase 'Z'
    2. Return true if the string contains at least one occurrence of 'z' or 'Z'
    3. Return false if the string does not contain any 'z' or 'Z' characters
    4. The check is case-insensitive for the letter z specifically
    5. Empty strings should return false (no characters to match)
    6. The position of 'z' or 'Z' in the string does not matter
-/

section Specs

-- Helper Functions
-- Using String.contains from Mathlib/Lean stdlib

-- Postcondition clauses
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ (s.contains 'z' ∨ s.contains 'Z')

def ensures2 (s : String) (result : Bool) :=
  result = false ↔ (¬s.contains 'z' ∧ ¬s.contains 'Z')

def precondition (s : String) :=
  True  -- no preconditions as stated in the problem

def postcondition (s : String) (result : Bool) :=
  ensures1 s result ∧ ensures2 s result

end Specs

section Impl

method containsZ (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: String without z or Z
def test1_s : String := "hello"
def test1_Expected : Bool := false

-- Test case 2: String starting with lowercase z
def test2_s : String := "zebra"
def test2_Expected : Bool := true

-- Test case 3: String starting with uppercase Z
def test3_s : String := "Zebra"
def test3_Expected : Bool := true

-- Test case 4: Empty string
def test4_s : String := ""
def test4_Expected : Bool := false

-- Test case 5: String with z in the middle
def test5_s : String := "crazy"
def test5_Expected : Bool := true

-- Test case 6: String ending with uppercase Z
def test6_s : String := "AZ"
def test6_Expected : Bool := true

-- Test case 7: String without z or Z (different)
def test7_s : String := "abc"
def test7_Expected : Bool := false

-- Test case 8: String with both z and Z
def test8_s : String := "Zz"
def test8_Expected : Bool := true

-- Test case 9: String with spaces but no z
def test9_s : String := "no letter"
def test9_Expected : Bool := false

-- Recommend to validate: 1, 2, 4

end TestCases
