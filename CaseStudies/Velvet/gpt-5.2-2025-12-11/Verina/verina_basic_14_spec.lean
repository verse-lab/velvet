import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsZ: Determine whether a given string contains the character 'z' or 'Z'.
    Natural language breakdown:
    1. Input is a string s.
    2. The method returns a Boolean.
    3. The result is true exactly when s contains at least one character equal to 'z' or equal to 'Z'.
    4. Otherwise the result is false.
    5. There are no preconditions.
-/

section Specs

-- Helper predicate: the string contains 'z' or 'Z'.
-- We state this via membership of the character list representation of the string.
def hasZ (s : String) : Prop :=
  ('z' ∈ s.toList) ∨ ('Z' ∈ s.toList)

-- No preconditions.
def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff s contains 'z' or 'Z'.
def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ hasZ s) ∧
  (result = false ↔ ¬ hasZ s)

end Specs

section Impl

method containsZ (s : String) return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
    pure false

end Impl

section TestCases

-- Test case 1: provided example "hello" has no z/Z
-- IMPORTANT example to validate.
def test1_s : String := "hello"
def test1_Expected : Bool := false

-- Test case 2: contains lowercase z
-- IMPORTANT example to validate.
def test2_s : String := "zebra"
def test2_Expected : Bool := true

-- Test case 3: contains uppercase Z
-- IMPORTANT example to validate.
def test3_s : String := "Zebra"
def test3_Expected : Bool := true

-- Test case 4: empty string

def test4_s : String := ""
def test4_Expected : Bool := false

-- Test case 5: z in the middle/end

def test5_s : String := "crazy"
def test5_Expected : Bool := true

-- Test case 6: short string containing Z

def test6_s : String := "AZ"
def test6_Expected : Bool := true

-- Test case 7: no z/Z

def test7_s : String := "abc"
def test7_Expected : Bool := false

-- Test case 8: both Z and z

def test8_s : String := "Zz"
def test8_Expected : Bool := true

-- Test case 9: spaces and no z/Z

def test9_s : String := "no letter"
def test9_Expected : Bool := false

-- Recommend to validate: 1, 2, 3

end TestCases
