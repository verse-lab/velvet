import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ifPowerOfFour: Determine whether a natural number is a power of four
    Natural language breakdown:
    1. A natural number n is a power of four if there exists a natural number x such that n = 4^x
    2. Powers of four are: 1 (4^0), 4 (4^1), 16 (4^2), 64 (4^3), 256 (4^4), 1024 (4^5), ...
    3. 0 is NOT a power of four (there is no x such that 4^x = 0)
    4. 1 is a power of four (4^0 = 1)
    5. Numbers like 2, 3, 8, etc. are not powers of four
    6. The function returns true if n is a power of four, false otherwise
    
    Key observations:
    - 4^x is always positive for any natural x, so 0 is never a power of four
    - We need to check if n can be expressed as 4^x for some natural x
    - This is equivalent to checking if n = (2^2)^x = 2^(2x), i.e., n is a power of 2 with even exponent
-/

section Specs

-- Predicate: n is a power of four if there exists some natural x where 4^x = n
def isPowerOfFour (n : Nat) : Prop :=
  ∃ x : Nat, 4 ^ x = n

-- Postcondition: result is true iff n is a power of four
def ensures1 (n : Nat) (result : Bool) :=
  result = true ↔ isPowerOfFour n

def precondition (n : Nat) :=
  True  -- no preconditions

def postcondition (n : Nat) (result : Bool) :=
  ensures1 n result

end Specs

section Impl

method ifPowerOfFour (n: Nat)
  return (result: Bool)
  require precondition n
  ensures postcondition n result
  do
    pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 0, not a power of four (no x such that 4^x = 0)
def test1_n : Nat := 0
def test1_Expected : Bool := false

-- Test case 2: n = 1, power of four (4^0 = 1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: n = 2, not a power of four
def test3_n : Nat := 2
def test3_Expected : Bool := false

-- Test case 4: n = 4, power of four (4^1 = 4)
def test4_n : Nat := 4
def test4_Expected : Bool := true

-- Test case 5: n = 8, not a power of four (8 = 2^3, but not 4^x)
def test5_n : Nat := 8
def test5_Expected : Bool := false

-- Test case 6: n = 16, power of four (4^2 = 16)
def test6_n : Nat := 16
def test6_Expected : Bool := true

-- Test case 7: n = 64, power of four (4^3 = 64)
def test7_n : Nat := 64
def test7_Expected : Bool := true

-- Test case 8: n = 100, not a power of four
def test8_n : Nat := 100
def test8_Expected : Bool := false

-- Test case 9: n = 256, power of four (4^4 = 256)
def test9_n : Nat := 256
def test9_Expected : Bool := true

-- Test case 10: n = 1024, power of four (4^5 = 1024)
def test10_n : Nat := 1024
def test10_Expected : Bool := true

-- Recommend to validate: 2, 4, 6 (covers 4^0=1, 4^1=4, 4^2=16 - small but representative powers)

end TestCases
