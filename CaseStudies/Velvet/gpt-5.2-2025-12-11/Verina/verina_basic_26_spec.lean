import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isEven: determine whether a given integer is even
    Natural language breakdown:
    1. The input is an integer n.
    2. The output is a Boolean.
    3. The output is true exactly when n is even.
    4. The output is false exactly when n is odd.
    5. Evenness for integers can be characterized by remainder modulo 2 being 0.
    6. There are no preconditions: the function is defined for all integers.
-/

section Specs

-- Helper definition: evenness via Int modulo.
-- We use the standard `%` on `Int` (implemented via `Int.fmod`).
def IntIsEven (n : Int) : Prop := n % 2 = 0

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ IntIsEven n) ∧
  (result = false ↔ ¬ IntIsEven n)

end Specs

section Impl

method isEven (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure false

end Impl

section TestCases

-- Test case 1: example from prompt: n = 4
-- 4 is even

def test1_n : Int := 4
def test1_Expected : Bool := true

-- Test case 2: example from prompt: n = 7
-- 7 is odd

def test2_n : Int := 7
def test2_Expected : Bool := false

-- Test case 3: example from prompt: n = 0
-- 0 is even

def test3_n : Int := 0
def test3_Expected : Bool := true

-- Test case 4: example from prompt: n = -2
-- -2 is even

def test4_n : Int := -2
def test4_Expected : Bool := true

-- Test case 5: example from prompt: n = -3
-- -3 is odd

def test5_n : Int := -3
def test5_Expected : Bool := false

-- Test case 6: small positive even

def test6_n : Int := 2
def test6_Expected : Bool := true

-- Test case 7: small positive odd

def test7_n : Int := 1
def test7_Expected : Bool := false

-- Test case 8: negative odd boundary-ish

def test8_n : Int := -1
def test8_Expected : Bool := false

-- Recommend to validate: 1, 4, 2

end TestCases
