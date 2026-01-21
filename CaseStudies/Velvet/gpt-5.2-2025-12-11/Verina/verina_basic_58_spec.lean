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
    double_array_elements: Transform an array of integers by doubling each element.
    Natural language breakdown:
    1. Input is an array s of integers.
    2. Output is an array result of integers.
    3. The output array has the same size as the input array.
    4. For every valid index i (i < s.size), result[i]! equals 2 * s[i]!. 
    5. The input array is assumed valid, and doubling does not overflow (modeled as standard Int arithmetic).
-/

section Specs

-- Helper definition: element-wise doubling relation between input and output arrays.
-- We use Nat indices and Array.get! access with an explicit range hypothesis i < s.size.
def DoubledArray (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ (i : Nat), i < s.size → result[i]! = (2 : Int) * s[i]!

def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  DoubledArray s result

end Specs

section Impl

method double_array_elements (s : Array Int) return (result : Array Int)
  require precondition s
  ensures postcondition s result
  do
    pure #[]  -- placeholder body

end Impl

section TestCases

-- Test case 1: empty array
-- (Given example from the problem statement)
def test1_s : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: typical positive integers
-- (Given example from the problem statement)
def test2_s : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Array Int := #[2, 4, 6, 8, 10]

-- Test case 3: includes zero and negative
-- (Given example from the problem statement)
def test3_s : Array Int := #[0, -1, 5]
def test3_Expected : Array Int := #[0, -2, 10]

-- Test case 4: single element positive
-- (Given example from the problem statement)
def test4_s : Array Int := #[100]
def test4_Expected : Array Int := #[200]

-- Test case 5: all negative
-- (Given example from the problem statement)
def test5_s : Array Int := #[-3, -4]
def test5_Expected : Array Int := #[-6, -8]

-- Test case 6: single element zero

def test6_s : Array Int := #[0]
def test6_Expected : Array Int := #[0]

-- Test case 7: mixed signs

def test7_s : Array Int := #[7, -8, 9, -10]
def test7_Expected : Array Int := #[14, -16, 18, -20]

-- Test case 8: repeated values

def test8_s : Array Int := #[2, 2, 2]
def test8_Expected : Array Int := #[4, 4, 4]

-- Recommend to validate: test1, test2, test3

end TestCases
