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
    removeElement: remove the element at index k from an array of integers.
    Natural language breakdown:
    1. Inputs are an integer array s and a natural number k (0-indexed).
    2. k is assumed to be a valid index, i.e., 0 ≤ k < s.size.
    3. The output is an array containing all elements of s except the one at index k.
    4. Elements before index k are unchanged and keep their positions.
    5. Elements after index k are shifted left by one position.
    6. The output array has size exactly s.size - 1.
-/

section Specs

-- Helper: describe the element-wise relationship between input and output after removing index k.
-- For output index i:
-- * if i < k, output[i] = s[i]
-- * if i ≥ k, output[i] = s[i+1]

def precondition (s : Array Int) (k : Nat) : Prop :=
  k < s.size

def postcondition (s : Array Int) (k : Nat) (result : Array Int) : Prop :=
  result.size + 1 = s.size ∧
  (∀ (i : Nat), i < result.size →
      (if i < k then result[i]! = s[i]! else result[i]! = s[i + 1]!))

end Specs

section Impl

method removeElement (s : Array Int) (k : Nat)
  return (result : Array Int)
  require precondition s k
  ensures postcondition s k result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: example from prompt
-- remove index 2 from #[1,2,3,4,5]

def test1_s : Array Int := #[1, 2, 3, 4, 5]
def test1_k : Nat := 2
def test1_Expected : Array Int := #[1, 2, 4, 5]

-- Test case 2: remove first element

def test2_s : Array Int := #[10, 20, 30, 40]
def test2_k : Nat := 0
def test2_Expected : Array Int := #[20, 30, 40]

-- Test case 3: remove last element

def test3_s : Array Int := #[10, 20, 30, 40]
def test3_k : Nat := 3
def test3_Expected : Array Int := #[10, 20, 30]

-- Test case 4: singleton array becomes empty

def test4_s : Array Int := #[7]
def test4_k : Nat := 0
def test4_Expected : Array Int := #[]

-- Test case 5: remove from middle with negative ints

def test5_s : Array Int := #[-1, 0, 5, -7]
def test5_k : Nat := 1
def test5_Expected : Array Int := #[-1, 5, -7]

-- Test case 6: remove from size-2 array, remove last

def test6_s : Array Int := #[3, 9]
def test6_k : Nat := 1
def test6_Expected : Array Int := #[3]

-- Test case 7: remove from size-2 array, remove first

def test7_s : Array Int := #[3, 9]
def test7_k : Nat := 0
def test7_Expected : Array Int := #[9]

-- Test case 8: repeated values; removing one occurrence at index k

def test8_s : Array Int := #[2, 2, 2, 2]
def test8_k : Nat := 2
def test8_Expected : Array Int := #[2, 2, 2]

-- Recommend to validate: 1, 2, 4

end TestCases
