import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    insertChars: Insert a subarray of characters into another array at a specified position
    Natural language breakdown:
    1. Given an original array oline, we consider only its first l characters
    2. Given an insertion array nl, we consider only its first p characters
    3. The insertion happens at position atPos in the effective portion of oline
    4. Characters before atPos (indices 0 to atPos-1) remain unchanged
    5. The p characters from nl are inserted starting at index atPos
    6. Characters from oline starting at atPos are shifted right by p positions
    7. The resulting array has length l + p
    8. Preconditions:
       - atPos is within [0, l]
       - l does not exceed oline.size
       - p does not exceed nl.size
-/

section Specs

-- Precondition: valid bounds for all parameters
def precondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) :=
  atPos ≤ l ∧ l ≤ oline.size ∧ p ≤ nl.size

-- Postcondition clauses:
-- 1. The result has the correct length
def ensures1 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  result.size = l + p

-- 2. Characters before atPos come from oline unchanged
def ensures2 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ∀ i : Nat, i < atPos → result[i]! = oline[i]!

-- 3. Characters at positions atPos to atPos + p - 1 come from nl
def ensures3 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ∀ i : Nat, i < p → result[atPos + i]! = nl[i]!

-- 4. Characters from atPos onwards in oline are shifted right by p positions
def ensures4 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ∀ i : Nat, atPos ≤ i → i < l → result[i + p]! = oline[i]!

def postcondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ensures1 oline l nl p atPos result ∧
  ensures2 oline l nl p atPos result ∧
  ensures3 oline l nl p atPos result ∧
  ensures4 oline l nl p atPos result

end Specs

section Impl

method insertChars (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat)
  return (result : Array Char)
  require precondition oline l nl p atPos
  ensures postcondition oline l nl p atPos result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic insertion in the middle (example from problem)
def test1_oline : Array Char := #['a','b','c','d','e']
def test1_l : Nat := 5
def test1_nl : Array Char := #['X','Y']
def test1_p : Nat := 2
def test1_atPos : Nat := 2
def test1_Expected : Array Char := #['a','b','X','Y','c','d','e']

-- Test case 2: Insertion at the beginning
def test2_oline : Array Char := #['H','e','l','l','o']
def test2_l : Nat := 5
def test2_nl : Array Char := #['W','o','r','l','d']
def test2_p : Nat := 5
def test2_atPos : Nat := 0
def test2_Expected : Array Char := #['W','o','r','l','d','H','e','l','l','o']

-- Test case 3: Insertion at the end
def test3_oline : Array Char := #['L','e','a','n']
def test3_l : Nat := 4
def test3_nl : Array Char := #['4']
def test3_p : Nat := 1
def test3_atPos : Nat := 4
def test3_Expected : Array Char := #['L','e','a','n','4']

-- Test case 4: Empty insertion (p = 0)
def test4_oline : Array Char := #['T','e','s','t']
def test4_l : Nat := 4
def test4_nl : Array Char := #[]
def test4_p : Nat := 0
def test4_atPos : Nat := 2
def test4_Expected : Array Char := #['T','e','s','t']

-- Test case 5: Partial use of both arrays (l < oline.size)
def test5_oline : Array Char := #['1','2','3','4','5','6']
def test5_l : Nat := 5
def test5_nl : Array Char := #['a','b','c']
def test5_p : Nat := 3
def test5_atPos : Nat := 3
def test5_Expected : Array Char := #['1','2','3','a','b','c','4','5']

-- Test case 6: Single character insertion
def test6_oline : Array Char := #['A','B','C']
def test6_l : Nat := 3
def test6_nl : Array Char := #['Z']
def test6_p : Nat := 1
def test6_atPos : Nat := 1
def test6_Expected : Array Char := #['A','Z','B','C']

-- Test case 7: Insertion into single character array
def test7_oline : Array Char := #['X']
def test7_l : Nat := 1
def test7_nl : Array Char := #['A','B']
def test7_p : Nat := 2
def test7_atPos : Nat := 0
def test7_Expected : Array Char := #['A','B','X']

-- Test case 8: Empty original array (l = 0)
def test8_oline : Array Char := #[]
def test8_l : Nat := 0
def test8_nl : Array Char := #['H','i']
def test8_p : Nat := 2
def test8_atPos : Nat := 0
def test8_Expected : Array Char := #['H','i']

-- Test case 9: Partial use of nl (p < nl.size)
def test9_oline : Array Char := #['a','b','c']
def test9_l : Nat := 3
def test9_nl : Array Char := #['X','Y','Z']
def test9_p : Nat := 2
def test9_atPos : Nat := 1
def test9_Expected : Array Char := #['a','X','Y','b','c']

-- Test case 10: Both arrays partially used
def test10_oline : Array Char := #['1','2','3','4']
def test10_l : Nat := 2
def test10_nl : Array Char := #['a','b','c']
def test10_p : Nat := 1
def test10_atPos : Nat := 1
def test10_Expected : Array Char := #['1','a','2']

-- Recommend to validate: 1, 2, 4

end TestCases
