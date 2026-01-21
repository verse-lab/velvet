import Lean
import Mathlib.Tactic

namespace VerinaSpec

def secondSmallest_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!  -- at least two distinct values
  -- !benchmark @end precond

def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i

def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  -- !benchmark @start postcond
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if array has at least two distinct values
def hasAtLeastTwoDistinct (arr : Array Int) : Prop :=
  ∃ i j, i < arr.size ∧ j < arr.size ∧ arr[i]! ≠ arr[j]!

-- Find the minimum element in an array (for specification purposes)
def isMinimum (arr : Array Int) (m : Int) : Prop :=
  (∃ i, i < arr.size ∧ arr[i]! = m) ∧
  (∀ j, j < arr.size → arr[j]! ≥ m)

-- Check if a value is in the array
def inArray (arr : Array Int) (val : Int) : Prop :=
  ∃ i, i < arr.size ∧ arr[i]! = val

-- Precondition clauses
def require1 (s : Array Int) :=
  s.size ≥ 2  -- Array has at least two elements

def require2 (s : Array Int) :=
  hasAtLeastTwoDistinct s  -- Array has at least two distinct values

-- Postcondition clauses
-- The result is an element of the array
def ensures1 (s : Array Int) (result : Int) :=
  inArray s result

-- The result is strictly greater than the minimum
def ensures2 (s : Array Int) (result : Int) :=
  ∀ m, isMinimum s m → result > m

-- No element in the array is strictly between the minimum and the result
def ensures3 (s : Array Int) (result : Int) :=
  ∀ m, isMinimum s m →
    ∀ i, i < s.size → (s[i]! > m → s[i]! ≥ result)

def precondition (s : Array Int) :=
  require1 s ∧ require2 s

def postcondition (s : Array Int) (result : Int) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : Array Int):
  VerinaSpec.secondSmallest_precond s ↔ LeetProofSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : Array Int) (result : Int) (h_precond : VerinaSpec.secondSmallest_precond s):
  VerinaSpec.secondSmallest_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  sorry
