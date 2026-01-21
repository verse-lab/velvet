import Lean
import Mathlib.Tactic

namespace VerinaSpec

def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList
  -- !benchmark @end precond

def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n

def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  -- !benchmark @start postcond
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: compute absolute difference between two integers as a natural number
def absDiff (x : Int) (y : Int) : Nat := (x - y).natAbs

-- Helper: check if a value is achievable as a difference between some pair
def isAchievableDiff (a : Array Int) (b : Array Int) (val : Nat) : Prop :=
  ∃ i j, i < a.size ∧ j < b.size ∧ absDiff a[i]! b[j]! = val

-- Helper: check if a value is minimal among all pairwise differences
def isMinimalDiff (a : Array Int) (b : Array Int) (val : Nat) : Prop :=
  ∀ i j, i < a.size → j < b.size → val ≤ absDiff a[i]! b[j]!

-- Helper: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition clauses
def require1 (a : Array Int) (b : Array Int) :=
  a.size > 0  -- First array is non-empty

def require2 (a : Array Int) (b : Array Int) :=
  b.size > 0  -- Second array is non-empty

def require3 (a : Array Int) (b : Array Int) :=
  isSortedNonDecreasing a  -- First array is sorted

def require4 (a : Array Int) (b : Array Int) :=
  isSortedNonDecreasing b  -- Second array is sorted

-- Postcondition clauses
def ensures1 (a : Array Int) (b : Array Int) (result : Nat) :=
  isAchievableDiff a b result  -- Result is achievable

def ensures2 (a : Array Int) (b : Array Int) (result : Nat) :=
  isMinimalDiff a b result  -- Result is minimal

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b ∧ require2 a b ∧ require3 a b ∧ require4 a b

def postcondition (a : Array Int) (b : Array Int) (result : Nat) :=
  ensures1 a b result ∧ ensures2 a b result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.CanyonSearch_precond a b ↔ LeetProofSpec.precondition a b := by
  sorry

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Nat) (h_precond : VerinaSpec.CanyonSearch_precond a b):
  VerinaSpec.CanyonSearch_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  sorry
