import Lean
import Mathlib.Tactic

namespace VerinaSpec

def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a.toList
  -- !benchmark @end precond

def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo

def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) (h_precond : BinarySearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: array must be sorted in non-decreasing order
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNonDecreasing a

-- Postcondition clauses
-- 1. Result is a valid index (between 0 and size inclusive)
def ensures1 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  result ≤ a.size

-- 2. All elements before the result index are strictly less than the key
def ensures2 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ∀ i : Nat, i < result → a[i]! < key

-- 3. All elements from the result index onwards are greater than or equal to the key
def ensures3 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ∀ i : Nat, result ≤ i → i < a.size → a[i]! ≥ key

def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ensures1 a key result ∧
  ensures2 a key result ∧
  ensures3 a key result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.BinarySearch_precond a key ↔ LeetProofSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Nat) (h_precond : VerinaSpec.BinarySearch_precond a key):
  VerinaSpec.BinarySearch_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  sorry
