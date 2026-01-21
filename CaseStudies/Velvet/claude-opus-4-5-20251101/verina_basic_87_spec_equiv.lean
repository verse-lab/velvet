import Lean
import Mathlib.Tactic

namespace VerinaSpec

def SelectionSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: Check if two arrays are permutations of each other using count equality
def isPermutation (a b : Array Int) : Prop :=
  a.size = b.size ∧ ∀ x : Int, a.toList.count x = b.toList.count x

-- Precondition: no constraints needed, any array is valid input
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  isSortedNonDecreasing result ∧ isPermutation a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.SelectionSort_precond a ↔ LeetProofSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.SelectionSort_precond a):
  VerinaSpec.SelectionSort_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  sorry
