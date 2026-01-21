import Lean
import Mathlib.Tactic

namespace VerinaSpec

def BubbleSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a

def BubbleSort_postcond (a : Array Int) (result: Array Int) (h_precond : BubbleSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: check if array is sorted in non-decreasing order
def isSortedArray (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper function: check if two arrays are permutations of each other
-- Using List.Perm via toList
def isPermutationArray (arr1 arr2 : Array Int) : Prop :=
  arr1.toList.Perm arr2.toList

-- Precondition: no restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition clauses
-- 1. Result is sorted in non-decreasing order
def ensures1 (a : Array Int) (result : Array Int) : Prop :=
  isSortedArray result

-- 2. Result is a permutation of input (preserves multiset and implies same size)
def ensures2 (a : Array Int) (result : Array Int) : Prop :=
  isPermutationArray a result

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  ensures1 a result ∧
  ensures2 a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.BubbleSort_precond a ↔ LeetProofSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.BubbleSort_precond a):
  VerinaSpec.BubbleSort_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  sorry
