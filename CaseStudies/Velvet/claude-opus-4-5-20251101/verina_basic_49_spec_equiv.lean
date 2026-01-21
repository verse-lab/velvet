import Lean
import Mathlib.Tactic

namespace VerinaSpec

def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0

def findFirstOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond

def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  -- !benchmark @start postcond
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if an integer is odd
def isOddInt (n : Int) : Prop := n % 2 ≠ 0

-- Helper: Check if an integer is even
def isEvenInt (n : Int) : Prop := n % 2 = 0

-- Precondition: array must be non-empty
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: characterizes the result
def postcondition (a : Array Int) (result : Option Nat) :=
  match result with
  | none =>
      -- No odd number exists in the array
      ∀ i : Nat, i < a.size → isEvenInt a[i]!
  | some idx =>
      -- idx is a valid index with an odd number
      idx < a.size ∧
      isOddInt a[idx]! ∧
      -- idx is the smallest such index (all elements before are even)
      (∀ j : Nat, j < idx → isEvenInt a[j]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.findFirstOdd_precond a ↔ LeetProofSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Option Nat) (h_precond : VerinaSpec.findFirstOdd_precond a):
  VerinaSpec.findFirstOdd_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  sorry
