import Lean
import Mathlib.Tactic

namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 = 0

def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  result.all (fun x => isEven x) ∧
  result.toList.Sublist arr.toList ∧
  result.size = arr.toList.countP isEven
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: check if an integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Postcondition clause 1: result is a sublist of input (preserves order)
def ensures1 (arr : Array Int) (result : Array Int) : Prop :=
  result.toList.Sublist arr.toList

-- Postcondition clause 2: all elements in result are even
def ensures2 (result : Array Int) : Prop :=
  ∀ i : Nat, i < result.size → result[i]! % 2 = 0

-- Postcondition clause 3: count preservation for even elements
def ensures3 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, x % 2 = 0 → result.toList.count x = arr.toList.count x

-- Postcondition clause 4: odd elements have count 0 in result
def ensures4 (result : Array Int) : Prop :=
  ∀ x : Int, x % 2 ≠ 0 → result.toList.count x = 0

def precondition (arr : Array Int) : Prop :=
  True  -- no preconditions

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  ensures1 arr result ∧
  ensures2 result ∧
  ensures3 arr result ∧
  ensures4 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int):
  VerinaSpec.FindEvenNumbers_precond arr ↔ LeetProofSpec.precondition arr := by
  sorry

theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.FindEvenNumbers_precond arr):
  VerinaSpec.FindEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  sorry
