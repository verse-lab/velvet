import Lean
import Mathlib.Tactic

namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 = 0

def findEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if an integer is even
def isEven (n : Int) : Bool := n % 2 = 0

-- Postcondition clause 1: Every element in result is even
def ensures1 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ i : Nat, i < result.size → isEven (result[i]!) = true

-- Postcondition clause 2: Result is a sublist of the input (preserves order)
def ensures2 (arr : Array Int) (result : Array Int) : Prop :=
  result.toList.Sublist arr.toList

-- Postcondition clause 3: Every even element from input appears in result with same count
def ensures3 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, isEven x = true → result.toList.count x = arr.toList.count x

-- Postcondition clause 4: No odd elements in result
def ensures4 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, isEven x = false → result.toList.count x = 0

def precondition (arr : Array Int) : Prop :=
  True  -- no preconditions

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  ensures1 arr result ∧
  ensures2 arr result ∧
  ensures3 arr result ∧
  ensures4 arr result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int):
  VerinaSpec.findEvenNumbers_precond arr ↔ LeetProofSpec.precondition arr := by
  sorry

theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.findEvenNumbers_precond arr):
  VerinaSpec.findEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  sorry
