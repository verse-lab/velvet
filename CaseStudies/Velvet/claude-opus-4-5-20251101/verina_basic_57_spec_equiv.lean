import Lean
import Mathlib.Tactic

namespace VerinaSpec

def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input
def precondition (numbers : Array Int) (threshold : Int) :=
  True

-- Postcondition: result equals the count of elements less than threshold
-- Using Array.countP which counts elements satisfying a predicate
def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) :=
  result = numbers.countP (· < threshold)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (numbers : Array Int) (threshold : Int):
  VerinaSpec.CountLessThan_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold := by
  sorry

theorem postcondition_equiv (numbers : Array Int) (threshold : Int) (result : Nat) (h_precond : VerinaSpec.CountLessThan_precond numbers threshold):
  VerinaSpec.CountLessThan_postcond numbers threshold result h_precond ↔ LeetProofSpec.postcondition numbers threshold result := by
  sorry
