import Lean
import Mathlib.Tactic

namespace VerinaSpec

def below_zero_precond (operations : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  -- !benchmark @start postcond
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper to compute the sum of the first n elements of a list
def listPrefixSum (ops : List Int) (n : Nat) : Int :=
  (ops.take n).sum

-- Precondition: no constraints on the input list
def precondition (operations : List Int) : Prop :=
  True

-- Postcondition: specifies the properties of the output array and boolean
def postcondition (operations : List Int) (result : Array Int × Bool) : Prop :=
  let arr := result.1
  let hasNegative := result.2
  -- The array size is one more than the operations length
  arr.size = operations.length + 1 ∧
  -- The first element is 0
  arr[0]! = 0 ∧
  -- Each element at index i equals the sum of the first i operations
  (∀ i : Nat, i ≤ operations.length → arr[i]! = listPrefixSum operations i) ∧
  -- The boolean is true iff there exists an index i (1 ≤ i ≤ operations.length) 
  -- such that the partial sum at index i is negative
  (hasNegative = true ↔ ∃ i : Nat, 1 ≤ i ∧ i ≤ operations.length ∧ arr[i]! < 0)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (operations : List Int):
  VerinaSpec.below_zero_precond operations ↔ LeetProofSpec.precondition operations := by
  sorry

theorem postcondition_equiv (operations : List Int) (result : (Array Int × Bool)) (h_precond : VerinaSpec.below_zero_precond operations):
  VerinaSpec.below_zero_postcond operations result h_precond ↔ LeetProofSpec.postcondition operations result := by
  sorry
