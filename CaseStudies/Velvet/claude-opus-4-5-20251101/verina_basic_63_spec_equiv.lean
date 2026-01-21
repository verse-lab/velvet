import Lean
import Mathlib.Tactic

namespace VerinaSpec

def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b

def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  -- !benchmark @start precond
  threshold ≥ 0.0 ∧
  ¬threshold.isNaN ∧
  numbers.all (fun x => ¬x.isNaN ∧ ¬x.isInf)  -- no NaN or Inf values
  -- !benchmark @end precond

def has_close_elements_postcond (numbers : List Float) (threshold : Float) (result: Bool) (h_precond : has_close_elements_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  ¬ result ↔ (List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a Float is valid (not NaN and not infinite)
def isValidFloat (f : Float) : Prop :=
  ¬f.isNaN ∧ ¬f.isInf

-- Helper: Check if all floats in a list are valid
def allValidFloats (numbers : List Float) : Prop :=
  ∀ i, i < numbers.length → isValidFloat numbers[i]!

-- Helper: Check if threshold is valid (non-negative and valid float)
def isValidThreshold (threshold : Float) : Prop :=
  isValidFloat threshold ∧ threshold ≥ 0.0

-- Helper: Absolute difference between two floats
def floatAbsDiff (a : Float) (b : Float) : Float :=
  Float.abs (a - b)

-- Helper: Check if a pair of elements at distinct indices are close
def hasClosePair (numbers : List Float) (threshold : Float) : Prop :=
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧
    floatAbsDiff numbers[i]! numbers[j]! < threshold

-- Precondition: threshold is valid and all numbers are valid floats
def precondition (numbers : List Float) (threshold : Float) :=
  isValidThreshold threshold ∧ allValidFloats numbers

-- Postcondition: result is true iff there exists a close pair
def postcondition (numbers : List Float) (threshold : Float) (result : Bool) :=
  result = true ↔ hasClosePair numbers threshold

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (numbers : List Float) (threshold : Float):
  VerinaSpec.has_close_elements_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold := by
  sorry

theorem postcondition_equiv (numbers : List Float) (threshold : Float) (result : Bool) (h_precond : VerinaSpec.has_close_elements_precond numbers threshold):
  VerinaSpec.has_close_elements_postcond numbers threshold result h_precond ↔ LeetProofSpec.postcondition numbers threshold result := by
  sorry
