import Lean
import Mathlib.Tactic

namespace VerinaSpec

def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- The k-th odd number (0-indexed) is 2*k + 1
-- We use Finset.sum from Mathlib to express the sum

-- Postcondition: result equals the sum of fourth powers of first n odd numbers
def ensures1 (n : Nat) (result : Nat) :=
  result = Finset.sum (Finset.range n) (fun k => (2 * k + 1) ^ 4)

def precondition (n : Nat) :=
  True  -- n is any non-negative natural number

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n ↔ LeetProofSpec.precondition n := by
  sorry

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n):
  VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  sorry
