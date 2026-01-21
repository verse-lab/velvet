import Lean
import Mathlib.Tactic

namespace VerinaSpec

def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)

def toUppercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Postcondition clauses

-- The result has the same length as the input
def ensures1 (s : String) (result : String) :=
  result.length = s.length

-- Each character in the result is the uppercase version of the corresponding input character
def ensures2 (s : String) (result : String) :=
  ∀ i : Nat, i < s.length → result.toList[i]! = (s.toList[i]!).toUpper

def precondition (s : String) :=
  True  -- no preconditions, any string is valid

def postcondition (s : String) (result : String) :=
  ensures1 s result ∧ ensures2 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.toUppercase_precond s ↔ LeetProofSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.toUppercase_precond s):
  VerinaSpec.toUppercase_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  sorry
