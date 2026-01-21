import Lean
import Mathlib.Tactic

namespace VerinaSpec

def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  -- !benchmark @start postcond
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Postcondition clauses

-- The result is a prefix of str1
def ensures1 (str1 : List Char) (str2 : List Char) (result : List Char) :=
  result <+: str1

-- The result is a prefix of str2
def ensures2 (str1 : List Char) (str2 : List Char) (result : List Char) :=
  result <+: str2

-- Maximality: any longer common prefix does not exist
-- i.e., for any list that is a common prefix of both, its length is at most result.length
def ensures3 (str1 : List Char) (str2 : List Char) (result : List Char) :=
  ∀ p : List Char, p <+: str1 → p <+: str2 → p.length ≤ result.length

def precondition (str1 : List Char) (str2 : List Char) :=
  True  -- no preconditions needed

def postcondition (str1 : List Char) (str2 : List Char) (result : List Char) :=
  ensures1 str1 str2 result ∧
  ensures2 str1 str2 result ∧
  ensures3 str1 str2 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (str1 : List Char) (str2 : List Char):
  VerinaSpec.LongestCommonPrefix_precond str1 str2 ↔ LeetProofSpec.precondition str1 str2 := by
  sorry

theorem postcondition_equiv (str1 : List Char) (str2 : List Char) (result : List Char) (h_precond : VerinaSpec.LongestCommonPrefix_precond str1 str2):
  VerinaSpec.LongestCommonPrefix_postcond str1 str2 result h_precond ↔ LeetProofSpec.postcondition str1 str2 result := by
  sorry
