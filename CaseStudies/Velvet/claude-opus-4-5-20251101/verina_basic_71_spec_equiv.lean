/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 71b33fc9-e1c8-435d-8384-eebca11cea9b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (str1 : List Char) (str2 : List Char):
  VerinaSpec.LongestCommonPrefix_precond str1 str2 ↔ LeetProofSpec.precondition str1 str2

- theorem postcondition_equiv (str1 : List Char) (str2 : List Char) (result : List Char) (h_precond : VerinaSpec.LongestCommonPrefix_precond str1 str2):
  VerinaSpec.LongestCommonPrefix_postcond str1 str2 result h_precond ↔ LeetProofSpec.postcondition str1 str2 result
-/

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
  True

-- no preconditions needed

def postcondition (str1 : List Char) (str2 : List Char) (result : List Char) :=
  ensures1 str1 str2 result ∧
  ensures2 str1 str2 result ∧
  ensures3 str1 str2 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (str1 : List Char) (str2 : List Char):
  VerinaSpec.LongestCommonPrefix_precond str1 str2 ↔ LeetProofSpec.precondition str1 str2 := by
  -- Since both preconditions are trivially true, the equivalence is immediate. We can use the fact that True is equivalent to itself.
  simp [VerinaSpec.LongestCommonPrefix_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (str1 : List Char) (str2 : List Char) (result : List Char) (h_precond : VerinaSpec.LongestCommonPrefix_precond str1 str2):
  VerinaSpec.LongestCommonPrefix_postcond str1 str2 result h_precond ↔ LeetProofSpec.postcondition str1 str2 result := by
  unfold VerinaSpec.LongestCommonPrefix_postcond LeetProofSpec.postcondition;
  constructor <;> intro h;
  · refine' ⟨ _, _, _ ⟩;
    · exact h.2.1.symm ▸ List.take_prefix _ _;
    · exact h.2.2.2.1.symm ▸ List.take_prefix _ _;
    · intro p hp1 hp2;
      rcases hp1 with ⟨ q, rfl ⟩ ; rcases hp2 with ⟨ r, rfl ⟩;
      grind;
  · rcases h with ⟨ h1, h2, h3 ⟩;
    rcases h1 with ⟨ k, rfl ⟩ ; rcases h2 with ⟨ l, rfl ⟩ ; simp_all +decide [ List.take_append ];
    contrapose! h3;
    -- Since $k$ and $l$ are non-empty and their first elements are equal, the longest common prefix of $result ++ k$ and $result ++ l$ is $result ++ [k.head!]$.
    have h_lcp : result ++ [k.head!] <+: result ++ k ∧ result ++ [k.head!] <+: result ++ l := by
      cases k <;> cases l <;> aesop;
    exact fun h => by have := h _ h_lcp.1 h_lcp.2; simp_all +decide ;