/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e5a205dc-36f1-400f-a244-7257b9b03f0b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) (k : Nat):
  VerinaSpec.shortestBeautifulSubstring_precond s k ↔ LeetProofSpec.precondition s k

The following was negated by Aristotle:

- theorem postcondition_equiv (s : String) (k : Nat) (result : String) (h_precond : VerinaSpec.shortestBeautifulSubstring_precond s k):
  VerinaSpec.shortestBeautifulSubstring_postcond s k result h_precond ↔ LeetProofSpec.postcondition s k result

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

@[reducible]
def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  -- !benchmark @start precond
  s.toList.all (fun c => c = '0' ∨ c = '1')

-- !benchmark @end precond

def listToString (lst : List Char) : String :=
  String.mk lst

def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

@[reducible]
def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : Prop :=
  -- !benchmark @start postcond
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Check if a string is a binary string (only '0' and '1')
def isBinaryString (s : String) : Prop :=
  ∀ c, c ∈ s.toList → c = '0' ∨ c = '1'

-- Count the number of '1' characters in a string
def countOnes (s : String) : Nat :=
  s.toList.count '1'

-- Check if a string is a substring of another starting at position i with length len
def isSubstringAt (s : String) (sub : String) (i : Nat) : Prop :=
  i + sub.length ≤ s.length ∧
  ∀ j : Nat, j < sub.length → s.toList[i + j]! = sub.toList[j]!

-- Check if sub is a contiguous substring of s
def isSubstringOf (s : String) (sub : String) : Prop :=
  ∃ i : Nat, isSubstringAt s sub i

-- A valid candidate substring has exactly k ones
def isValidCandidate (s : String) (sub : String) (k : Nat) : Prop :=
  isSubstringOf s sub ∧ countOnes sub = k

-- Check if result is the optimal (shortest, then lexicographically smallest) among valid candidates
def isOptimalResult (s : String) (k : Nat) (result : String) : Prop :=
  isValidCandidate s result k ∧
  (∀ other : String, isValidCandidate s other k →
    result.length < other.length ∨
    (result.length = other.length ∧ result ≤ other))

-- Check if no valid candidate exists
def noValidCandidate (s : String) (k : Nat) : Prop :=
  ¬∃ sub : String, isValidCandidate s sub k

-- Precondition: s must be a binary string
def precondition (s : String) (k : Nat) :=
  isBinaryString s

-- Postcondition clauses
def ensures1 (s : String) (k : Nat) (result : String) :=
  noValidCandidate s k → result = ""

def ensures2 (s : String) (k : Nat) (result : String) :=
  (∃ sub : String, isValidCandidate s sub k) → isOptimalResult s k result

def postcondition (s : String) (k : Nat) (result : String) :=
  ensures1 s k result ∧ ensures2 s k result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String) (k : Nat):
  VerinaSpec.shortestBeautifulSubstring_precond s k ↔ LeetProofSpec.precondition s k := by
  -- By definition of `VerinaSpec.shortestBeautifulSubstring_precond`, it requires that all characters in `s` are either '0' or '1'.
  simp [VerinaSpec.shortestBeautifulSubstring_precond, LeetProofSpec.precondition];
  exact?

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The precondition holds for s="0" and k=0.
-/
theorem precond_holds_0_0 : VerinaSpec.shortestBeautifulSubstring_precond "0" 0 := by
  -- The string "0" has exactly one '0' and no '1's, so it satisfies the precondition.
  simp [VerinaSpec.shortestBeautifulSubstring_precond]

/-
VerinaSpec holds for s="0", k=0, result="0".
-/
theorem verina_holds_0_0 (h : VerinaSpec.shortestBeautifulSubstring_precond "0" 0) :
  VerinaSpec.shortestBeautifulSubstring_postcond "0" 0 "0" h := by
  unfold VerinaSpec.shortestBeautifulSubstring_postcond
  simp [VerinaSpec.countOnes, VerinaSpec.allSubstrings, VerinaSpec.listToString]
  -- We need to show that "0" is in the targets and is optimal.
  -- targets calculation:
  -- substrings of "0" are "" and "0".
  -- both have 0 ones, so both are beautiful.
  -- targets filters out "", so targets = ["0"].
  -- result "0" is in targets.
  -- "0" is optimal in targets (only element).
  exact ⟨ ⟨ [ '0' ], ⟨ ⟨ 1, by decide, rfl ⟩, rfl ⟩, rfl ⟩, by rintro r a ha₁ ha₂ rfl hr; interval_cases a <;> simp_all +decide ⟩

/-
LeetProofSpec fails for s="0", k=0, result="0" because the empty string is a better candidate.
-/
theorem leet_fails_0_0 : ¬ LeetProofSpec.postcondition "0" 0 "0" := by
  intro h
  have h2 := h.2
  have h_empty_valid : LeetProofSpec.isValidCandidate "0" "" 0 := by
    simp [LeetProofSpec.isValidCandidate, LeetProofSpec.isSubstringOf, LeetProofSpec.isSubstringAt, LeetProofSpec.countOnes]
    use 0
    simp
  have h_opt := h2 ⟨"", h_empty_valid⟩
  have h_better := h_opt.2 "" h_empty_valid
  simp at h_better

end AristotleLemmas

theorem postcondition_equiv (s : String) (k : Nat) (result : String) (h_precond : VerinaSpec.shortestBeautifulSubstring_precond s k):
  VerinaSpec.shortestBeautifulSubstring_postcond s k result h_precond ↔ LeetProofSpec.postcondition s k result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where `s = "0"` and `k = 0`.
  use "0", 0, "0";
  -- Apply the lemmas to conclude the proof.
  apply Exists.intro (precond_holds_0_0)
  apply Or.inl
  exact ⟨verina_holds_0_0 (precond_holds_0_0), leet_fails_0_0⟩

-/
theorem postcondition_equiv (s : String) (k : Nat) (result : String) (h_precond : VerinaSpec.shortestBeautifulSubstring_precond s k):
  VerinaSpec.shortestBeautifulSubstring_postcond s k result h_precond ↔ LeetProofSpec.postcondition s k result := by
  sorry