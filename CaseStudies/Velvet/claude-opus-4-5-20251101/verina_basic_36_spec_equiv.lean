/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bce9f090-fb41-4fd8-859a-c14aad15721e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.replaceWithColon_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.replaceWithColon_precond s):
  VerinaSpec.replaceWithColon_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false

def replaceWithColon_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def replaceWithColon_postcond (s : String) (result: String) (h_precond : replaceWithColon_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < s.length →
    (isSpaceCommaDot cs[i]! → cs'[i]! = ':') ∧
    (¬isSpaceCommaDot cs[i]! → cs'[i]! = cs[i]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper to check if a character should be replaced
def shouldReplace (c : Char) : Bool :=
  c = ' ' ∨ c = ',' ∨ c = '.'

-- Transform a single character according to the rule
def transformChar (c : Char) : Char :=
  if shouldReplace c then ':' else c

-- Postcondition clauses
-- The result has the same length as the input
def ensures1 (s : String) (result : String) : Prop :=
  result.length = s.length

-- Each character is transformed correctly: replaced if space/comma/dot, unchanged otherwise
def ensures2 (s : String) (result : String) : Prop :=
  ∀ i : Nat, i < s.length →
    result.data[i]! = transformChar s.data[i]!

def precondition (s : String) : Prop :=
  True

-- no preconditions

def postcondition (s : String) (result : String) : Prop :=
  ensures1 s result ∧
  ensures2 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.replaceWithColon_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are trivially true, the equivalence holds.
  simp [VerinaSpec.replaceWithColon_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) (h_precond : VerinaSpec.replaceWithColon_precond s):
  VerinaSpec.replaceWithColon_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  unfold VerinaSpec.replaceWithColon_postcond LeetProofSpec.postcondition;
  unfold VerinaSpec.isSpaceCommaDot LeetProofSpec.ensures1 LeetProofSpec.ensures2;
  unfold LeetProofSpec.transformChar;
  unfold LeetProofSpec.shouldReplace; aesop;