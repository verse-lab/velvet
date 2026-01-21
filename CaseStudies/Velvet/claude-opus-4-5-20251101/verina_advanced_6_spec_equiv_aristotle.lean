/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b085ce0c-3488-4e4d-8feb-06045d162885

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allVowels_precond s):
  VerinaSpec.allVowels_postcond s result h_precond ↔ LeetProofSpec.postcondition s result

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

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4de97130-3c29-4be5-9295-d1f1c7c290a7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.allVowels_precond s ↔ LeetProofSpec.precondition s
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower

@[reducible]
def allVowels_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Define the set of vowels as lowercase characters
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']

-- Precondition: no restrictions on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff all 5 vowels appear in the string (case-insensitive)
-- Using property-based specification with List.all and membership
def postcondition (s : String) (result : Bool) : Prop :=
  result = (vowels.all (fun v => v ∈ s.toLower.toList))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.allVowels_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are true, the equivalence holds trivially.
  simp [VerinaSpec.allVowels_precond, LeetProofSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Aristotle failed to find a proof.
-/
theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allVowels_precond s):
  VerinaSpec.allVowels_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  have hfeq :
    ∀ str : String,
    ∀ v : Char,
      let chars := VerinaSpec.normalize_str str
      (chars.contains v = true) ↔ (v ∈ s.toLower.toList) := by
    intro str v
    simp [VerinaSpec.normalize_str]
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    -- Let's choose the string `s = "bcdfg"` and the result `false`.
    use "bcdfg", false;
    -- Show that the precondition holds for `s = "bcdfg"`.
    simp [VerinaSpec.allVowels_precond];
    -- Let's choose the string `str = "a"` and the character `v = 'a'`.
    use "a", 'a';
    native_decide
  simp [VerinaSpec.allVowels_postcond, LeetProofSpec.postcondition]
  apply Iff.intro
  · intro hresult
    simp [LeetProofSpec.vowels]
    grind
  · intro hresult
    simp [LeetProofSpec.vowels] at hresult
    grind

-/
/- Aristotle failed to find a proof. -/
theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allVowels_precond s):
  VerinaSpec.allVowels_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  have hfeq :
    ∀ str : String,
    ∀ v : Char,
      let chars := VerinaSpec.normalize_str str
      (chars.contains v = true) ↔ (v ∈ s.toLower.toList) := by
    intro str v
    simp [VerinaSpec.normalize_str]
    sorry
  simp [VerinaSpec.allVowels_postcond, LeetProofSpec.postcondition]
  apply Iff.intro
  · intro hresult
    simp [LeetProofSpec.vowels]
    grind
  · intro hresult
    simp [LeetProofSpec.vowels] at hresult
    grind