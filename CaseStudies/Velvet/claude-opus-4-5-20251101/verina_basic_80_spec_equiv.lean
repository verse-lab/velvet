/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 843d4a07-da88-4512-b603-6484efe0ec19

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.only_once_precond a key ↔ LeetProofSpec.precondition a key

- theorem postcondition_equiv (a : Array Int) (key : Int) (result : Bool) (h_precond : VerinaSpec.only_once_precond a key):
  VerinaSpec.only_once_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def only_once_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0

def only_once_postcond (a : Array Int) (key : Int) (result: Bool) (h_precond : only_once_precond (a) (key)) :=
  -- !benchmark @start postcond
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no restrictions on input
def precondition (a : Array Int) (key : Int) :=
  True

-- Postcondition: result is true iff key appears exactly once in array
def postcondition (a : Array Int) (key : Int) (result : Bool) :=
  result = (a.count key == 1)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.only_once_precond a key ↔ LeetProofSpec.precondition a key := by
  tauto

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Bool) (h_precond : VerinaSpec.only_once_precond a key):
  VerinaSpec.only_once_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  -- By definition of `only_once_postcond` and `postcondition`, we can rewrite the goal using the equivalence of the hypotheses.
  simp [VerinaSpec.only_once_postcond, LeetProofSpec.postcondition];
  -- By definition of `count_occurrences`, we know that `count_occurrences a key = a.count key`.
  have h_count : VerinaSpec.count_occurrences a key = a.count key := by
    -- By definition of `count_occurrences`, we can rewrite it using the foldl operation.
    simp [VerinaSpec.count_occurrences];
    -- By induction on the array, we can show that the foldl operation counts the occurrences of the key correctly.
    induction' a with a ih;
    induction a using List.reverseRecOn <;> aesop;
  grind