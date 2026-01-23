/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: af272ab7-41c5-443e-a099-3d472cb0f231

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Lean
import Mathlib.Tactic


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  K
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Invalid projection: Type of
  a
is not known; cannot resolve projection `1`
Invalid projection: Type of
  b
is not known; cannot resolve projection `1`-/
namespace VerinaSpec


def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def find? {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) : Option V :=
  m.entries.find? (fun p => p.1 == k) |>.map (·.2)

def update_map_postcond (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (fun a b => a.1 ≤ b.1) result.entries ∧
  m2.entries.all (fun x => find? result x.1 = some x.2) ∧
  m1.entries.all (fun x =>
    match find? m2 x.1 with
    | some _ => true
    | none => find? result x.1 = some x.2
  ) ∧
  result.entries.all (fun x =>
    match find? m1 x.1 with
    | some v => match find? m2 x.1 with
      | some v' => x.2 = v'
      | none => x.2 = v
    | none => find? m2 x.1 = some x.2
  )

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to check if a key exists in a list of pairs
def hasKey (m : List (Int × Int)) (k : Int) : Bool :=
  m.any (fun p => p.1 == k)

-- Helper function to get the value for a key (returns default if not found)
def getValue (m : List (Int × Int)) (k : Int) (default : Int) : Int :=
  match m.find? (fun p => p.1 == k) with
  | some p => p.2
  | none => default

-- Helper to check if a list of pairs is sorted by first element
def isSortedByKey (lst : List (Int × Int)) : Prop :=
  ∀ i : Nat, i + 1 < lst.length → (lst[i]!).1 ≤ (lst[i + 1]!).1

-- Helper to check if keys are unique in a list of pairs
def hasUniqueKeys (lst : List (Int × Int)) : Prop :=
  ∀ i j : Nat, i < lst.length → j < lst.length → i ≠ j → (lst[i]!).1 ≠ (lst[j]!).1

-- Precondition: no specific constraints required
def precondition (m1 : List (Int × Int)) (m2 : List (Int × Int)) :=
  True

-- Postcondition: defines the merge behavior
def postcondition (m1 : List (Int × Int)) (m2 : List (Int × Int)) (result : List (Int × Int)) :=
  -- 1. Every key in result is from m1 or m2
  (∀ k : Int, hasKey result k → hasKey m1 k ∨ hasKey m2 k) ∧
  -- 2. Every key in m1 is in result
  (∀ k : Int, hasKey m1 k → hasKey result k) ∧
  -- 3. Every key in m2 is in result
  (∀ k : Int, hasKey m2 k → hasKey result k) ∧
  -- 4. For keys in m2, result has m2's value
  (∀ k : Int, hasKey m2 k → getValue result k 0 = getValue m2 k 0) ∧
  -- 5. For keys only in m1 (not in m2), result has m1's value
  (∀ k : Int, hasKey m1 k → ¬hasKey m2 k → getValue result k 0 = getValue m1 k 0) ∧
  -- 6. Result is sorted by key
  isSortedByKey result ∧
  -- 7. Result has unique keys
  hasUniqueKeys result

end LeetProofSpec

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `VerinaSpec.update_map_precond`
Unknown identifier `LeetProofSpec.precondition`
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int-/
-- Equivalence theorems

theorem precondition_equiv (m1 : Map Int Int) (m2 : Map Int Int):
  VerinaSpec.update_map_precond m1 m2 ↔ LeetProofSpec.precondition m1 m2 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `VerinaSpec.update_map_precond`
Unknown identifier `VerinaSpec.update_map_postcond`
Unknown identifier `LeetProofSpec.postcondition`
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int
Function expected at
  Map
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Int-/
theorem postcondition_equiv (m1 : Map Int Int) (m2 : Map Int Int) (result : Map Int Int) (h_precond : VerinaSpec.update_map_precond m1 m2):
  VerinaSpec.update_map_postcond m1 m2 result h_precond ↔ LeetProofSpec.postcondition m1 m2 result := by
  sorry
