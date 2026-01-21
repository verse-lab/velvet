/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f4dd24ef-3c12-4ddc-89d9-082b53a0746e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int):
  VerinaSpec.mostFrequent_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Int) (h_precond : VerinaSpec.mostFrequent_precond xs):
  VerinaSpec.mostFrequent_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result
-/

import Lean
import Mathlib.Tactic
import Std.Data.HashMap


open Std

namespace VerinaSpec

@[reducible]
def mostFrequent_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  xs ≠ []

-- !benchmark @end precond

-- Build a frequency map from the list
def countMap (xs : List Int) : HashMap Int Nat :=
  let step := fun m x =>
    let current := m.getD x 0
    m.insert x (current + 1)
  let init := (HashMap.empty : HashMap Int Nat)
  xs.foldl step init

-- Compute the maximum frequency in the map
def getMaxFrequency (m : HashMap Int Nat) : Nat :=
  let step := fun acc (_k, v) =>
    if v > acc then v else acc
  let init := 0
  m.toList.foldl step init

-- Extract all keys whose frequency == maxFreq
def getCandidates (m : HashMap Int Nat) (maxFreq : Nat) : List Int :=
  let isTarget := fun (_k, v) => v = maxFreq
  let extract := fun (k, _) => k
  m.toList.filter isTarget |>.map extract

-- Return the first candidate element from original list
def getFirstWithFreq (xs : List Int) (candidates : List Int) : Int :=
  match xs.find? (fun x => candidates.contains x) with
  | some x => x
  | none => 0

@[reducible]
def mostFrequent_postcond (xs : List Int) (result: Int) (h_precond : mostFrequent_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  let count := fun x => xs.countP (fun y => y = x)
  result ∈ xs ∧
  xs.all (fun x => count x ≤ count result) ∧
  ((xs.filter (fun x => count x = count result)).head? = some result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Count occurrences of an element in a list
def countFreq (x : Int) (xs : List Int) : Nat :=
  xs.count x

-- Check if an element has the maximum frequency in the list
def hasMaxFrequency (x : Int) (xs : List Int) : Prop :=
  ∀ y ∈ xs, countFreq y xs ≤ countFreq x xs

-- Find the index of the first occurrence of an element
def firstOccurrenceIdx (x : Int) (xs : List Int) : Nat :=
  match xs.findIdx? (· == x) with
  | some idx => idx
  | none => xs.length

-- Check if x appears before y in the list (by first occurrence)
def appearsBeforeOrEqual (x : Int) (y : Int) (xs : List Int) : Prop :=
  firstOccurrenceIdx x xs ≤ firstOccurrenceIdx y xs

-- Precondition: list must be non-empty
def precondition (xs : List Int) :=
  xs ≠ []

-- Postcondition clauses
-- 1. Result must be an element of the list
def ensures1 (xs : List Int) (result : Int) :=
  result ∈ xs

-- 2. Result has the maximum frequency
def ensures2 (xs : List Int) (result : Int) :=
  hasMaxFrequency result xs

-- 3. Among all elements with max frequency, result appears first
def ensures3 (xs : List Int) (result : Int) :=
  ∀ y ∈ xs, countFreq y xs = countFreq result xs → appearsBeforeOrEqual result y xs

def postcondition (xs : List Int) (result : Int) :=
  ensures1 xs result ∧ ensures2 xs result ∧ ensures3 xs result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int):
  VerinaSpec.mostFrequent_precond xs ↔ LeetProofSpec.precondition xs := by
  rfl

noncomputable section AristotleLemmas

/-
Checking definitions of count and countP
-/
#check List.count
#check List.countP

/-
Checking definition of List.count
-/
#print List.count

/-
The count of elements equal to `x` (using propositional equality) is the same as `countFreq` (using boolean equality).
-/
open LeetProofSpec

lemma LeetProofSpec.countP_eq_countFreq (xs : List Int) (x : Int) :
  xs.countP (fun y => y = x) = countFreq x xs := by
    exact?

/-
Checking definitions of find? and filter
-/
#print List.find?
#print List.filter

/-
The head of the filtered list is equal to the result of `find?`.
-/
open LeetProofSpec

lemma LeetProofSpec.head?_filter_eq_find? (xs : List Int) (P : Int → Bool) :
  (xs.filter P).head? = xs.find? P := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.filter, List.find?]
    split
    · simp
    · exact ih

/-
`firstOccurrenceIdx_cons`: The first occurrence index of `y` in `x :: xs` is 0 if `x = y`, else `1 +` index in `xs`.
`find?_eq_some_iff_min_index`: `find?` returns `some r` iff `r` is in the list, satisfies `P`, and has the minimal first occurrence index among all elements satisfying `P`.
-/
open LeetProofSpec

lemma firstOccurrenceIdx_cons (x y : Int) (xs : List Int) :
  firstOccurrenceIdx y (x :: xs) = if x = y then 0 else 1 + firstOccurrenceIdx y xs := by
    unfold LeetProofSpec.firstOccurrenceIdx;
    grind

lemma find?_eq_some_iff_min_index (xs : List Int) (P : Int → Bool) (r : Int) :
  xs.find? P = some r ↔ r ∈ xs ∧ P r ∧ ∀ y ∈ xs, P y → firstOccurrenceIdx r xs ≤ firstOccurrenceIdx y xs := by
    revert xs;
    -- We'll use induction on the list `xs`.
    intro xs
    induction' xs with x xs ih;
    · aesop;
    · by_cases hx : P x <;> simp_all +decide [ List.find?_cons ];
      · unfold LeetProofSpec.firstOccurrenceIdx; simp +decide [ hx ] ;
        cases eq_or_ne x r <;> simp_all +decide [ List.findIdx?_cons ];
        cases h : List.findIdx? ( fun x => x == r ) xs <;> aesop;
      · by_cases hr : r = x <;> simp_all +decide [ LeetProofSpec.firstOccurrenceIdx ];
        simp_all +decide [ List.findIdx?_cons ];
        intro hr₁ hr₂; constructor <;> intro h <;> intro y hy₁ hy₂ <;> specialize h y hy₁ hy₂ <;> split_ifs at * <;> simp_all +decide ;
        · cases h' : List.findIdx? ( fun x => x == r ) xs <;> cases h'' : List.findIdx? ( fun x => x == y ) xs <;> simp_all +decide;
        · cases h' : List.findIdx? ( fun x => x == r ) xs <;> cases h'' : List.findIdx? ( fun x => x == y ) xs <;> simp_all +decide

end AristotleLemmas

theorem postcondition_equiv (xs : List Int) (result : Int) (h_precond : VerinaSpec.mostFrequent_precond xs):
  VerinaSpec.mostFrequent_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  unfold VerinaSpec.mostFrequent_postcond LeetProofSpec.postcondition LeetProofSpec.ensures1 LeetProofSpec.ensures2 LeetProofSpec.ensures3;
  simp +zetaDelta at *;
  intro h; rw [ find?_eq_some_iff_min_index ] ; aesop;