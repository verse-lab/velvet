/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6bf0dcc8-209b-422b-9812-5a4803cfa602

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int):
  VerinaSpec.secondSmallest_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : Array Int) (result : Int) (h_precond : VerinaSpec.secondSmallest_precond s):
  VerinaSpec.secondSmallest_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def secondSmallest_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!

-- at least two distinct values
  -- !benchmark @end precond

def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i

def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  -- !benchmark @start postcond
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if array has at least two distinct values
def hasAtLeastTwoDistinct (arr : Array Int) : Prop :=
  ∃ i j, i < arr.size ∧ j < arr.size ∧ arr[i]! ≠ arr[j]!

-- Find the minimum element in an array (for specification purposes)
def isMinimum (arr : Array Int) (m : Int) : Prop :=
  (∃ i, i < arr.size ∧ arr[i]! = m) ∧
  (∀ j, j < arr.size → arr[j]! ≥ m)

-- Check if a value is in the array
def inArray (arr : Array Int) (val : Int) : Prop :=
  ∃ i, i < arr.size ∧ arr[i]! = val

-- Precondition clauses
def require1 (s : Array Int) :=
  s.size ≥ 2

-- Array has at least two elements

def require2 (s : Array Int) :=
  hasAtLeastTwoDistinct s

-- Array has at least two distinct values

-- Postcondition clauses
-- The result is an element of the array
def ensures1 (s : Array Int) (result : Int) :=
  inArray s result

-- The result is strictly greater than the minimum
def ensures2 (s : Array Int) (result : Int) :=
  ∀ m, isMinimum s m → result > m

-- No element in the array is strictly between the minimum and the result
def ensures3 (s : Array Int) (result : Int) :=
  ∀ m, isMinimum s m →
    ∀ i, i < s.size → (s[i]! > m → s[i]! ≥ result)

def precondition (s : Array Int) :=
  require1 s ∧ require2 s

def postcondition (s : Array Int) (result : Int) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : Array Int):
  VerinaSpec.secondSmallest_precond s ↔ LeetProofSpec.precondition s := by
  bound

theorem postcondition_equiv (s : Array Int) (result : Int) (h_precond : VerinaSpec.secondSmallest_precond s):
  VerinaSpec.secondSmallest_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  constructor;
  · rintro ⟨ ⟨ i, hi, hi' ⟩, ⟨ j, hj, hj', hj'' ⟩ ⟩;
    constructor;
    · exact ⟨ i, hi, hi' ⟩;
    · constructor;
      · intro m hm;
        unfold LeetProofSpec.isMinimum at hm;
        grind;
      · -- To prove the third part of the postcondition, we need to show that for any minimum m, there's no element between m and result.
        intro m hm
        obtain ⟨k, hk⟩ : ∃ k, k < s.size ∧ s[k]! = m := by
          exact hm.1;
        grind;
  · -- Let's choose any $m$ that is the minimum element of the array.
    intro h
    obtain ⟨i, hi⟩ : ∃ i < s.size, s[i]! = result := h.left
    obtain ⟨m, hm⟩ : ∃ m, (∃ i < s.size, s[i]! = m) ∧ (∀ j < s.size, s[j]! ≥ m) := by
      have h_min : ∃ m ∈ Finset.image (fun i => s[i]!) (Finset.range s.size), ∀ n ∈ Finset.image (fun i => s[i]!) (Finset.range s.size), m ≤ n := by
        exact ⟨ Finset.min' ( Finset.image ( fun i => s[i]! ) ( Finset.range s.size ) ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr hi.1 ) ⟩, Finset.min'_mem _ _, fun n hn => Finset.min'_le _ _ hn ⟩;
      aesop;
    exact ⟨ ⟨ i, hi.1, hi.2 ⟩, by obtain ⟨ j, hj₁, hj₂ ⟩ := hm.1; exact ⟨ j, hj₁, by linarith [ h.2.1 m hm ], fun k hk₁ hk₂ => by linarith [ h.2.2 m hm k hk₁ ( lt_of_le_of_ne ( hm.2 k hk₁ ) ( Ne.symm <| by aesop ) ) ] ⟩ ⟩