/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5355810c-7599-4199-981a-0e599964a223

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.runLengthEncode_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : List (Char × Nat)) (h_precond : VerinaSpec.runLengthEncode_precond s):
  VerinaSpec.runLengthEncode_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def runLengthEncode_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail

def runLengthEncode_postcond (s : String) (result: List (Char × Nat)) (h_precond : runLengthEncode_precond (s)) : Prop :=
  -- !benchmark @start postcond
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to decode a run-length encoded list back to a list of characters
def decode (encoded : List (Char × Nat)) : List Char :=
  encoded.flatMap (fun p => List.replicate p.2 p.1)

-- Check that all run lengths are positive (no zero counts)
def allPositiveCounts (encoded : List (Char × Nat)) : Prop :=
  ∀ p ∈ encoded, p.2 > 0

-- Check that no two consecutive pairs have the same character
def noConsecutiveSameChar (encoded : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i + 1 < encoded.length → (encoded[i]!).1 ≠ (encoded[i + 1]!).1

-- Postcondition clause 1: All counts are positive
def ensures1 (s : String) (result : List (Char × Nat)) :=
  allPositiveCounts result

-- Postcondition clause 2: No consecutive pairs have the same character
def ensures2 (s : String) (result : List (Char × Nat)) :=
  noConsecutiveSameChar result

-- Postcondition clause 3: Decoding returns the original string
def ensures3 (s : String) (result : List (Char × Nat)) :=
  decode result = s.toList

def precondition (s : String) :=
  True

-- no preconditions

def postcondition (s : String) (result : List (Char × Nat)) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.runLengthEncode_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.runLengthEncode_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : List (Char × Nat)) (h_precond : VerinaSpec.runLengthEncode_precond s):
  VerinaSpec.runLengthEncode_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  unfold VerinaSpec.runLengthEncode_postcond LeetProofSpec.postcondition;
  -- Show that the decodeRLE function and the decode function are equivalent.
  have h_decode_equiv : ∀ lst : List (Char × Nat), VerinaSpec.decodeRLE lst = String.mk (LeetProofSpec.decode lst) := by
    intro lst
    induction' lst with p lst ih;
    · rfl;
    · -- By definition of `decodeRLE`, we have `decodeRLE (p :: lst) = (String.mk (List.replicate p.snd p.fst)) ++ decodeRLE lst`.
      have h_decodeRLE_def : VerinaSpec.decodeRLE (p :: lst) = (String.mk (List.replicate p.snd p.fst)) ++ VerinaSpec.decodeRLE lst := by
        rfl;
      unfold LeetProofSpec.decode; aesop;
  simp_all +decide [ LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3 ];
  simp +decide [ LeetProofSpec.allPositiveCounts, LeetProofSpec.noConsecutiveSameChar, String.ext_iff ];
  exact fun _ _ => ⟨ fun h i hi => h i ( Nat.lt_pred_iff.mpr hi ), fun h i hi => h i ( Nat.lt_pred_iff.mp hi ) ⟩