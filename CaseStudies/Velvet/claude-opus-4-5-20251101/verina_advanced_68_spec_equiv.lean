/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e50367e4-99ab-4086-ac5c-5514cd7e8967

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem postcondition_equiv (input : String) (result : String) (h_precond : VerinaSpec.runLengthEncoder_precond input):
  VerinaSpec.runLengthEncoder_postcond input result h_precond ↔ LeetProofSpec.postcondition input result

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

@[reducible]
def runLengthEncoder_precond (input : String) : Prop :=
  -- !benchmark @start precond
  input.all (fun c => ¬c.isDigit)

-- no digits allowed in input (ambiguous encoding)
  -- !benchmark @end precond

@[reducible]
def runLengthEncoder_postcond (input : String) (result: String) (h_precond : runLengthEncoder_precond (input)) : Prop :=
  -- !benchmark @start postcond
  -- Helper functions
  let chars : String → List Char := fun s => s.data

  -- Parse encoded string into (char, count) pairs
  let parseEncodedString : String → List (Char × Nat) :=
    let rec parseState : List Char → Option Char → Option Nat → List (Char × Nat) → List (Char × Nat) :=
      fun remaining currentChar currentCount acc =>
        match remaining with
        | [] =>
          -- Add final pair if we have both char and count
          match currentChar, currentCount with
          | some c, some n => (c, n) :: acc
          | _, _ => acc
        | c :: cs =>
          if c.isDigit then
            match currentChar with
            | none => [] -- Invalid format: digit without preceding character
            | some ch =>
              -- Update current count
              let digit := c.toNat - 48
              let newCount :=
                match currentCount with
                | none => digit
                | some n => n * 10 + digit
              parseState cs currentChar (some newCount) acc
          else
            -- We found a new character, save previous pair if exists
            let newAcc :=
              match currentChar, currentCount with
              | some ch, some n => (ch, n) :: acc
              | _, _ => acc
            parseState cs (some c) none newAcc

    fun s =>
      let result := parseState (chars s) none none []
      result.reverse

  -- Format check: characters followed by at least one digit
  let formatValid : Bool :=
    let rec checkPairs (chars : List Char) (nowDigit : Bool) : Bool :=
      match chars with
      | [] => true
      | c :: cs =>
        if nowDigit && c.isDigit then
          checkPairs cs true
        else
        -- Need at least one digit after character
          match cs with
          | [] => false -- Ending with character, no digits
          | d :: ds =>
            if d.isDigit then
              checkPairs ds true
            else
              false -- No digit after character

    checkPairs (chars result) false

  -- Content validation
  let contentValid : Bool :=
    let pairs := parseEncodedString result
    let expanded := pairs.flatMap (fun (c, n) => List.replicate n c)
    expanded == chars input

  -- Empty check
  let nonEmptyValid : Bool :=
    input.isEmpty = result.isEmpty

  formatValid && contentValid && nonEmptyValid

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if a character is a digit
def isDigitChar (c : Char) : Bool := c.isDigit

-- Check if input contains no digit characters (precondition)
def noDigitsInString (s : String) : Prop :=
  ∀ c, c ∈ s.toList → ¬isDigitChar c

-- A run is represented as (character, count)
-- Expand a single run into a list of characters
def expandRun (c : Char) (n : Nat) : List Char :=
  List.replicate n c

-- Expand a list of runs into a list of characters
def expandRuns (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => expandRun p.1 p.2)

-- Encode a single run as character followed by its decimal count
def encodeRun (c : Char) (n : Nat) : List Char :=
  c :: (Nat.repr n).toList

-- Encode a list of runs into RLE format
def encodeRuns (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => encodeRun p.1 p.2)

-- Check if runs are valid: each count >= 1
def validRunCounts (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i < runs.length → (runs[i]!).2 ≥ 1

-- Check if runs are maximal: adjacent runs have different characters
def maximalRuns (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i + 1 < runs.length → (runs[i]!).1 ≠ (runs[i+1]!).1

-- Check if runs contain no digit characters
def runsNoDigits (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i < runs.length → ¬isDigitChar (runs[i]!).1

-- Decode a result string back to original: expand each (char, count) pair
-- This is used to verify the round-trip property
def decodeRLE (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => List.replicate p.2 p.1)

-- Property 1: result correctly encodes input using RLE
-- There exists a valid run decomposition such that:
-- 1. The runs expand to the input
-- 2. The runs are maximal (no two adjacent runs have the same character)
-- 3. The result is the encoding of those runs
-- 4. The runs contain no digit characters (consistent with precondition)
def ensures1 (input : String) (result : String) :=
  ∃ (runs : List (Char × Nat)),
    -- Runs expand to input (decoding property)
    expandRuns runs = input.toList ∧
    -- All counts are positive
    validRunCounts runs ∧
    -- Runs are maximal (consecutive runs have different characters)
    maximalRuns runs ∧
    -- Runs contain no digit characters
    runsNoDigits runs ∧
    -- Result is the encoding of these runs
    result.toList = encodeRuns runs

-- Property 2: result is non-empty iff input is non-empty
def ensures2 (input : String) (result : String) :=
  (input.isEmpty ↔ result.isEmpty)

-- Precondition: input contains no digit characters
def precondition (input : String) :=
  noDigitsInString input

-- Combined postcondition
def postcondition (input : String) (result : String) :=
  ensures1 input result ∧ ensures2 input result

end LeetProofSpec

/- Aristotle failed to find a proof. -/
-- Equivalence theorems

theorem precondition_equiv (input : String):
  VerinaSpec.runLengthEncoder_precond input ↔ LeetProofSpec.precondition input := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Helper lemma: The precondition holds for the counterexample input "aa".
-/
open VerinaSpec LeetProofSpec

def bad_input_ex : String := "aa"
def bad_result_ex : String := "a1a1"

lemma precond_holds_ex : runLengthEncoder_precond bad_input_ex := by
  unfold runLengthEncoder_precond
  native_decide

/-
Helper lemma: The Verina postcondition holds for the counterexample "aa" -> "a1a1".
-/
open VerinaSpec LeetProofSpec

lemma verina_holds_ex : runLengthEncoder_postcond bad_input_ex bad_result_ex precond_holds_ex := by
  unfold runLengthEncoder_postcond
  native_decide

/-
Helper lemma: The LeetProofSpec postcondition fails for the counterexample "aa" -> "a1a1" because the runs [('a', 1), ('a', 1)] are not maximal.
-/
open VerinaSpec LeetProofSpec

lemma leet_fails_ex : ¬ postcondition bad_input_ex bad_result_ex := by
  intro h
  have h1 := h.1
  unfold ensures1 at h1
  obtain ⟨runs, h_exp, h_valid, h_max, h_nodig, h_enc⟩ := h1
  -- We show that runs must be [('a', 1), ('a', 1)]
  -- and that this violates h_max.
  rcases runs with ( _ | ⟨ ⟨ c, n ⟩, _ | ⟨ d, m ⟩, _ | ⟨ e, p ⟩ ⟩ ) <;> simp_all! +arith +decide;
  · unfold LeetProofSpec.encodeRuns at h_enc; simp_all +decide [ LeetProofSpec.expandRuns ] ;
    unfold bad_result_ex LeetProofSpec.encodeRun at h_enc; simp_all! +arith +decide;
    rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ Nat.toDigits ];
    cases h_exp;
  · unfold LeetProofSpec.expandRuns at h_exp; simp_all;
    unfold bad_input_ex at h_exp; simp_all! +arith +decide;
    unfold LeetProofSpec.expandRun at h_exp; rcases n with ( _ | _ | n ) <;> rcases ‹Char × ℕ› with ⟨ d, m ⟩ <;> simp_all +arith +decide;
    · exact absurd ( h_valid 0 ( by simp +decide ) ) ( by simp +decide );
    · rcases n : ( ‹Char × ℕ› : Char × ℕ ).2 with ( _ | _ | n ) <;> simp_all +arith +decide;
      · exact absurd ( h_valid 1 ( by simp +arith +decide ) ) ( by simp +arith +decide [ n ] );
      · cases h_max 0 ( by simp +arith +decide ) ( by aesop );
      · grind;
    · replace h_exp := congr_arg List.length h_exp ; simp_all +arith +decide;
      have := h_valid 1; aesop;

end AristotleLemmas

theorem postcondition_equiv (input : String) (result : String) (h_precond : VerinaSpec.runLengthEncoder_precond input):
  VerinaSpec.runLengthEncoder_postcond input result h_precond ↔ LeetProofSpec.postcondition input result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Use the counterexample inputs and results to conclude the proof.
  use bad_input_ex, bad_result_ex, precond_holds_ex
  left
  exact ⟨verina_holds_ex, leet_fails_ex⟩

-/
theorem postcondition_equiv (input : String) (result : String) (h_precond : VerinaSpec.runLengthEncoder_precond input):
  VerinaSpec.runLengthEncoder_postcond input result h_precond ↔ LeetProofSpec.postcondition input result := by
  sorry
