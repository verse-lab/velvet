import Lean
import Mathlib.Tactic

namespace VerinaSpec

@[reducible]
def runLengthEncoder_precond (input : String) : Prop :=
  -- !benchmark @start precond
  input.all (fun c => ¬c.isDigit)  -- no digits allowed in input (ambiguous encoding)
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

-- Equivalence theorems

theorem precondition_equiv (input : String):
  VerinaSpec.runLengthEncoder_precond input ↔ LeetProofSpec.precondition input := by
  sorry

theorem postcondition_equiv (input : String) (result : String) (h_precond : VerinaSpec.runLengthEncoder_precond input):
  VerinaSpec.runLengthEncoder_postcond input result h_precond ↔ LeetProofSpec.postcondition input result := by
  sorry
