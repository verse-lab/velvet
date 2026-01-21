import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    letterCombinations: Generate all possible letter combinations from a string of digits based on telephone keypad mappings
    Natural language breakdown:
    1. Given a string of digits, we need to generate all possible letter combinations
    2. Each digit from 2-9 maps to a set of letters on a telephone keypad:
       - 2: a, b, c
       - 3: d, e, f
       - 4: g, h, i
       - 5: j, k, l
       - 6: m, n, o
       - 7: p, q, r, s
       - 8: t, u, v
       - 9: w, x, y, z
    3. Digits 0, 1, and any non-digit characters have no letter mappings
    4. If the input is empty, return an empty list
    5. If any digit in the input is invalid (not 2-9), return an empty list
    6. The result contains all possible combinations formed by taking one letter from each digit's mapping
    7. The order of combinations follows lexicographic order based on digit position
    8. Each resulting string has length equal to the number of input digits
    9. The total number of combinations is the product of the sizes of each digit's letter set
-/

section Specs
-- Helper Functions

-- Mapping from digit character to list of corresponding letters
def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

-- Check if a digit is valid (maps to letters)
def isValidDigit (c : Char) : Bool :=
  (digitToLetters c).length > 0

-- Check if all digits in the string are valid
def allValidDigits (s : String) : Bool :=
  s.data.all isValidDigit

-- Precondition: no restrictions on input
def precondition (digits : String) :=
  True

-- Postcondition: property-based specification without recursive reference implementation
def postcondition (digits : String) (result : List String) :=
  -- If input is empty, result is empty
  (digits.isEmpty → result = []) ∧
  -- If any digit is invalid, result is empty
  (¬digits.isEmpty → ¬allValidDigits digits → result = []) ∧
  -- If input is non-empty and all digits are valid:
  (¬digits.isEmpty → allValidDigits digits →
    -- Result length equals product of letter counts
    result.length = (digits.data.map (fun c => (digitToLetters c).length)).foldl (· * ·) 1 ∧
    -- Each result string has correct length
    (∀ i : Nat, i < result.length → (result[i]!).length = digits.length) ∧
    -- Each result string is a valid combination (each char comes from correct digit mapping)
    (∀ i : Nat, i < result.length →
      ∀ j : Nat, j < digits.length →
        (result[i]!).data[j]! ∈ digitToLetters (digits.data[j]!)) ∧
    -- No duplicates
    result.Nodup ∧
    -- All valid combinations are covered (every valid combination appears in result)
    (∀ combo : List Char, combo.length = digits.length →
      (∀ j : Nat, j < digits.length → combo[j]! ∈ digitToLetters (digits.data[j]!)) →
      combo.asString ∈ result))
end Specs

section Impl
method letterCombinations (digits : String)
  return (result : List String)
  require precondition digits
  ensures postcondition digits result
  do
  -- Handle empty input
  if digits.isEmpty then
    return []
  else
    -- Check if all digits are valid
    let mut allValid := true
    let mut i := 0
    while i < digits.length
      -- i is bounded by string length
      invariant "i_bounds" 0 ≤ i ∧ i ≤ digits.length
      -- allValid tracks whether all digits checked so far are valid
      invariant "allValid_meaning" allValid = true → (∀ k : Nat, k < i → isValidDigit (digits.data[k]!) = true)
      invariant "allValid_false" allValid = false → (∃ k : Nat, k < i ∧ isValidDigit (digits.data[k]!) = false)
      done_with i >= digits.length
    do
      if ¬isValidDigit (digits.data[i]!) then
        allValid := false
      i := i + 1
    
    -- If any digit is invalid, return empty list
    if ¬allValid then
      return []
    else
      -- Generate all combinations
      -- Start with a list containing one empty string
      let mut combinations : List String := [""]
      let mut idx := 0
      
      while idx < digits.length
        -- idx is bounded
        invariant "idx_bounds" 0 ≤ idx ∧ idx ≤ digits.length
        -- combinations is non-empty when all digits are valid
        invariant "combinations_nonempty" combinations.length > 0
        -- all combinations have length equal to idx (number of digits processed)
        invariant "combo_length" ∀ k : Nat, k < combinations.length → (combinations[k]!).length = idx
        -- each character in each combination comes from the correct digit's letters
        invariant "combo_valid_chars" ∀ k : Nat, k < combinations.length → ∀ j : Nat, j < idx → (combinations[k]!).data[j]! ∈ digitToLetters (digits.data[j]!)
        -- combinations has no duplicates
        invariant "combinations_nodup" combinations.Nodup
        -- combination count equals product of letter counts for processed digits
        invariant "combinations_count" combinations.length = ((digits.data.take idx).map (fun c => (digitToLetters c).length)).foldl (· * ·) 1
        -- all valid combinations for processed digits are in combinations
        invariant "combinations_complete" ∀ combo : List Char, combo.length = idx → (∀ j : Nat, j < idx → combo[j]! ∈ digitToLetters (digits.data[j]!)) → combo.asString ∈ combinations
        done_with idx >= digits.length
      do
        let digit := digits.data[idx]!
        let letters := digitToLetters digit
        
        -- For each existing combination, append each possible letter
        let mut newCombinations : List String := []
        let mut combIdx := 0
        
        while combIdx < combinations.length
          -- combIdx is bounded
          invariant "combIdx_bounds" 0 ≤ combIdx ∧ combIdx ≤ combinations.length
          -- newCombinations length relates to combIdx and letters.length
          invariant "newComb_length" newCombinations.length = combIdx * letters.length
          -- all new combinations have length idx + 1
          invariant "newComb_item_length" ∀ k : Nat, k < newCombinations.length → (newCombinations[k]!).length = idx + 1
          -- characters in new combinations are valid
          invariant "newComb_valid_chars" ∀ k : Nat, k < newCombinations.length → ∀ j : Nat, j < idx + 1 → (newCombinations[k]!).data[j]! ∈ digitToLetters (digits.data[j]!)
          -- newCombinations has no duplicates
          invariant "newComb_nodup" newCombinations.Nodup
          done_with combIdx >= combinations.length
        do
          let combo := combinations[combIdx]!
          let mut letterIdx := 0
          
          while letterIdx < letters.length
            -- letterIdx is bounded
            invariant "letterIdx_bounds" 0 ≤ letterIdx ∧ letterIdx ≤ letters.length
            -- newCombinations length accumulates correctly
            invariant "newComb_inner_length" newCombinations.length = combIdx * letters.length + letterIdx
            -- all new combinations have length idx + 1
            invariant "newComb_inner_item_length" ∀ k : Nat, k < newCombinations.length → (newCombinations[k]!).length = idx + 1
            -- characters in new combinations are valid
            invariant "newComb_inner_valid_chars" ∀ k : Nat, k < newCombinations.length → ∀ j : Nat, j < idx + 1 → (newCombinations[k]!).data[j]! ∈ digitToLetters (digits.data[j]!)
            -- newCombinations has no duplicates
            invariant "newComb_inner_nodup" newCombinations.Nodup
            done_with letterIdx >= letters.length
          do
            let letter := letters[letterIdx]!
            let newCombo := combo.push letter
            newCombinations := newCombinations ++ [newCombo]
            letterIdx := letterIdx + 1
          
          combIdx := combIdx + 1
        
        combinations := newCombinations
        idx := idx + 1
      
      return combinations
end Impl

section TestCases
-- Test case 1: Empty string returns empty list
def test1_digits : String := ""
def test1_Expected : List String := []

-- Test case 2: Single digit '2' returns three letters
def test2_digits : String := "2"
def test2_Expected : List String := ["a", "b", "c"]

-- Test case 3: Single digit '9' returns four letters
def test3_digits : String := "9"
def test3_Expected : List String := ["w", "x", "y", "z"]

-- Test case 4: Two digits "23" returns 9 combinations
def test4_digits : String := "23"
def test4_Expected : List String := ["ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf"]

-- Test case 5: Two digits "27" returns 12 combinations (3 * 4)
def test5_digits : String := "27"
def test5_Expected : List String := ["ap", "aq", "ar", "as", "bp", "bq", "br", "bs", "cp", "cq", "cr", "cs"]

-- Test case 6: Invalid digit '0' returns empty list
def test6_digits : String := "0"
def test6_Expected : List String := []

-- Test case 7: Contains invalid digit '1' returns empty list
def test7_digits : String := "21"
def test7_Expected : List String := []

-- Test case 8: Single digit '7' returns four letters (p, q, r, s)
def test8_digits : String := "7"
def test8_Expected : List String := ["p", "q", "r", "s"]

-- Test case 9: Three digits "234" returns 27 combinations (3 * 3 * 3)
def test9_digits : String := "234"
def test9_Expected : List String := ["adg", "adh", "adi", "aeg", "aeh", "aei", "afg", "afh", "afi", "bdg", "bdh", "bdi", "beg", "beh", "bei", "bfg", "bfh", "bfi", "cdg", "cdh", "cdi", "ceg", "ceh", "cei", "cfg", "cfh", "cfi"]

-- Test case 10: Invalid character '*' returns empty list
def test10_digits : String := "2*3"
def test10_Expected : List String := []

-- Recommend to validate: 1, 2, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((letterCombinations test1_digits).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((letterCombinations test2_digits).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((letterCombinations test3_digits).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((letterCombinations test4_digits).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((letterCombinations test5_digits).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((letterCombinations test6_digits).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((letterCombinations test7_digits).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((letterCombinations test8_digits).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((letterCombinations test9_digits).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((letterCombinations test10_digits).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 239, Column 0
-- Message: unsolved goals
-- case refine_2.refine_2
-- digits : String
-- result : List String
-- ⊢ Decidable
--     (¬digits.isEmpty = true →
--       allValidDigits digits = true →
--         result.length = List.foldl (fun x1 x2 ↦ x1 * x2) 1 (List.map (fun c ↦ (digitToLetters c).length) digits.data) ∧
--           (∀ i < result.length, result[i]!.length = digits.length) ∧
--             (∀ i < result.length, ∀ j < digits.length, result[i]!.data[j]! ∈ digitToLetters digits.data[j]!) ∧
--               result.Nodup ∧
--                 ∀ (combo : List Char),
--                   combo.length = digits.length →
--                     (∀ j < digits.length, combo[j]! ∈ digitToLetters digits.data[j]!) → combo.asString ∈ result)
-- Line: prove_postcondition_decidable_for letterCombinations
-- [ERROR] Line 241, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for letterCombinations
-- prove_precondition_decidable_for letterCombinations
-- prove_postcondition_decidable_for letterCombinations
-- derive_tester_for letterCombinations
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (String)
--     let res := letterCombinationsTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct letterCombinations by
  -- loom_solve <;> (try simp at *; expose_names)


prove_correct letterCombinations by
  loom_solve <;> (try simp at *; expose_names)
end Proof
