import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findFirstRepeatedChar: identify the first repeated character in a given string.
    Natural language breakdown:
    1. Input is a String s.
    2. Output is Option Char.
    3. Return none iff no character appears at least twice in the string.
    4. Return some c iff there exists a first position j (the earliest second-occurrence position)
       such that the character at position j has already appeared at some earlier i < j, and c is
       exactly that character at position j.
    5. “First repeated character” means: among all indices j where a repeat happens, pick the
       smallest j; the output is the character at that index.
    6. There are no preconditions; the method must work for any string (including empty).
-/

section Specs
-- A repetition at index j means there is an earlier index i < j with the same character.
-- We model strings via their character list representation.

def repeatsAt (l : List Char) (j : Nat) : Prop :=
  j < l.length ∧ ∃ i : Nat, i < j ∧ l[i]! = l[j]!

-- No repetitions strictly before index j.

def noRepeatBefore (l : List Char) (j : Nat) : Prop :=
  ∀ k : Nat, k < j → ¬repeatsAt l k

-- There are no preconditions.

def precondition (s : String) : Prop :=
  True

-- Postcondition:
-- * result = none iff the string has no repeated character anywhere
-- * result = some c iff there exists a minimal index j where a repeat happens, and c = l[j]!

def postcondition (s : String) (result : Option Char) : Prop :=
  let l := s.toList
  (result = none ↔ (∀ j : Nat, ¬repeatsAt l j)) ∧
    (∀ c : Char,
      result = some c ↔
        (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c))
end Specs

section Impl
method findFirstRepeatedChar (s: String) return (result: Option Char)
  require precondition s
  ensures postcondition s result
  do
  let l := s.toList
  let mut j : Nat := 0
  let mut ans : Option Char := none
  let mut found : Bool := false

  while j < l.length ∧ (found = false)
    -- Bounds on j.
    -- Init: j = 0. Preserve: j increases by 1, guard gives j < l.length.
    invariant "ffrc_outer_bounds" j ≤ l.length
    -- Tie control flag to answer: if not found yet, answer must still be none.
    -- Init: ans=none, found=false. Preserve: ans only set when found becomes true.
    invariant "ffrc_outer_ans_none_when_not_found" (found = false → ans = none)
    -- Completeness of the search so far: while still searching, we have ruled out all repeats
    -- at indices strictly before j.
    -- Init: j=0 vacuous. Preserve: if current j is not a repeat, then it extends to j+1.
    invariant "ffrc_outer_noRepeatBefore_j_if_searching" (found = false → noRepeatBefore l j)
    -- If we have found an answer, it is exactly the character at the current index j.
    -- (This is the only point where ans is assigned.)
    invariant "ffrc_outer_found_ans_eq_current" (found = true → ans = some (l[j]!))
    done_with (j = l.length ∨ found = true)
  do
    let mut i : Nat := 0
    let mut rep : Bool := false

    while i < j ∧ (rep = false)
      -- i stays within [0, j].
      invariant "ffrc_inner_bounds" i ≤ j
      -- If rep is still false, no earlier scanned index matches l[j].
      -- This matches repeatsAt l j directly at exit when i=j.
      invariant "ffrc_inner_scannedNoMatch" (rep = false → ∀ k : Nat, k < i → l[k]! ≠ l[j]!)
      -- If rep becomes true, we have found some k < i with l[k]=l[j].
      invariant "ffrc_inner_rep_witness" (rep = true → ∃ k : Nat, k < i ∧ l[k]! = l[j]!)
      done_with (i = j ∨ rep = true)
    do
      if l[i]! = l[j]! then
        rep := true
      else
        pure ()
      i := i + 1

    if rep = true then
      ans := some (l[j]!)
      found := true
    else
      pure ()

    j := j + 1

  return ans
end Impl

section TestCases
-- Test case 1: example given: "abca" -> first repeated is 'a'

def test1_s : String := "abca"
def test1_Expected : Option Char := some 'a'

-- Test case 2: no repeats

def test2_s : String := "abcdef"
def test2_Expected : Option Char := none

-- Test case 3: grouped repeats; earliest second occurrence is for 'a'

def test3_s : String := "aabbcc"
def test3_Expected : Option Char := some 'a'

-- Test case 4: empty string

def test4_s : String := ""
def test4_Expected : Option Char := none

-- Test case 5: first repeated is 'b'

def test5_s : String := "abbc"
def test5_Expected : Option Char := some 'b'

-- Test case 6: case sensitivity, no repeats

def test6_s : String := "Aa"
def test6_Expected : Option Char := none

-- Test case 7: single character

def test7_s : String := "z"
def test7_Expected : Option Char := none

-- Test case 8: repeats with punctuation

def test8_s : String := "!!?"
def test8_Expected : Option Char := some '!'

-- Test case 9: multiple candidates; choose the one whose second appearance is earliest
-- "abcbad": b repeats first (at index 3)

def test9_s : String := "abcbad"
def test9_Expected : Option Char := some 'b'

-- Recommend to validate: test1, test5, test9
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findFirstRepeatedChar test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findFirstRepeatedChar test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findFirstRepeatedChar test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findFirstRepeatedChar test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findFirstRepeatedChar test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findFirstRepeatedChar test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findFirstRepeatedChar test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findFirstRepeatedChar test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((findFirstRepeatedChar test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 184, Column 0
-- Message: unsolved goals
-- case refine_1
-- s : String
-- result : Option Char
-- ⊢ Decidable (result = none ↔ ∀ (j : ℕ), ¬repeatsAt s.toList j)
-- 
-- case refine_2
-- s : String
-- result : Option Char
-- ⊢ Decidable (∀ (c : Char), result = some c ↔ ∃ j, repeatsAt s.toList j ∧ noRepeatBefore s.toList j ∧ s.toList[j]! = c)
-- Line: prove_postcondition_decidable_for findFirstRepeatedChar
-- [ERROR] Line 186, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for findFirstRepeatedChar
-- prove_precondition_decidable_for findFirstRepeatedChar
-- prove_postcondition_decidable_for findFirstRepeatedChar
-- derive_tester_for findFirstRepeatedChar
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (String)
--     let res := findFirstRepeatedCharTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct findFirstRepeatedChar by
  -- loom_solve <;> (try simp at *; expose_names)
end Proof
