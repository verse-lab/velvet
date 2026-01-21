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
    toLowercase: Convert all uppercase characters in a string to their lowercase equivalents.
    Natural language breakdown:
    1. Input is any string s (no preconditions).
    2. Output is a string result with the same length as s.
    3. For every character position i in s, the output character at i equals Char.toLower applied to the input character at i.
    4. Characters not affected by Char.toLower remain unchanged.
-/

section Specs
-- Helper: Pointwise character relation between two strings via their underlying Char lists.
-- This characterizes the output uniquely without referring to String.toLower.
-- Note: Char.toLower converts uppercase ASCII letters 'A'..'Z' to lowercase and leaves other chars unchanged.
def charsLoweredPointwise (s : String) (t : String) : Prop :=
  let sl := s.toList
  let tl := t.toList
  tl.length = sl.length ∧
    ∀ (i : Nat), i < sl.length → tl[i]! = Char.toLower (sl[i]!)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  charsLoweredPointwise s result
end Specs

section Impl
method toLowercase (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  let sl := s.toList
  let mut tl : List Char := []
  let mut i : Nat := 0
  while i < sl.length
    -- i stays within bounds of the source list
    -- init: i=0; step: i:=i+1; exit: i=sl.length
    invariant "inv_bounds" i ≤ sl.length
    -- tl is exactly the lowered prefix of sl of length i
    -- init: tl=[] and i=0; step: append lowered sl[i]!
    invariant "inv_tl_length" tl.length = i
    invariant "inv_tl_pointwise" (∀ j : Nat, j < i → tl[j]! = Char.toLower (sl[j]!))
    done_with i = sl.length
  do
    let c := sl[i]!
    tl := tl ++ [Char.toLower c]
    i := i + 1
  let resStr := String.mk tl
  return resStr
end Impl

section TestCases
-- Test case 1: provided example with punctuation and mixed case
-- "Hello, World!" → "hello, world!"
def test1_s : String := "Hello, World!"
def test1_Expected : String := "hello, world!"

-- Test case 2: all uppercase

def test2_s : String := "ABC"
def test2_Expected : String := "abc"

-- Test case 3: already lowercase

def test3_s : String := "abc"
def test3_Expected : String := "abc"

-- Test case 4: empty string

def test4_s : String := ""
def test4_Expected : String := ""

-- Test case 5: digits and symbols only

def test5_s : String := "1234!@"
def test5_Expected : String := "1234!@"

-- Test case 6: mixed case with digits

def test6_s : String := "MixedCASE123"
def test6_Expected : String := "mixedcase123"

-- Test case 7: single uppercase character

def test7_s : String := "Z"
def test7_Expected : String := "z"

-- Test case 8: whitespace and newline preserved

def test8_s : String := "A a\nB"
def test8_Expected : String := "a a\nb"

-- Test case 9: non-ASCII letter (Char.toLower leaves it unchanged)

def test9_s : String := "É"
def test9_Expected : String := "É"

-- Recommend to validate: test1, test4, test6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((toLowercase test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((toLowercase test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((toLowercase test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((toLowercase test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((toLowercase test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((toLowercase test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((toLowercase test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((toLowercase test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((toLowercase test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for toLowercase
prove_precondition_decidable_for toLowercase
prove_postcondition_decidable_for toLowercase
derive_tester_for toLowercase
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := toLowercaseTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct toLowercase by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (require_1 : precondition s)
    (i : ℕ)
    (tl : List Char)
    (invariant_inv_bounds : i ≤ s.data.length)
    (invariant_inv_tl_length : tl.length = i)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (tl_1 : List Char)
    (invariant_inv_tl_pointwise : ∀ j < i, tl[j]?.getD 'A' = (s.data[j]?.getD 'A').toLower)
    (i_2 : i = i_1 ∧ tl = tl_1)
    : postcondition s { data := tl_1 } := by
  unfold postcondition
  unfold charsLoweredPointwise
  -- toList reduces to data
  simp [String.toList]
  constructor
  · rcases i_2 with ⟨hi, htl⟩
    calc
      tl_1.length = tl.length := by simpa [htl]
      _ = i := invariant_inv_tl_length
      _ = s.data.length := done_1
  · intro k hk
    rcases i_2 with ⟨hi, htl⟩
    have hk' : k < i := by simpa [done_1] using hk
    have hInv :
        tl[k]?.getD 'A' = (s.data[k]?.getD 'A').toLower :=
      invariant_inv_tl_pointwise k hk'
    -- rewrite tl to tl_1 in the invariant and finish
    simpa [htl] using hInv


prove_correct toLowercase by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1 i tl invariant_inv_bounds invariant_inv_tl_length done_1 i_1 tl_1 invariant_inv_tl_pointwise i_2)
end Proof
