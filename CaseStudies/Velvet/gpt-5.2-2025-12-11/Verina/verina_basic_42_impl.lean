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
    countDigits: Count the number of ASCII digit characters ('0'..'9') in a string.
    Natural language breakdown:
    1. Input is a string s.
    2. Consider the characters of s in order.
    3. A character is a digit iff Char.isDigit returns true (equivalently '0'..'9').
    4. The output is the number of characters in s that are digits.
    5. There are no preconditions; the function must work for any string.
-/

section Specs
-- Helper: digit predicate (use the standard library definition)
def isDigitChar (c : Char) : Bool :=
  c.isDigit

-- Helper: count digit characters in a string via List.countP over s.toList.
-- Note: This is a mathematical characterization of the intended result.
def digitCount (s : String) : Nat :=
  (s.toList.countP (fun c => isDigitChar c))

-- No preconditions

def precondition (s : String) : Prop :=
  True

-- Postcondition: result equals the number of digit characters in s.
-- This uniquely determines the output.
def postcondition (s : String) (result : Nat) : Prop :=
  result = digitCount s
end Specs

section Impl
method countDigits (s: String)
  return (result: Nat)
  require precondition s
  ensures postcondition s result
  do
  let chars := s.toList
  let mut l := chars
  let mut cnt : Nat := 0
  while True
    -- l is always a suffix of the original character list `chars`
    -- Initialization: l = chars = [] ++ chars
    -- Preservation: if l = c::tl then tl is suffix as ( [c]++pref) ++ tl = chars
    invariant "inv_suffix" ∃ pref : List Char, chars = pref ++ l
    -- cnt equals the number of digit characters already consumed from the front of `chars`
    -- Let pref be the processed prefix with chars = pref ++ l
    -- Initialization: pref = [], cnt = 0
    -- Preservation: consuming c updates both pref and cnt consistently
    invariant "inv_cnt" ∃ pref : List Char, chars = pref ++ l ∧ cnt = pref.countP (fun c => isDigitChar c)
    done_with (l = [])
  do
    match l with
    | [] =>
      break
    | c :: tl =>
      if isDigitChar c then
        cnt := cnt + 1
      l := tl
  return cnt
end Impl

section TestCases
-- Test case 1: mixed digits and letters (given example)
def test1_s : String := "123abc456"
def test1_Expected : Nat := 6

-- Test case 2: no digits
def test2_s : String := "no digits here!"
def test2_Expected : Nat := 0

-- Test case 3: all digits
def test3_s : String := "1234567890"
def test3_Expected : Nat := 10

-- Test case 4: empty string
def test4_s : String := ""
def test4_Expected : Nat := 0

-- Test case 5: alternating letters and digits
def test5_s : String := "a1b2c3"
def test5_Expected : Nat := 3

-- Test case 6: single digit zero
def test6_s : String := "0"
def test6_Expected : Nat := 1

-- Test case 7: only letters
def test7_s : String := "abc"
def test7_Expected : Nat := 0

-- Test case 8: punctuation and spaces with digits
def test8_s : String := " 9!x-0?"
def test8_Expected : Nat := 2

-- Test case 9: newline and tab around digits
def test9_s : String := "\n7\t"
def test9_Expected : Nat := 1

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((countDigits test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((countDigits test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((countDigits test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((countDigits test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((countDigits test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((countDigits test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((countDigits test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((countDigits test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((countDigits test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for countDigits
prove_precondition_decidable_for countDigits
prove_postcondition_decidable_for countDigits
derive_tester_for countDigits
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := countDigitsTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct countDigits by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (require_1 : precondition s)
    (cnt : ℕ)
    (l : List Char)
    (invariant_inv_suffix : ∃ pref, s.data = pref ++ l)
    (invariant_inv_cnt : ∃ pref, s.data = pref ++ l ∧ cnt = List.countP (fun c ↦ isDigitChar c) pref)
    (i : Char)
    (i_1 : List Char)
    (i_2 : l = i :: i_1)
    (if_pos : isDigitChar i = true)
    : ∃ pref, s.data = pref ++ i_1 := by
    rcases invariant_inv_suffix with ⟨pref0, hs⟩
    refine ⟨pref0 ++ [i], ?_⟩
    calc
      s.data = pref0 ++ l := hs
      _ = pref0 ++ (i :: i_1) := by simp [i_2]
      _ = (pref0 ++ [i]) ++ i_1 := by
            simpa [List.append_assoc] using (List.append_cons pref0 i i_1).symm

theorem goal_1
    (s : String)
    (require_1 : precondition s)
    (cnt : ℕ)
    (l : List Char)
    (invariant_inv_suffix : ∃ pref, s.data = pref ++ l)
    (invariant_inv_cnt : ∃ pref, s.data = pref ++ l ∧ cnt = List.countP (fun c ↦ isDigitChar c) pref)
    (i : Char)
    (i_1 : List Char)
    (i_2 : l = i :: i_1)
    (if_pos : isDigitChar i = true)
    : ∃ pref, s.data = pref ++ i_1 ∧ cnt + 1 = List.countP (fun c ↦ isDigitChar c) pref := by
  rcases invariant_inv_cnt with ⟨pref, hs, hcnt⟩
  refine ⟨pref ++ [i], ?_, ?_⟩
  · -- show: s.data = (pref ++ [i]) ++ i_1
    have hs' : s.data = pref ++ (i :: i_1) := by
      simpa [i_2] using hs
    -- use append_cons: pref ++ (i :: i_1) = pref ++ [i] ++ i_1, then reassociate
    calc
      s.data = pref ++ (i :: i_1) := hs'
      _ = pref ++ [i] ++ i_1 := by simpa using (List.append_cons pref i i_1).symm
      _ = (pref ++ [i]) ++ i_1 := by simp [List.append_assoc]
  · -- show: cnt + 1 = countP ... (pref ++ [i])
    -- First rewrite countP on the extended prefix using append and singleton
    have hcount :
        List.countP (fun c ↦ isDigitChar c) (pref ++ [i])
          = List.countP (fun c ↦ isDigitChar c) pref + 1 := by
      -- countP_append + countP_singleton + if_pos
      simpa [List.countP_append, List.countP_singleton, if_pos, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using (rfl :
        List.countP (fun c ↦ isDigitChar c) (pref ++ [i])
          = List.countP (fun c ↦ isDigitChar c) pref +
              List.countP (fun c ↦ isDigitChar c) [i])
    -- Now use cnt = countP ... pref
    calc
      cnt + 1
          = List.countP (fun c ↦ isDigitChar c) pref + 1 := by simpa [hcnt]
      _ = List.countP (fun c ↦ isDigitChar c) (pref ++ [i]) := by
            simpa [hcount]

theorem goal_2
    (s : String)
    (require_1 : precondition s)
    (cnt : ℕ)
    (l : List Char)
    (invariant_inv_suffix : ∃ pref, s.data = pref ++ l)
    (invariant_inv_cnt : ∃ pref, s.data = pref ++ l ∧ cnt = List.countP (fun c ↦ isDigitChar c) pref)
    (i : Char)
    (i_1 : List Char)
    (i_2 : l = i :: i_1)
    (if_neg : isDigitChar i = false)
    : ∃ pref, s.data = pref ++ i_1 := by
    rcases invariant_inv_suffix with ⟨pref0, hs⟩
    refine ⟨pref0 ++ [i], ?_⟩
    -- Move one element from the suffix to the prefix
    calc
      s.data = pref0 ++ l := hs
      _ = pref0 ++ (i :: i_1) := by simpa [i_2]
      _ = pref0 ++ [i] ++ i_1 := by simpa using (List.append_cons pref0 i i_1)
      _ = (pref0 ++ [i]) ++ i_1 := by simp [List.append_assoc]

theorem goal_3
    (s : String)
    (require_1 : precondition s)
    (cnt : ℕ)
    (l : List Char)
    (invariant_inv_suffix : ∃ pref, s.data = pref ++ l)
    (invariant_inv_cnt : ∃ pref, s.data = pref ++ l ∧ cnt = List.countP (fun c ↦ isDigitChar c) pref)
    (i : Char)
    (i_1 : List Char)
    (i_2 : l = i :: i_1)
    (if_neg : isDigitChar i = false)
    : ∃ pref, s.data = pref ++ i_1 ∧ cnt = List.countP (fun c ↦ isDigitChar c) pref := by
  rcases invariant_inv_cnt with ⟨pref, hs, hcnt⟩
  refine ⟨pref ++ [i], ?_, ?_⟩
  · -- update suffix decomposition
    -- hs : s.data = pref ++ l, and l = i :: i_1
    calc
      s.data = pref ++ l := hs
      _ = pref ++ (i :: i_1) := by simpa [i_2]
      _ = pref ++ [i] ++ i_1 := by simpa using (List.append_cons pref i i_1)
      _ = (pref ++ [i]) ++ i_1 := by
        simpa [List.append_assoc]
  · -- update count: i is not a digit, so count doesn't change
    -- want: cnt = countP _ (pref ++ [i])
    -- use old hcnt : cnt = countP _ pref, and show countP _ (pref ++ [i]) = countP _ pref
    have hcount :
        List.countP (fun c ↦ isDigitChar c) (pref ++ [i]) =
          List.countP (fun c ↦ isDigitChar c) pref := by
      -- countP over append and singleton
      simp [List.countP_append, List.countP_singleton, if_neg, Nat.add_zero]
    -- now rewrite using hcnt
    calc
      cnt = List.countP (fun c ↦ isDigitChar c) pref := hcnt
      _ = List.countP (fun c ↦ isDigitChar c) (pref ++ [i]) := by
        symm
        exact hcount

theorem goal_4
    (s : String)
    (require_1 : precondition s)
    : ∃ pref, s.toList = pref ++ s.toList := by
    refine ⟨([] : List Char), ?_⟩
    simp

theorem goal_5
    (s : String)
    (require_1 : precondition s)
    : ∃ pref, s.toList = pref ++ s.toList ∧ 0 = List.countP (fun c ↦ isDigitChar c) pref := by
    refine ⟨([] : List Char), ?_, ?_⟩
    · simp
    · simp

theorem goal_6
    (s : String)
    (require_1 : precondition s)
    (cnt : ℕ)
    (l : List Char)
    (invariant_inv_suffix : ∃ pref, s.data = pref ++ l)
    (invariant_inv_cnt : ∃ pref, s.data = pref ++ l ∧ cnt = List.countP (fun c ↦ isDigitChar c) pref)
    (done_1 : l = [])
    (i : ℕ)
    (l_1 : List Char)
    (i_1 : cnt = i ∧ l = l_1)
    : postcondition s i := by
  unfold postcondition digitCount
  -- Reduce goal to a statement about `List.countP` on `s.data`
  have hcnti : cnt = i := i_1.1
  rcases invariant_inv_cnt with ⟨pref, hs, hcnt⟩
  have hs' : s.data = pref := by
    -- from `s.data = pref ++ l` and `l = []` get `s.data = pref`
    simpa [done_1] using hs
  -- rewrite `cnt` via the invariant and identify `pref` with `s.data`
  have hcnt_data : cnt = List.countP (fun c ↦ isDigitChar c) s.data := by
    -- from hcnt: cnt = countP _ pref, and hs': s.data = pref
    simpa [hs'] using hcnt
  -- now substitute `i` for `cnt` using hcnti
  have : i = List.countP (fun c ↦ isDigitChar c) s.data := by
    -- hcnti : cnt = i, so rewrite cnt -> i in hcnt_data
    simpa [hcnti] using hcnt_data
  simpa using this


prove_correct countDigits by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1 cnt l invariant_inv_suffix invariant_inv_cnt i i_1 i_2 if_pos)
  exact (goal_1 s require_1 cnt l invariant_inv_suffix invariant_inv_cnt i i_1 i_2 if_pos)
  exact (goal_2 s require_1 cnt l invariant_inv_suffix invariant_inv_cnt i i_1 i_2 if_neg)
  exact (goal_3 s require_1 cnt l invariant_inv_suffix invariant_inv_cnt i i_1 i_2 if_neg)
  exact (goal_4 s require_1)
  exact (goal_5 s require_1)
  exact (goal_6 s require_1 cnt l invariant_inv_suffix invariant_inv_cnt done_1 i l_1 i_1)
end Proof
