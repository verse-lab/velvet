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
    allDigits: determine whether every character in a provided string is a digit.
    Natural language breakdown:
    1. Input is a well-formed string `s`.
    2. A character counts as a digit exactly when `Char.isDigit` is true for it (ASCII digits '0'..'9').
    3. The function returns `true` exactly when every character in `s` is a digit.
    4. If `s` is empty, the result is `true` (vacuously, all characters are digits).
    5. If at least one character in `s` is not a digit, the result is `false`.
-/

section Specs
-- Helper: decidable, Bool-based "all characters satisfy Char.isDigit" aggregator
-- Using `List.all` avoids non-decidable quantification over `Char`.
def allDigitsBool (s : String) : Bool :=
  s.toList.all Char.isDigit

-- No preconditions

def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff `Char.isDigit` holds for every character in the string.
-- This formulation is computable and unambiguous.
def postcondition (s : String) (result : Bool) : Prop :=
  result = allDigitsBool s
end Specs

section Impl
method allDigits (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  -- Imperative scan over the character list; empty string yields true.
  let chars := s.toList
  let mut ok := true
  let mut i : Nat := 0
  while i < chars.length ∧ ok
    -- Invariant: index stays within bounds; i starts at 0 and only increases while i < length.
    invariant "inv_bounds" i ≤ chars.length
    -- Invariant: ok exactly tracks whether all characters in the scanned prefix are digits.
    -- Init: i=0, (take 0).all = true and ok=true. Preserve: each step extends prefix by one; if digit then ok stays true,
    -- else ok becomes false and (take (i+1)).all becomes false.
    invariant "inv_ok_eq_prefixAll" ok = (chars.take i).all Char.isDigit
    done_with (i = chars.length ∨ ok = false)
  do
    let c := chars.get! i
    if Char.isDigit c then
      i := i + 1
    else
      ok := false
      i := i + 1
  return ok
end Impl

section TestCases
-- Test case 1: example from prompt
-- "123456" -> true

def test1_s : String := "123456"
def test1_Expected : Bool := true

-- Test case 2: contains a non-digit letter
-- "123a56" -> false

def test2_s : String := "123a56"
def test2_Expected : Bool := false

-- Test case 3: empty string is vacuously all digits
-- "" -> true

def test3_s : String := ""
def test3_Expected : Bool := true

-- Test case 4: leading zeros are still digits
-- "007" -> true

def test4_s : String := "007"
def test4_Expected : Bool := true

-- Test case 5: contains whitespace
-- "98 76" -> false

def test5_s : String := "98 76"
def test5_Expected : Bool := false

-- Test case 6: single digit

def test6_s : String := "5"
def test6_Expected : Bool := true

-- Test case 7: single non-digit punctuation

def test7_s : String := "+"
def test7_Expected : Bool := false

-- Test case 8: newline character present

def test8_s : String := "12\n34"
def test8_Expected : Bool := false

-- Test case 9: mixed punctuation and digits

def test9_s : String := "12-34"
def test9_Expected : Bool := false

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test2, test3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((allDigits test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((allDigits test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((allDigits test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((allDigits test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((allDigits test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((allDigits test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((allDigits test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((allDigits test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((allDigits test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for allDigits
prove_precondition_decidable_for allDigits
prove_postcondition_decidable_for allDigits
derive_tester_for allDigits
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := allDigitsTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct allDigits by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (i : ℕ)
    (ok : Bool)
    (invariant_inv_ok_eq_prefixAll : ok = (List.take i s.data).all Char.isDigit)
    (a : i < s.data.length)
    (a_1 : ok = true)
    (if_pos : (s.data[i]?.getD 'A').isDigit = true)
    : ok = (List.take (i + 1) s.data).all Char.isDigit := by
  -- From ok = true and the invariant, the first i chars are all digits.
  have htakei_true : (List.take i s.data).all Char.isDigit = true := by
    calc
      (List.take i s.data).all Char.isDigit = ok := by
        simpa using invariant_inv_ok_eq_prefixAll.symm
      _ = true := a_1

  -- In-bounds: convert getD of get? into the actual element.
  have hgetD : s.data[i]?.getD 'A' = s.data[i]'a := by
    simp [List.getD_getElem?, a]

  have hi_digit : (s.data[i]'a).isDigit = true := by
    simpa [hgetD] using if_pos

  -- Compute `.all` on the (i+1)-prefix as conjunction of the i-prefix and the i-th element.
  have htakesucc_true : (List.take (i + 1) s.data).all Char.isDigit = true := by
    -- Rewrite take (i+1) as take i ++ [l[i]], then use `all_append`.
    -- Avoid `simp` recursion by rewriting step-by-step.
    have ht :
        List.take (i + 1) s.data = List.take i s.data ++ [s.data[i]'a] := by
      simpa using (List.take_succ_eq_append_getElem (l := s.data) (i := i) a)
    -- Now compute `all` on both sides.
    rw [ht, List.all_append]
    -- Reduce `[x].all f` via `List.all_cons` and `List.all` on `[]`.
    -- Then finish by rewriting with known truths.
    -- Goal: ((take i ...).all .. && [x].all ..) = true
    -- where [x].all .. = (Char.isDigit x && true)
    simpa [List.all_cons, List.all, htakei_true, hi_digit]

  -- Finish: both sides are `true`.
  calc
    ok = true := a_1
    _ = (List.take (i + 1) s.data).all Char.isDigit := by
      simpa [htakesucc_true]

theorem goal_1
    (s : String)
    (i : ℕ)
    (a : i < s.data.length)
    (if_neg : (s.data[i]?.getD 'A').isDigit = false)
    : ∃ x ∈ List.take (i + 1) s.data, x.isDigit = false := by
  refine ⟨s.data[i]'a, ?_, ?_⟩
  · -- membership: the i-th element is in the prefix of length i+1
    have ht :
        List.take (i + 1) s.data = List.take i s.data ++ [s.data[i]'a] :=
      List.take_succ_eq_append_getElem (l := s.data) (i := i) a
    -- show membership in the RHS, then rewrite using ht.symm
    have hx : s.data[i]'a ∈ List.take i s.data ++ [s.data[i]'a] := by
      apply List.mem_append_right
      simp
    -- avoid simp recursion: rewrite by ht (in reverse direction)
    exact ht.symm ▸ hx
  · -- not-a-digit: rewrite the getD form using the bounds a
    have hget : s.data[i]?.getD 'A' = s.data[i]'a := by
      simp [List.getD_getElem?, a]
    -- rewrite and close
    simpa [hget] using if_neg

theorem goal_2
    (s : String)
    (i : ℕ)
    (ok : Bool)
    (invariant_inv_ok_eq_prefixAll : ok = (List.take i s.data).all Char.isDigit)
    (done_1 : i = s.data.length ∨ ok = false)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (i_2 : i = i_1 ∧ ok = ok_1)
    : postcondition s ok_1 := by
    unfold postcondition
    unfold allDigitsBool
    rcases i_2 with ⟨hi, hok⟩
    -- reduce to showing `ok = s.data.all isDigit` and then rewrite by `hok`
    have : ok = s.data.all Char.isDigit := by
      cases done_1 with
      | inl hlen =>
          -- i reached the length: take i = full list
          -- so `ok = (take i data).all = data.all`
          simpa [invariant_inv_ok_eq_prefixAll, hlen, List.take_length]
      | inr hokFalse =>
          -- ok is false, so prefix-all is false; hence whole-list-all is false
          have hprefixFalse : (List.take i s.data).all Char.isDigit = false := by
            -- from invariant and ok=false
            simpa [invariant_inv_ok_eq_prefixAll] using hokFalse
          have hfullFalse : s.data.all Char.isDigit = false := by
            -- use all_eq_false and prefix property of take
            rcases (List.all_eq_false).1 hprefixFalse with ⟨x, hx_mem_take, hx_not⟩
            have hx_mem : x ∈ s.data := by
              exact List.mem_of_mem_take hx_mem_take
            -- conclude all is false on full list
            exact (List.all_eq_false).2 ⟨x, hx_mem, hx_not⟩
          -- combine
          simpa [hokFalse, hfullFalse]
    -- finish: rewrite ok_1 using hok
    simpa [hok] using congrArg (fun b => (b : Bool)) this


prove_correct allDigits by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s i ok invariant_inv_ok_eq_prefixAll a a_1 if_pos)
  exact (goal_1 s i a if_neg)
  exact (goal_2 s i ok invariant_inv_ok_eq_prefixAll done_1 i_1 ok_1 i_2)
end Proof
