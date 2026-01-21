import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Mathlib.Data.String.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replaceChars: Replace every occurrence of a specified character in a string.
    Natural language breakdown:
    1. Inputs are a string s and two characters oldChar and newChar.
    2. The result is a string with the same number of characters as s.
    3. For each index i within bounds, if the i-th character of s equals oldChar,
       then the i-th character of the result equals newChar.
    4. For each index i within bounds, if the i-th character of s does not equal oldChar,
       then the i-th character of the result equals the i-th character of s.
    5. There are no preconditions; the method must work for any string and characters.
-/

section Specs
-- Helper: pointwise replacement on characters.
-- This is a simple, computable predicate used in the postcondition.
def replChar (oldChar : Char) (newChar : Char) (c : Char) : Char :=
  if c = oldChar then newChar else c

-- No preconditions.
def precondition (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True

-- Postcondition: list-view length preserved and pointwise replacement behavior on `toList`.
-- We specify everything through `toList` to avoid mixing different views (`String.length` vs list length).
def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  (∀ (i : Nat), i < s.toList.length →
    result.toList[i]! = replChar oldChar newChar (s.toList[i]!))
end Specs

section Impl
method replaceChars (s : String) (oldChar : Char) (newChar : Char)
  return (result : String)
  require precondition s oldChar newChar
  ensures postcondition s oldChar newChar result
  do
  let chars := s.toList
  let mut out := ""
  let mut i : Nat := 0
  while i < chars.length
    -- i stays within bounds of `chars`.
    -- Init: i = 0. Preserved: i increases by 1 while guard enforces i < chars.length.
    invariant "inv_bounds" i ≤ chars.length
    -- `out` is the result of pointwise replacement on the prefix processed so far.
    -- Init: i=0, out="". Preserved: we append exactly replChar(...) of chars[i]!
    -- Suffices: at exit i=chars.length, we have full list processed.
    invariant "inv_out_list" out.toList = (List.map (replChar oldChar newChar) (chars.take i))
  do
    let c := chars[i]!
    let c' := replChar oldChar newChar c
    out := out.push c'
    i := i + 1
  return out
end Impl

section TestCases
-- Test case 1: example from prompt

def test1_s : String := "hello, world!"
def test1_oldChar : Char := ','
def test1_newChar : Char := ';'
def test1_Expected : String := "hello; world!"

-- Test case 2: punctuation replacement inside string

def test2_s : String := "a,b.c"
def test2_oldChar : Char := ','
def test2_newChar : Char := ':'
def test2_Expected : String := "a:b.c"

-- Test case 3: multiple occurrences of a letter

def test3_s : String := "hello, world!"
def test3_oldChar : Char := 'o'
def test3_newChar : Char := 'O'
def test3_Expected : String := "hellO, wOrld!"

-- Test case 4: empty string

def test4_s : String := ""
def test4_oldChar : Char := 'x'
def test4_newChar : Char := 'y'
def test4_Expected : String := ""

-- Test case 5: oldChar not present

def test5_s : String := "test"
def test5_oldChar : Char := 'x'
def test5_newChar : Char := 'y'
def test5_Expected : String := "test"

-- Test case 6: oldChar equals newChar (idempotent)

def test6_s : String := "unchanged"
def test6_oldChar : Char := 'u'
def test6_newChar : Char := 'u'
def test6_Expected : String := "unchanged"

-- Test case 7: all characters replaced

def test7_s : String := "aaa"
def test7_oldChar : Char := 'a'
def test7_newChar : Char := 'b'
def test7_Expected : String := "bbb"

-- Test case 8: single-character string replaced

def test8_s : String := "x"
def test8_oldChar : Char := 'x'
def test8_newChar : Char := 'y'
def test8_Expected : String := "y"

-- Test case 9: single-character string unchanged

def test9_s : String := "x"
def test9_oldChar : Char := 'z'
def test9_newChar : Char := 'y'
def test9_Expected : String := "x"

-- Recommend to validate: test1, test3, test7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((replaceChars test1_s test1_oldChar test1_newChar).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((replaceChars test2_s test2_oldChar test2_newChar).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((replaceChars test3_s test3_oldChar test3_newChar).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((replaceChars test4_s test4_oldChar test4_newChar).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((replaceChars test5_s test5_oldChar test5_newChar).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((replaceChars test6_s test6_oldChar test6_newChar).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((replaceChars test7_s test7_oldChar test7_newChar).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((replaceChars test8_s test8_oldChar test8_newChar).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((replaceChars test9_s test9_oldChar test9_newChar).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for replaceChars
prove_precondition_decidable_for replaceChars
prove_postcondition_decidable_for replaceChars
derive_tester_for replaceChars
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let arg_1 ← Plausible.SampleableExt.interpSample (Char)
    let arg_2 ← Plausible.SampleableExt.interpSample (Char)
    let res := replaceCharsTester arg_0 arg_1 arg_2
    pure ((arg_0, arg_1, arg_2), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct replaceChars by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (h_lt_sdata : i < s.length)
    (h_len_sdata : True)
    (h_len_map : True)
    (h_lt_map : i < s.length)
    : List.take (i + 1) (List.map (replChar oldChar newChar) s.data) =
        List.take i (List.map (replChar oldChar newChar) s.data) ++
          [replChar oldChar newChar (s.data[i]?.getD 'A')] := by
  -- First use the standard take-succ lemma on the mapped list.
  have hi : i < (List.map (replChar oldChar newChar) s.data).length := by
    -- avoid rewriting `String.length`; instead transfer the bound directly via `data.length`
    -- `simp` knows `(String.mk s.data).length = s.data.length`-style facts for `s.length`.
    simpa [List.length_map] using h_lt_sdata

  -- Then rewrite the last element from `s.data[i]` to `s.data[i]?.getD 'A'` using the in-bounds fact.
  have hgetD : s.data[i]?.getD 'A' = s.data[i] := by
    -- `getElem?_eq_some` gives in-bounds optional indexing; then `getD` reduces.
    have hs : s.data[i]? = some (s.data[i]) := by
      simpa using (List.getElem?_eq_some.2 hi)
    simpa [Option.getD, hs]

  -- Finish by rewriting the singleton element.
  simpa [hgetD] using
    (List.take_succ_eq_append_getElem
      (l := List.map (replChar oldChar newChar) s.data) (i := i) hi)

theorem goal_0_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (h_len_sdata : s.data.length = s.length)
    (h_lt_sdata : i < s.data.length)
    (h_len_map : (List.map (replChar oldChar newChar) s.data).length = s.data.length)
    (h_lt_map : i < (List.map (replChar oldChar newChar) s.data).length)
    (h_take_succ : List.take (i + 1) (List.map (replChar oldChar newChar) s.data) = List.take i (List.map (replChar oldChar newChar) s.data) ++ [(List.map (replChar oldChar newChar) s.data)[i]?.getD (replChar oldChar newChar 'A')])
    (h_getElem_map? : (List.map (replChar oldChar newChar) s.data)[i]? = Option.map (replChar oldChar newChar) s.data[i]?)
    : (List.map (replChar oldChar newChar) s.data)[i]?.getD (replChar oldChar newChar 'A') = replChar oldChar newChar (s.data[i]?.getD 'A') := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    : out.data ++ [replChar oldChar newChar (s.data[i]?.getD 'A')] = List.take (i + 1) (List.map (replChar oldChar newChar) s.data) := by
    -- Step 6: convert the bound `i < s.length` into a bound on the mapped list length
    have h_len_sdata : s.data.length = s.length := by
      (try simp at *; expose_names); exact rfl; done
    have h_lt_sdata : i < s.data.length := by
      (try simp at *; expose_names); exact if_pos; done
    have h_len_map : (List.map (replChar oldChar newChar) s.data).length = s.data.length := by
      (try simp at *; expose_names); exact List.length_map (replChar oldChar newChar); done
    have h_lt_map : i < (List.map (replChar oldChar newChar) s.data).length := by
      (try simp at *; expose_names); exact if_pos; done

    -- Step 4: take-succ decomposition on the mapped list
    have h_take_succ :
        List.take (i + 1) (List.map (replChar oldChar newChar) s.data)
          =
        List.take i (List.map (replChar oldChar newChar) s.data) ++
          [((List.map (replChar oldChar newChar) s.data)[i]? ).getD (replChar oldChar newChar 'A')] := by
      (try simp at *; expose_names); exact (goal_0_0 s oldChar newChar require_1 i out invariant_inv_bounds if_pos invariant_inv_out_list h_lt_sdata h_len_sdata h_len_map h_lt_map); done

    -- Step 5: relate the appended element to the mapped list's `getD`
    have h_getElem_map? :
        (List.map (replChar oldChar newChar) s.data)[i]?
          =
        Option.map (replChar oldChar newChar) (s.data[i]?) := by
      (try simp at *; expose_names); exact List.getElem?_map; done
    have h_getD_map :
        (((List.map (replChar oldChar newChar) s.data)[i]? ).getD (replChar oldChar newChar 'A'))
          =
        replChar oldChar newChar ((s.data[i]? ).getD 'A') := by
      (try simp at *; expose_names); exact (goal_0_1 s oldChar newChar require_1 i out invariant_inv_bounds if_pos invariant_inv_out_list h_len_sdata h_lt_sdata h_len_map h_lt_map h_take_succ h_getElem_map?); done

    -- Step 3: rewrite `out.data` using the invariant, then finish via the above facts
    calc
      out.data ++ [replChar oldChar newChar (s.data[i]?.getD 'A')]
          =
        (List.take i (List.map (replChar oldChar newChar) s.data)) ++
          [replChar oldChar newChar (s.data[i]?.getD 'A')] := by
            simpa [invariant_inv_out_list]
      _ =
        (List.take i (List.map (replChar oldChar newChar) s.data)) ++
          [((List.map (replChar oldChar newChar) s.data)[i]? ).getD (replChar oldChar newChar 'A')] := by
            simpa [h_getD_map]
      _ =
        List.take (i + 1) (List.map (replChar oldChar newChar) s.data) := by
            simpa [h_take_succ]

theorem goal_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    : "".toList = List.map (replChar oldChar newChar) (List.take 0 s.toList) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    : out = out_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (hout : out = out_1)
    (hi_eq_len : i = s.length)
    : out.data = List.take s.length (List.map (replChar oldChar newChar) s.data) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_2
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (hout : out = out_1)
    (hi_eq_len : i = s.length)
    (hout_data_take_len : out.data = List.take s.length (List.map (replChar oldChar newChar) s.data))
    : List.take s.length (List.map (replChar oldChar newChar) s.data) = List.map (replChar oldChar newChar) s.data := by
    -- `String.length` is definitional: for `s = ⟨xs⟩`, `s.length = xs.length`.
    cases s with
    | mk xs =>
      -- goal becomes `List.take xs.length (List.map _ xs) = List.map _ xs`
      simpa using (List.take_length (l := List.map (replChar oldChar newChar) xs))

theorem goal_2_3
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (hout : out = out_1)
    (hi_eq_len : i = s.length)
    (hout_data_take_len : out.data = List.take s.length (List.map (replChar oldChar newChar) s.data))
    (htake_all : True)
    : out.data = List.map (replChar oldChar newChar) s.data := by
    -- Reduce to showing the take is the whole list.
    rw [hout_data_take_len]
    -- `s.length` is definitionaly `s.data.length`, so this is `take (length (map _ s.data)) (map _ s.data)`.
    cases s with
    | mk xs =>
      simp [String.length_mk, List.take_length]

theorem goal_2_4
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (hout : out = out_1)
    (hi_eq_len : i = s.length)
    (hout_data_take_len : out.data = List.take s.length (List.map (replChar oldChar newChar) s.data))
    (hout_data_map : out.data = List.map (replChar oldChar newChar) s.data)
    (htake_all : True)
    : out_1.data = List.map (replChar oldChar newChar) s.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )



end Proof
