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
    replaceWithColon: Replace each space, comma, or dot character in a string with a colon.
    Natural language breakdown:
    1. Input is a single string s.
    2. Output is a string result.
    3. The output and input have the same number of characters (as lists of Char).
    4. For each character position i within s.toList.length:
       - If the input character is ' ' or ',' or '.', then the output character is ':'.
       - Otherwise, the output character equals the input character.
    5. All characters not in the set {space, comma, dot} remain unchanged.
    6. There are no preconditions.
-/

section Specs
-- Helper: the set of characters to be replaced.
def shouldReplaceWithColon (c : Char) : Bool :=
  c = ' ' || c = ',' || c = '.'

-- Helper: pointwise character relation between input/output at an index.
def charSpecAt (s : String) (result : String) (i : Nat) : Prop :=
  i < s.toList.length →
    let cin := s.toList[i]!
    let cout := result.toList[i]!
    (shouldReplaceWithColon cin = true → cout = ':') ∧
    (shouldReplaceWithColon cin = false → cout = cin)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  ∀ i : Nat, charSpecAt s result i
end Specs

section Impl
method replaceWithColon (s : String) return (result : String)
  require precondition s
  ensures postcondition s result
  do
  let chars : List Char := s.toList
  let mut out : List Char := []
  let mut i : Nat := 0
  while i < chars.length
    -- i stays within bounds; needed for safe indexing and to relate out to prefix processed so far.
    invariant "inv_bounds" i ≤ chars.length
    -- out is built pointwise from the first i characters of chars.
    -- Initialization: i=0 so both sides are [].
    -- Preservation: loop appends exactly one character matching spec for chars[i]!, extending map over prefix.
    invariant "inv_out_eq" out = (List.map (fun c => if shouldReplaceWithColon c = true then ':' else c) (chars.take i))
    -- Length of out matches number of processed characters; helps discharge final length postcondition.
    invariant "inv_len" out.length = i
    done_with i = chars.length
  do
    let c := chars[i]!
    if shouldReplaceWithColon c = true then
      out := out ++ [':']
    else
      out := out ++ [c]
    i := i + 1
  let resStr : String := String.mk out
  return resStr
end Impl

section TestCases
-- Test case 1: example from prompt
-- "Hello, world. How are you?" -> "Hello::world::How:are:you?"
def test1_s : String := "Hello, world. How are you?"
def test1_Expected : String := "Hello::world::How:are:you?"

-- Test case 2: no characters to replace
-- "No-changes!" stays the same
def test2_s : String := "No-changes!"
def test2_Expected : String := "No-changes!"

-- Test case 3: only replaceable characters
-- ",. " -> ":::"
def test3_s : String := ",. "
def test3_Expected : String := ":::"

-- Test case 4: empty string
def test4_s : String := ""
def test4_Expected : String := ""

-- Test case 5: single replaceable character: space
def test5_s : String := " "
def test5_Expected : String := ":"

-- Test case 6: single replaceable character: comma
def test6_s : String := ","
def test6_Expected : String := ":"

-- Test case 7: single replaceable character: dot
def test7_s : String := "."
def test7_Expected : String := ":"

-- Test case 8: mixture with consecutive punctuation and internal spaces
def test8_s : String := "a, b.c"
def test8_Expected : String := "a::b:c"

-- Test case 9: other punctuation should remain unchanged (question mark, exclamation)
def test9_s : String := "?.!?"
def test9_Expected : String := "?:!?"

-- Recommend to validate: 1, 3, 8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((replaceWithColon test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((replaceWithColon test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((replaceWithColon test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((replaceWithColon test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((replaceWithColon test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((replaceWithColon test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((replaceWithColon test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((replaceWithColon test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((replaceWithColon test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for replaceWithColon
prove_precondition_decidable_for replaceWithColon
prove_postcondition_decidable_for replaceWithColon
derive_tester_for replaceWithColon
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := replaceWithColonTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct replaceWithColon by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (i : ℕ)
    (out : List Char)
    (invariant_inv_len : out.length = i)
    (if_pos : i < s.data.length)
    (invariant_inv_out_eq : out = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (if_pos_1 : shouldReplaceWithColon (s.data[i]?.getD 'A') = true)
    : out ++ [':'] = List.take (i + 1) (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
  -- rewrite `out` using the invariant
  subst invariant_inv_out_eq

  -- Let `xs` be the mapped list we are taking prefixes of
  set xs :=
    List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data

  -- Convert the branch condition to an `xs[i]?` statement (in-bounds)
  have hopt : xs[i]? = some ':' := by
    -- First, eliminate the default `'A'` since we are in-bounds
    have hgD : s.data[i]?.getD 'A' = s.data[i]'if_pos := by
      simp [List.getD_getElem?, if_pos]
    have htrue : shouldReplaceWithColon (s.data[i]'if_pos) = true := by
      simpa [hgD] using if_pos_1

    -- Now compute `xs[i]?` via mapping, and use `htrue` to simplify the `if`
    -- `(map f l)[i]? = Option.map f (l[i]?)`, and `l[i]? = some (l[i]'if_pos)`
    simp [xs, List.getElem?_map, List.get?_eq_get, if_pos, htrue]

  -- `take (i+1)` decomposes as `take i` plus `xs[i]?.toList`
  -- and `hopt` makes that last part `[ ':']`.
  have ht : List.take (i + 1) xs = List.take i xs ++ [':'] := by
    simpa [List.take_succ, hopt]

  -- Finish by rewriting the RHS using `ht`
  simpa [ht]

theorem goal_1
    (s : String)
    (i : ℕ)
    (out : List Char)
    (if_pos : i < s.data.length)
    (invariant_inv_out_eq : out = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (if_neg : shouldReplaceWithColon (s.data[i]?.getD 'A') = false)
    : out ++ [s.data[i]?.getD 'A'] = List.take (i + 1) (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
  -- simplify the in-bounds `getD` at index `i`
  have hgetD : s.data[i]?.getD 'A' = s.data[i] := by
    -- `getD_getElem?` gives an if-then-else; `if_pos` selects the in-bounds branch
    simpa [List.getD_getElem?, if_pos]

  -- rewrite the branch condition in terms of the actual element
  have hneg' : shouldReplaceWithColon (s.data[i]) = false := by
    simpa [hgetD] using if_neg

  -- rewrite `out` using the invariant
  rw [invariant_inv_out_eq]
  -- rewrite the appended element using in-bounds `getD`
  simp [hgetD]

  -- let xs be the mapped list; use `take_succ` and compute the `i`th option
  set xs :=
    List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data with hxs

  -- expand `take (i+1)` using `take_succ`
  -- it suffices to show that `xs[i]?.toList = [s.data[i]]`
  have : xs[i]?.toList = [s.data[i]] := by
    -- compute `xs[i]?` via `map` and in-bounds `getElem?` on `s.data`
    have hsdata : s.data[i]? = some s.data[i] := by
      simpa using (List.getElem?_eq_getElem (l := s.data) (i := i) if_pos)
    have hxi : xs[i]? =
        some ((fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data[i]) := by
      -- push `get?` through `map`
      simp [xs, List.getElem?_map, hsdata]
    -- simplify the mapped element using the fact we're in the "no replacement" branch
    have hf :
        (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data[i] = s.data[i] := by
      simp [hneg']
    -- finish: option toList of a `some` is singleton
    simp [hxi, hf]

  -- finish with `take_succ`
  -- `List.take_succ` is: take (i+1) xs = take i xs ++ xs[i]?.toList
  -- so rewrite RHS and use the computed singleton list
  have ht : List.take (i + 1) xs = List.take i xs ++ xs[i]?.toList := by
    simpa [List.take_succ]
  -- use ht and `this`
  calc
    List.take i xs ++ [s.data[i]] =
        List.take i xs ++ xs[i]?.toList := by simpa [this]
    _ = List.take (i + 1) xs := by simpa [ht]
    _ = List.take (i + 1)
          (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
          simpa [xs]

theorem goal_2_0
    (i : ℕ)
    (out : List Char)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    : i = i_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_1
    (i : ℕ)
    (out : List Char)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    : out = out_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_2
    (i : ℕ)
    (out : List Char)
    (invariant_inv_len : out.length = i)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    : out_1.length = i := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_3
    (s : String)
    (i : ℕ)
    (out : List Char)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    : out_1.length = s.data.length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_4
    (s : String)
    (i : ℕ)
    (out : List Char)
    (i_1 : ℕ)
    (out_1 : List Char)
    (invariant_inv_out_eq : out = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    (hlen : out_1.length = s.data.length)
    : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_5
    (s : String)
    (i : ℕ)
    (out : List Char)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (out_1 : List Char)
    (invariant_inv_out_eq : out = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    (hlen : out_1.length = s.data.length)
    (hout1_eq_take_i_map : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    : out_1 = List.take s.data.length (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_6
    (s : String)
    (i : ℕ)
    (out : List Char)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (out_1 : List Char)
    (invariant_inv_out_eq : out = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    (hlen : out_1.length = s.data.length)
    (hout1_eq_take_i_map : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_take_len_map : out_1 = List.take s.data.length (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    : out_1 = List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_7
    (s : String)
    (i : ℕ)
    (out : List Char)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    (hlen : out_1.length = s.data.length)
    (hout1_eq_take_i_map : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_take_len_map : out_1 = List.take s.data.length (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_map : out_1 = List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data)
    (j : ℕ)
    (hj : j < s.data.length)
    : out_1[j]?.getD 'A' = if shouldReplaceWithColon (s.data[j]?.getD 'A') = true then ':' else s.data[j]?.getD 'A' := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_8
    (s : String)
    (i : ℕ)
    (out : List Char)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    (hlen : out_1.length = s.data.length)
    (hout1_eq_take_i_map : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_take_len_map : out_1 = List.take s.data.length (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_map : out_1 = List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data)
    (j : ℕ)
    (hj : j < s.data.length)
    (hcout : out_1[j]?.getD 'A' = if shouldReplaceWithColon (s.data[j]?.getD 'A') = true then ':' else s.data[j]?.getD 'A')
    (htrue : shouldReplaceWithColon (s.data[j]?.getD 'A') = true)
    : out_1[j]?.getD 'A' = ':' := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_9
    (s : String)
    (i : ℕ)
    (out : List Char)
    (i_1 : ℕ)
    (out_1 : List Char)
    (i_2 : i = i_1 ∧ out = out_1)
    (hi : i = i_1)
    (hout : out = out_1)
    (hlen_out1_eq_i : out_1.length = i)
    (hlen : out_1.length = s.data.length)
    (hout1_eq_take_i_map : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_take_len_map : out_1 = List.take s.data.length (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (hout1_eq_map : out_1 = List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data)
    (j : ℕ)
    (hj : j < s.data.length)
    (hcout : out_1[j]?.getD 'A' = if shouldReplaceWithColon (s.data[j]?.getD 'A') = true then ':' else s.data[j]?.getD 'A')
    (hfalse : shouldReplaceWithColon (s.data[j]?.getD 'A') = false)
    : out_1[j]?.getD 'A' = s.data[j]?.getD 'A' := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2
    (s : String)
    (i : ℕ)
    (out : List Char)
    (invariant_inv_len : out.length = i)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (out_1 : List Char)
    (invariant_inv_out_eq : out = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data))
    (i_2 : i = i_1 ∧ out = out_1)
    : postcondition s { data := out_1 } := by
  -- unpack the "state copy" equality
  have hi : i = i_1 := by
    (try simp at *; expose_names); exact (goal_2_0 i out i_1 out_1 i_2); done
  have hout : out = out_1 := by
    (try simp at *; expose_names); exact (goal_2_1 i out i_1 out_1 i_2 hi); done

  -- transport invariant_inv_len to out_1
  have hlen_out1_eq_i : out_1.length = i := by
    (try simp at *; expose_names); exact (goal_2_2 i out invariant_inv_len i_1 out_1 i_2 hi hout); done

  -- length part of postcondition
  have hlen : ({ data := out_1 } : String).toList.length = s.toList.length := by
    (try simp at *; expose_names); exact (goal_2_3 s i out done_1 i_1 out_1 i_2 hi hout hlen_out1_eq_i); done

  -- simplify the invariant at termination to get a full-map characterization of out_1
  have hout1_eq_take_i_map : out_1 = List.take i (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
    (try simp at *; expose_names); exact (goal_2_4 s i out i_1 out_1 invariant_inv_out_eq i_2 hi hout hlen_out1_eq_i hlen); done
  have hout1_eq_take_len_map :
      out_1 = List.take s.data.length (List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data) := by
    (try simp at *; expose_names); exact (goal_2_5 s i out done_1 i_1 out_1 invariant_inv_out_eq i_2 hi hout hlen_out1_eq_i hlen hout1_eq_take_i_map); done
  have hout1_eq_map :
      out_1 = List.map (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) s.data := by
    (try simp at *; expose_names); exact (goal_2_6 s i out done_1 i_1 out_1 invariant_inv_out_eq i_2 hi hout hlen_out1_eq_i hlen hout1_eq_take_i_map hout1_eq_take_len_map); done

  -- pointwise charSpecAt
  have hcharspec : ∀ j : Nat, charSpecAt s ({ data := out_1 } : String) j := by
    intro j
    -- unfold the spec and assume the index is in-bounds
    unfold charSpecAt
    intro hj
    -- rewrite toList/data and replace out_1 by the full map
    have hcout :
        (({ data := out_1 } : String).toList[j]!) =
          (fun c ↦ if shouldReplaceWithColon c = true then ':' else c) (s.toList[j]!) := by
      (try simp at *; expose_names); exact (goal_2_7 s i out done_1 i_1 out_1 i_2 hi hout hlen_out1_eq_i hlen hout1_eq_take_i_map hout1_eq_take_len_map hout1_eq_map j hj); done
    -- now the two implications follow by simplifying the `if`
    refine And.intro ?_ ?_
    · intro htrue
      -- use hcout and simp the `if` under htrue
      (try simp at *; expose_names); exact (goal_2_8 s i out i_1 out_1 i_2 hi hout hlen_out1_eq_i hlen hout1_eq_take_i_map hout1_eq_take_len_map hout1_eq_map j hj hcout htrue); done
    · intro hfalse
      -- use hcout and simp the `if` under hfalse
      (try simp at *; expose_names); exact (goal_2_9 s i out i_1 out_1 i_2 hi hout hlen_out1_eq_i hlen hout1_eq_take_i_map hout1_eq_take_len_map hout1_eq_map j hj hcout hfalse); done

  -- assemble the postcondition conjunction
  unfold postcondition
  exact And.intro hlen hcharspec


prove_correct replaceWithColon by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s i out invariant_inv_len if_pos invariant_inv_out_eq if_pos_1)
  exact (goal_1 s i out if_pos invariant_inv_out_eq if_neg)
  exact (goal_2 s i out invariant_inv_len done_1 i_1 out_1 invariant_inv_out_eq i_2)
end Proof
