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
    toUppercase: Convert a string to uppercase.
    Natural language breakdown:
    1. Input is a string s.
    2. Output is a string result.
    3. The output has the same length as the input.
    4. For every position i within bounds, the i-th character of result equals
       the uppercase of the i-th character of s.
    5. Uppercasing is performed using Char.toUpper: lowercase ASCII letters are
       mapped to their corresponding uppercase letters; all other characters are unchanged.
    6. There are no preconditions.
-/

section Specs
def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  result.length = s.length ∧
    (∀ (i : Nat), i < s.length → result.toList[i]! = (s.toList[i]!).toUpper)
end Specs

section Impl
method toUppercase (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  let chars := s.toList
  let mut out : List Char := []
  let mut i : Nat := 0
  while i < chars.length
    -- i stays within bounds of chars, giving safe indexing and enabling exit reasoning
    invariant "inv_bounds" i ≤ chars.length
    -- out is exactly the mapped prefix (toUpper) of the first i characters of chars
    -- initialization: i=0, out=[] = map ... []
    -- preservation: body appends toUpper(chars[i]) matching map over take (i+1)
    invariant "inv_out_prefix" out = (List.map (fun c => c.toUpper) (chars.take i))
    -- length of out tracks progress and will match final string length
    invariant "inv_len" out.length = i
    done_with (i = chars.length)
  do
    out := out.concat ((chars[i]!).toUpper)
    i := i + 1
  let res := String.mk out
  return res
end Impl

section TestCases
-- Test case 1: provided example
-- "Hello, World!" → "HELLO, WORLD!"
def test1_s : String := "Hello, World!"
def test1_Expected : String := "HELLO, WORLD!"

-- Test case 2: all lowercase
def test2_s : String := "abc"
def test2_Expected : String := "ABC"

-- Test case 3: already uppercase
def test3_s : String := "ABC"
def test3_Expected : String := "ABC"

-- Test case 4: non-letters unchanged
def test4_s : String := "123!?@"
def test4_Expected : String := "123!?@"

-- Test case 5: empty string
def test5_s : String := ""
def test5_Expected : String := ""

-- Test case 6: mixed with whitespace and newlines
def test6_s : String := "a Z\n\t!"
def test6_Expected : String := "A Z\n\t!"

-- Test case 7: letters near ASCII boundaries
def test7_s : String := "xyzXYZ"
def test7_Expected : String := "XYZXYZ"

-- Test case 8: punctuation around letters
def test8_s : String := "(lean4)"
def test8_Expected : String := "(LEAN4)"

-- Test case 9: repeating letters and mixed case
def test9_s : String := "aAaA"
def test9_Expected : String := "AAAA"

-- Recommend to validate: test1, test2, test5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((toUppercase test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((toUppercase test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((toUppercase test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((toUppercase test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((toUppercase test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((toUppercase test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((toUppercase test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((toUppercase test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((toUppercase test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for toUppercase
prove_precondition_decidable_for toUppercase
prove_postcondition_decidable_for toUppercase
derive_tester_for toUppercase
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := toUppercaseTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct toUppercase by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (require_1 : precondition s)
    (i : ℕ)
    (out : List Char)
    (invariant_inv_bounds : i ≤ s.data.length)
    (invariant_inv_len : out.length = i)
    (if_pos : i < s.data.length)
    (invariant_inv_out_prefix : out = List.take i (List.map (fun c ↦ c.toUpper) s.data))
    : out ++ [(s.data[i]?.getD 'A').toUpper] = List.take (i + 1) (List.map (fun c ↦ c.toUpper) s.data) := by
  -- rewrite `out` using the invariant
  subst invariant_inv_out_prefix

  -- abbreviate the mapped list
  let l : List Char := List.map (fun c ↦ c.toUpper) s.data
  have hl : l.length = s.data.length := by
    simp [l]

  have hi_l : i < l.length := by
    simpa [hl] using if_pos

  -- characterize `take (i+1)` as `take i ++ [l[i]]`
  have htake : (List.take i l) ++ [l[i]] = List.take (i + 1) l := by
    simpa using (List.take_append_getElem (l := l) (i := i) hi_l)

  -- compute the appended element (in bounds, so the default is irrelevant)
  have hgetD : s.data[i]?.getD 'A' = s.data[i] := by
    -- use the in-bounds description of `getD` over `get?`
    simpa [List.getD_getElem?, if_pos] using
      (List.getD_getElem? (l := s.data) (i := i) (d := ('A' : Char)))

  -- relate the appended element to `l[i]`
  have hElem : (s.data[i]?.getD 'A').toUpper = l[i] := by
    -- reduce to the usual `map`/index interaction
    have : l[i] = (s.data[i]).toUpper := by
      -- `List.getElem_map` gives `(map f xs)[i] = f (xs[i])` under the bound hypothesis
      simpa [l] using (List.getElem_map (f := fun c : Char ↦ c.toUpper) (l := s.data) if_pos)
    simpa [hgetD, this]

  -- finish
  simpa [l, hElem] using htake

theorem goal_1
    (s : String)
    (require_1 : precondition s)
    (i : ℕ)
    (out : List Char)
    (invariant_inv_bounds : i ≤ s.data.length)
    (invariant_inv_len : out.length = i)
    (done_1 : i = s.data.length)
    (i_1 : ℕ)
    (out_1 : List Char)
    (invariant_inv_out_prefix : out = List.take i (List.map (fun c ↦ c.toUpper) s.data))
    (i_2 : i = i_1 ∧ out = out_1)
    : postcondition s { data := out_1 } := by
  rcases i_2 with ⟨hi, hout⟩

  have hout1 : out_1 = List.map (fun c ↦ c.toUpper) s.data := by
    have : out = List.map (fun c ↦ c.toUpper) s.data := by
      calc
        out = List.take i (List.map (fun c ↦ c.toUpper) s.data) := by
          simpa [invariant_inv_out_prefix]
        _ = List.take (s.data.length) (List.map (fun c ↦ c.toUpper) s.data) := by
          simpa [done_1]
        _ = List.map (fun c ↦ c.toUpper) s.data := by
          simpa [List.take_length]
    simpa [hout] using this

  unfold postcondition
  constructor
  · -- length equality
    -- reduce to list lengths
    have : out_1.length = s.data.length := by
      simpa [hout1, List.length_map]
    simpa [String.length_mk] using this
  · -- pointwise character property
    intro j hj
    have hj' : j < s.data.length := by
      simpa using hj
    -- rewrite out_1, then evaluate get! via getElem under the bound
    have hmap : j < (List.map (fun c ↦ c.toUpper) s.data).length := by
      simpa [List.length_map] using hj'
    -- convert `get!` to `getElem` using the bound
    simpa [hout1, List.getElem_map, hmap, hj'] using
      (List.get_of_eq_true rfl : (List.map (fun c ↦ c.toUpper) s.data)[j]'hmap =
        (s.data[j]'hj').toUpper)


prove_correct toUppercase by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1 i out invariant_inv_bounds invariant_inv_len if_pos invariant_inv_out_prefix)
  exact (goal_1 s require_1 i out invariant_inv_bounds invariant_inv_len done_1 i_1 out_1 invariant_inv_out_prefix i_2)
end Proof
