import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    allVowels: Determine whether a given string contains all 5 English vowels (a, e, i, o, u)
    Natural language breakdown:
    1. The input is a string that may contain any characters
    2. The check is case-insensitive (both 'A' and 'a' count as the vowel 'a')
    3. All 5 vowels must be present: a, e, i, o, u
    4. Return true if all 5 vowels are found, false otherwise
    5. The vowels can appear anywhere in the string, in any order
    6. Each vowel only needs to appear at least once
    7. Use String.toLower for case-insensitive comparison
-/

section Specs
-- Define the set of vowels as lowercase characters
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']

-- Precondition: no restrictions on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff all 5 vowels appear in the string (case-insensitive)
-- Using property-based specification with List.all and membership
def postcondition (s : String) (result : Bool) : Prop :=
  result = (vowels.all (fun v => v ∈ s.toLower.toList))
end Specs

section Impl
method allVowels (s: String)
  return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  let chars := s.toLower.toList
  let mut hasA := false
  let mut hasE := false
  let mut hasI := false
  let mut hasO := false
  let mut hasU := false
  let mut i := 0
  while i < chars.length
    -- Bounds invariant: i stays within valid range
    invariant "i_bounds" 0 ≤ i ∧ i ≤ chars.length
    -- Flag invariant for 'a': hasA is true iff 'a' appears in first i characters
    invariant "hasA_inv" hasA = ('a' ∈ chars.take i)
    -- Flag invariant for 'e': hasE is true iff 'e' appears in first i characters
    invariant "hasE_inv" hasE = ('e' ∈ chars.take i)
    -- Flag invariant for 'i': hasI is true iff 'i' appears in first i characters
    invariant "hasI_inv" hasI = ('i' ∈ chars.take i)
    -- Flag invariant for 'o': hasO is true iff 'o' appears in first i characters
    invariant "hasO_inv" hasO = ('o' ∈ chars.take i)
    -- Flag invariant for 'u': hasU is true iff 'u' appears in first i characters
    invariant "hasU_inv" hasU = ('u' ∈ chars.take i)
    done_with i = chars.length
  do
    let c := chars.get! i
    if c = 'a' then
      hasA := true
    else
      if c = 'e' then
        hasE := true
      else
        if c = 'i' then
          hasI := true
        else
          if c = 'o' then
            hasO := true
          else
            if c = 'u' then
              hasU := true
    i := i + 1
  return (hasA && hasE && hasI && hasO && hasU)
end Impl

section TestCases
-- Test case 1: "education" contains all vowels (e, u, a, i, o)
def test1_s : String := "education"
def test1_Expected : Bool := true

-- Test case 2: "education123" contains all vowels with non-alpha chars
def test2_s : String := "education123"
def test2_Expected : Bool := true

-- Test case 3: "AEIOU" contains all vowels in uppercase
def test3_s : String := "AEIOU"
def test3_Expected : Bool := true

-- Test case 4: "hello" is missing some vowels (only has e, o)
def test4_s : String := "hello"
def test4_Expected : Bool := false

-- Test case 5: empty string has no vowels
def test5_s : String := ""
def test5_Expected : Bool := false

-- Test case 6: "apple orange union" contains all vowels across multiple words
def test6_s : String := "apple orange union"
def test6_Expected : Bool := true

-- Test case 7: "bcdfg" has no vowels at all
def test7_s : String := "bcdfg"
def test7_Expected : Bool := false

-- Test case 8: "aeiou" contains exactly all vowels in lowercase
def test8_s : String := "aeiou"
def test8_Expected : Bool := true

-- Test case 9: "AeIoU" mixed case vowels
def test9_s : String := "AeIoU"
def test9_Expected : Bool := true

-- Test case 10: "aaaa" only has one vowel repeated
def test10_s : String := "aaaa"
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((allVowels test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((allVowels test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((allVowels test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((allVowels test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((allVowels test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((allVowels test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((allVowels test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((allVowels test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((allVowels test9_s).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((allVowels test10_s).run), DivM.res test10_Expected ]
end Assertions

section Pbt
extract_program_for allVowels
prove_precondition_decidable_for allVowels
prove_postcondition_decidable_for allVowels
derive_tester_for allVowels
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (String)
    let res := allVowelsTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct allVowels by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'a')
    : 'a' ∈ List.take (i + 1) s.toLower.data := by
    have h1 : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    rw [h1, Option.getD_some] at if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    right
    simp [if_pos_1]

theorem goal_1
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'a')
    : hasE = true ↔ 'e' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_some_iff.mpr ⟨if_pos, rfl⟩
    have h_char : s.toLower.data[i] = 'a' := by
      simp [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    rw [h_char]
    simp only [List.mem_singleton]
    have h_ne : 'e' ≠ 'a' := by decide
    simp only [h_ne, or_false]
    exact invariant_hasE_inv

theorem goal_2
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'a')
    : hasI = true ↔ 'i' ∈ List.take (i + 1) s.toLower.data := by
    -- First, establish what the character at position i is
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'a' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    -- Rewrite take (i+1) as take i ++ [element at i]
    rw [List.take_succ_eq_append_getElem if_pos]
    -- Membership in append is disjunction
    rw [List.mem_append]
    -- Membership in singleton
    rw [List.mem_singleton]
    -- The character at i is 'a', not 'i'
    have h_ne : 'i' ≠ 'a' := by decide
    rw [h_char]
    -- So 'i' = 'a' is false
    simp only [h_ne, or_false]
    -- Now it's just the original invariant
    exact invariant_hasI_inv

theorem goal_3
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'a')
    : hasO = true ↔ 'o' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'a' := by
      simp [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    rw [List.mem_singleton]
    rw [h_char]
    have h_neq : 'o' ≠ 'a' := by decide
    simp only [h_neq, or_false]
    exact invariant_hasO_inv

theorem goal_4
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'a')
    : hasU = true ↔ 'u' ∈ List.take (i + 1) s.toLower.data := by
    have h_elem : s.toLower.data[i] = 'a' := by
      have h_some : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
      simp [h_some, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_ne : 'u' ≠ 'a' := by decide
    rw [h_elem]
    simp [h_ne]
    exact invariant_hasU_inv

theorem goal_5
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'e')
    : hasA = true ↔ 'a' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_getElem : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      rw [List.getElem?_eq_getElem if_pos]
      simp [Option.getD_some]
    have h_char_eq : s.toLower.data[i] = 'e' := by
      rw [← h_getElem]
      exact if_pos_1
    have h_ne : 'a' ≠ 'e' := by decide
    have h_not_a : ¬('a' = s.toLower.data[i]) := by
      rw [h_char_eq]
      exact h_ne
    simp only [h_not_a, or_false]
    exact invariant_hasA_inv

theorem goal_6
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'e')
    : 'e' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    apply Or.inr
    rw [List.mem_singleton]
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    simp only [h_getElem, Option.getD_some] at if_pos_1
    exact if_pos_1.symm

theorem goal_7
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'e')
    : hasI = true ↔ 'i' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'e' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    constructor
    · intro h
      left
      exact invariant_hasI_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasI_inv.mpr h_left
      | inr h_right =>
        rw [h_char] at h_right
        simp at h_right

theorem goal_8
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'e')
    : hasO = true ↔ 'o' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'e' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_ne : 'o' ≠ 'e' := by decide
    rw [h_char]
    simp only [h_ne, or_false]
    exact invariant_hasO_inv

theorem goal_9
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'e')
    : hasU = true ↔ 'u' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    rw [List.mem_singleton]
    have h_char : s.toLower.data[i] = 'e' := by
      have h_eq : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
      simp only [h_eq, Option.getD_some] at if_pos_1
      exact if_pos_1
    constructor
    · intro h
      left
      exact invariant_hasU_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasU_inv.mpr h_left
      | inr h_right =>
        rw [h_char] at h_right
        simp at h_right

theorem goal_10
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'i')
    : hasA = true ↔ 'a' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_getD : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      simp [List.getElem?_eq_getElem if_pos, Option.getD_some]
    have h_char : s.toLower.data[i] = 'i' := by
      rw [← h_getD]
      exact if_pos_1
    rw [h_char]
    constructor
    · intro h
      left
      exact invariant_hasA_inv.mp h
    · intro h
      cases h with
      | inl h_mem => exact invariant_hasA_inv.mpr h_mem
      | inr h_eq => simp at h_eq

theorem goal_11
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'i')
    : hasE = true ↔ 'e' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'i' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    rw [h_char]
    have h_ne : 'e' ≠ 'i' := by decide
    simp only [h_ne, or_false]
    exact invariant_hasE_inv

theorem goal_12
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'i')
    : 'i' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    right
    rw [List.mem_singleton]
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    simp only [h_getElem, Option.getD_some] at if_pos_1
    exact if_pos_1.symm

theorem goal_13
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'i')
    : hasO = true ↔ 'o' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'i' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_not_o : 'o' ≠ 'i' := by decide
    simp only [h_char, h_not_o, or_false]
    exact invariant_hasO_inv

theorem goal_14
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'i')
    : hasU = true ↔ 'u' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      simp [List.getElem?_eq_getElem if_pos]
    have h_char_eq : s.toLower.data[i] = 'i' := by
      rw [← h_getElem]
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_ne : 'u' ≠ 'i' := by decide
    constructor
    · intro h
      left
      exact invariant_hasU_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasU_inv.mpr h_left
      | inr h_right => 
        rw [h_char_eq] at h_right
        exact absurd h_right h_ne

theorem goal_15
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'o')
    : hasA = true ↔ 'a' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'o' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    rw [h_char]
    have h_ne : 'a' ≠ 'o' := by decide
    simp only [h_ne, or_false]
    exact invariant_hasA_inv

theorem goal_16
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'o')
    : hasE = true ↔ 'e' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'o' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    rw [h_char]
    simp only [invariant_hasE_inv]
    constructor
    · intro h
      left
      exact h
    · intro h
      cases h with
      | inl h => exact h
      | inr h => exact absurd h (by decide)

theorem goal_17
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'o')
    : hasI = true ↔ 'i' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'o' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_ne : 'i' ≠ 'o' := by decide
    rw [h_char]
    constructor
    · intro h
      left
      exact invariant_hasI_inv.mp h
    · intro h
      cases h with
      | inl h_mem => exact invariant_hasI_inv.mpr h_mem
      | inr h_eq => exact absurd h_eq h_ne

theorem goal_18
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'o')
    : 'o' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    right
    rw [List.mem_singleton]
    have h1 : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    simp only [h1, Option.getD_some] at if_pos_1
    exact if_pos_1.symm

theorem goal_19
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'o')
    : hasU = true ↔ 'u' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'o' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [h_char]
    rw [List.mem_append, List.mem_singleton]
    have h_ne : 'u' ≠ 'o' := by decide
    simp only [h_ne, or_false]
    exact invariant_hasU_inv

theorem goal_20
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'u')
    : hasA = true ↔ 'a' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'u' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    constructor
    · intro h
      left
      exact invariant_hasA_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasA_inv.mpr h_left
      | inr h_right => 
        rw [h_char] at h_right
        exact absurd h_right (by decide)

theorem goal_21
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'u')
    : hasE = true ↔ 'e' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'u' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    rw [h_char]
    simp only [invariant_hasE_inv]
    constructor
    · intro h
      left
      exact h
    · intro h
      cases h with
      | inl h => exact h
      | inr h => exact absurd h (by decide)

theorem goal_22
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'u')
    : hasI = true ↔ 'i' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'u' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_ne : 'i' ≠ 'u' := by decide
    rw [h_char]
    simp only [h_ne, or_false]
    exact invariant_hasI_inv

theorem goal_23
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'u')
    : hasO = true ↔ 'o' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_getElem : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      simp [List.getElem?_eq_getElem if_pos]
    have h_char : s.toLower.data[i] = 'u' := by
      rw [← h_getElem]
      exact if_pos_1
    rw [h_char]
    constructor
    · intro h
      left
      exact invariant_hasO_inv.mp h
    · intro h
      cases h with
      | inl h_mem => exact invariant_hasO_inv.mpr h_mem
      | inr h_eq => exact absurd h_eq (by decide)

theorem goal_24
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_pos_1 : s.toLower.data[i]?.getD 'A' = 'u')
    : 'u' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_char : s.toLower.data[i] = 'u' := by
      simp only [h_getElem, Option.getD_some] at if_pos_1
      exact if_pos_1
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    right
    rw [List.mem_singleton]
    exact h_char.symm

theorem goal_25
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_neg_4 : ¬s.toLower.data[i]?.getD 'A' = 'u')
    : hasA = true ↔ 'a' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_getD : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by simp [h_getElem, Option.getD_some]
    have h_not_a : s.toLower.data[i] ≠ 'a' := by
      intro h_eq
      rw [h_getD] at if_neg
      exact if_neg h_eq
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    constructor
    · intro h_hasA
      left
      exact invariant_hasA_inv.mp h_hasA
    · intro h_mem
      cases h_mem with
      | inl h_in_take =>
        exact invariant_hasA_inv.mpr h_in_take
      | inr h_eq =>
        exfalso
        exact h_not_a h_eq.symm

theorem goal_26
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_neg_4 : ¬s.toLower.data[i]?.getD 'A' = 'u')
    : hasE = true ↔ 'e' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]? = some s.toLower.data[i] := List.getElem?_eq_getElem if_pos
    have h_getD : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by simp [h_getElem]
    have h_not_e : s.toLower.data[i] ≠ 'e' := by
      intro heq
      rw [h_getD] at if_neg_1
      exact if_neg_1 heq
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append]
    rw [List.mem_singleton]
    constructor
    · intro h
      left
      exact invariant_hasE_inv.mp h
    · intro h
      cases h with
      | inl h_in_take => exact invariant_hasE_inv.mpr h_in_take
      | inr h_eq => exact absurd h_eq.symm h_not_e

theorem goal_27
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_neg_4 : ¬s.toLower.data[i]?.getD 'A' = 'u')
    : hasI = true ↔ 'i' ∈ List.take (i + 1) s.toLower.data := by
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    have h_getD : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      simp [List.getElem?_eq_getElem if_pos]
    have h_not_i : s.toLower.data[i] ≠ 'i' := by
      intro h
      apply if_neg_2
      rw [h_getD, h]
    constructor
    · intro h
      left
      exact invariant_hasI_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasI_inv.mpr h_left
      | inr h_right => exact absurd h_right.symm h_not_i

theorem goal_28
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_neg_4 : ¬s.toLower.data[i]?.getD 'A' = 'u')
    : hasO = true ↔ 'o' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      simp [List.getElem?_eq_getElem if_pos, Option.getD_some]
    have h_not_o : s.toLower.data[i] ≠ 'o' := by
      intro h_eq
      rw [h_eq] at h_getElem
      exact if_neg_3 h_getElem
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    constructor
    · intro h
      left
      exact invariant_hasO_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasO_inv.mpr h_left
      | inr h_right => exact absurd h_right.symm h_not_o

theorem goal_29
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (if_pos : i < s.toLower.data.length)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (if_neg : ¬s.toLower.data[i]?.getD 'A' = 'a')
    (if_neg_1 : ¬s.toLower.data[i]?.getD 'A' = 'e')
    (if_neg_2 : ¬s.toLower.data[i]?.getD 'A' = 'i')
    (if_neg_3 : ¬s.toLower.data[i]?.getD 'A' = 'o')
    (if_neg_4 : ¬s.toLower.data[i]?.getD 'A' = 'u')
    : hasU = true ↔ 'u' ∈ List.take (i + 1) s.toLower.data := by
    have h_getElem : s.toLower.data[i]?.getD 'A' = s.toLower.data[i] := by
      simp [List.getElem?_eq_getElem if_pos]
    have h_not_u : s.toLower.data[i] ≠ 'u' := by
      intro h
      apply if_neg_4
      rw [h_getElem, h]
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.mem_append, List.mem_singleton]
    constructor
    · intro h
      left
      exact invariant_hasU_inv.mp h
    · intro h
      cases h with
      | inl h_left => exact invariant_hasU_inv.mpr h_left
      | inr h_right => exact absurd h_right.symm h_not_u

theorem goal_30_0
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : hasA = i_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_1
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : hasE = i_2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_2
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : hasI = i_3 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_3
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : hasO = i_4 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_4
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : hasU = i_5 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_5
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : i_1 = true ↔ 'a' ∈ s.toLower.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_6
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : i_2 = true ↔ 'e' ∈ s.toLower.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_7
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : i_3 = true ↔ 'i' ∈ s.toLower.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_8
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : i_4 = true ↔ 'o' ∈ s.toLower.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_9
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data)
    (h_i4_iff : i_4 = true ↔ 'o' ∈ s.toLower.data)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : i_5 = true ↔ 'u' ∈ s.toLower.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_10
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data)
    (h_i4_iff : i_4 = true ↔ 'o' ∈ s.toLower.data)
    (h_i5_iff : i_5 = true ↔ 'u' ∈ s.toLower.data)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    : (((i_1 = true ∧ i_2 = true) ∧ i_3 = true) ∧ i_4 = true) ∧ i_5 = true ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_11
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data)
    (h_i4_iff : i_4 = true ↔ 'o' ∈ s.toLower.data)
    (h_i5_iff : i_5 = true ↔ 'u' ∈ s.toLower.data)
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    (h_and_true_iff : (((i_1 = true ∧ i_2 = true) ∧ i_3 = true) ∧ i_4 = true) ∧ i_5 = true ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true)
    : 'a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_12
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data)
    (h_i4_iff : i_4 = true ↔ 'o' ∈ s.toLower.data)
    (h_i5_iff : i_5 = true ↔ 'u' ∈ s.toLower.data)
    (h_all_vowels_mem : 'a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true)
    (h_vowels_def : vowels = ['a', 'e', 'i', 'o', 'u'])
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    (h_and_true_iff : (((i_1 = true ∧ i_2 = true) ∧ i_3 = true) ∧ i_4 = true) ∧ i_5 = true ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true)
    : (∀ x ∈ vowels, x ∈ s.toLower.data) ↔ 'a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30_13
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    (h_hasA_eq : hasA = i_1)
    (h_hasE_eq : hasE = i_2)
    (h_hasI_eq : hasI = i_3)
    (h_hasO_eq : hasO = i_4)
    (h_hasU_eq : hasU = i_5)
    (h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data)
    (h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data)
    (h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data)
    (h_i4_iff : i_4 = true ↔ 'o' ∈ s.toLower.data)
    (h_i5_iff : i_5 = true ↔ 'u' ∈ s.toLower.data)
    (h_all_vowels_mem : 'a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true)
    (h_vowels_def : vowels = ['a', 'e', 'i', 'o', 'u'])
    (h_take_full : s.toLower.data.length ≤ i)
    (h_toList_eq_data : True)
    (h_and_true_iff : (((i_1 = true ∧ i_2 = true) ∧ i_3 = true) ∧ i_4 = true) ∧ i_5 = true ↔ i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true)
    (h_vowels_all_unfold : (∀ x ∈ vowels, x ∈ s.toLower.data) ↔ 'a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data)
    (h_result_iff : (((i_1 = true ∧ i_2 = true) ∧ i_3 = true) ∧ i_4 = true) ∧ i_5 = true ↔ ∀ x ∈ vowels, x ∈ s.toLower.data)
    : (i_1 && i_2 && i_3 && i_4 && i_5) = vowels.all fun v ↦ decide (v ∈ s.toLower.data) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_30
    (s : String)
    (require_1 : precondition s)
    (hasA : Bool)
    (hasE : Bool)
    (hasI : Bool)
    (hasO : Bool)
    (hasU : Bool)
    (i : ℕ)
    (a_1 : i ≤ s.toLower.data.length)
    (done_1 : i = s.toLower.data.length)
    (i_1 : Bool)
    (i_2 : Bool)
    (i_3 : Bool)
    (i_4 : Bool)
    (i_5 : Bool)
    (i_6 : ℕ)
    (a : True)
    (invariant_hasA_inv : hasA = true ↔ 'a' ∈ List.take i s.toLower.data)
    (invariant_hasE_inv : hasE = true ↔ 'e' ∈ List.take i s.toLower.data)
    (invariant_hasI_inv : hasI = true ↔ 'i' ∈ List.take i s.toLower.data)
    (invariant_hasO_inv : hasO = true ↔ 'o' ∈ List.take i s.toLower.data)
    (invariant_hasU_inv : hasU = true ↔ 'u' ∈ List.take i s.toLower.data)
    (i_7 : hasA = i_1 ∧ hasE = i_2 ∧ hasI = i_3 ∧ hasO = i_4 ∧ hasU = i_5 ∧ i = i_6)
    : postcondition s (i_1 && i_2 && i_3 && i_4 && i_5) := by
    have h_take_full : List.take i s.toLower.data = s.toLower.data := by (try simp at *; expose_names); exact (Nat.le_of_eq (id (Eq.symm done_1))); done
    have h_toList_eq_data : s.toLower.toList = s.toLower.data := by (try simp at *; expose_names); exact (rfl); done
    have h_hasA_eq : hasA = i_1 := by (try simp at *; expose_names); exact (goal_30_0 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_take_full h_toList_eq_data); done
    have h_hasE_eq : hasE = i_2 := by (try simp at *; expose_names); exact (goal_30_1 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_take_full h_toList_eq_data); done
    have h_hasI_eq : hasI = i_3 := by (try simp at *; expose_names); exact (goal_30_2 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_take_full h_toList_eq_data); done
    have h_hasO_eq : hasO = i_4 := by (try simp at *; expose_names); exact (goal_30_3 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_take_full h_toList_eq_data); done
    have h_hasU_eq : hasU = i_5 := by (try simp at *; expose_names); exact (goal_30_4 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_take_full h_toList_eq_data); done
    have h_i1_iff : i_1 = true ↔ 'a' ∈ s.toLower.data := by (try simp at *; expose_names); exact (goal_30_5 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_take_full h_toList_eq_data); done
    have h_i2_iff : i_2 = true ↔ 'e' ∈ s.toLower.data := by (try simp at *; expose_names); exact (goal_30_6 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_take_full h_toList_eq_data); done
    have h_i3_iff : i_3 = true ↔ 'i' ∈ s.toLower.data := by (try simp at *; expose_names); exact (goal_30_7 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_take_full h_toList_eq_data); done
    have h_i4_iff : i_4 = true ↔ 'o' ∈ s.toLower.data := by (try simp at *; expose_names); exact (goal_30_8 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_i3_iff h_take_full h_toList_eq_data); done
    have h_i5_iff : i_5 = true ↔ 'u' ∈ s.toLower.data := by (try simp at *; expose_names); exact (goal_30_9 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_i3_iff h_i4_iff h_take_full h_toList_eq_data); done
    have h_and_true_iff : (i_1 && i_2 && i_3 && i_4 && i_5) = true ↔ (i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true) := by (try simp at *; expose_names); exact (goal_30_10 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_i3_iff h_i4_iff h_i5_iff h_take_full h_toList_eq_data); done
    have h_all_vowels_mem : ('a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data) ↔ (i_1 = true ∧ i_2 = true ∧ i_3 = true ∧ i_4 = true ∧ i_5 = true) := by (try simp at *; expose_names); exact (goal_30_11 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_i3_iff h_i4_iff h_i5_iff h_take_full h_toList_eq_data h_and_true_iff); done
    have h_vowels_def : vowels = ['a', 'e', 'i', 'o', 'u'] := by (try simp at *; expose_names); exact (rfl); done
    have h_vowels_all_unfold : vowels.all (fun v => v ∈ s.toLower.toList) = true ↔ ('a' ∈ s.toLower.data ∧ 'e' ∈ s.toLower.data ∧ 'i' ∈ s.toLower.data ∧ 'o' ∈ s.toLower.data ∧ 'u' ∈ s.toLower.data) := by (try simp at *; expose_names); exact (goal_30_12 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_i3_iff h_i4_iff h_i5_iff h_all_vowels_mem h_vowels_def h_take_full h_toList_eq_data h_and_true_iff); done
    have h_result_iff : (i_1 && i_2 && i_3 && i_4 && i_5) = true ↔ vowels.all (fun v => v ∈ s.toLower.toList) = true := by (try simp at *; expose_names); exact ((iff_congr (id (Iff.symm h_and_true_iff)) (id (Iff.symm h_vowels_all_unfold))).mp (id (Iff.symm h_all_vowels_mem))); done
    have h_bool_eq_of_iff_true : (i_1 && i_2 && i_3 && i_4 && i_5) = vowels.all (fun v => v ∈ s.toLower.toList) := by (try simp at *; expose_names); exact (goal_30_13 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7 h_hasA_eq h_hasE_eq h_hasI_eq h_hasO_eq h_hasU_eq h_i1_iff h_i2_iff h_i3_iff h_i4_iff h_i5_iff h_all_vowels_mem h_vowels_def h_take_full h_toList_eq_data h_and_true_iff h_vowels_all_unfold h_result_iff); done
    unfold postcondition
    rw [h_toList_eq_data]
    exact h_bool_eq_of_iff_true


prove_correct allVowels by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_pos_1)
  exact (goal_1 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_pos_1)
  exact (goal_2 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_pos_1)
  exact (goal_3 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_pos_1)
  exact (goal_4 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_pos_1)
  exact (goal_5 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_pos_1)
  exact (goal_6 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_pos_1)
  exact (goal_7 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_pos_1)
  exact (goal_8 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_pos_1)
  exact (goal_9 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_pos_1)
  exact (goal_10 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_pos_1)
  exact (goal_11 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_pos_1)
  exact (goal_12 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_pos_1)
  exact (goal_13 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_pos_1)
  exact (goal_14 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_pos_1)
  exact (goal_15 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_pos_1)
  exact (goal_16 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_pos_1)
  exact (goal_17 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_pos_1)
  exact (goal_18 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_pos_1)
  exact (goal_19 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_pos_1)
  exact (goal_20 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_21 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_22 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_23 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_24 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_25 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_26 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_27 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_28 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_29 s require_1 hasA hasE hasI hasO hasU i a_1 if_pos a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_30 s require_1 hasA hasE hasI hasO hasU i a_1 done_1 i_1 i_2 i_3 i_4 i_5 i_6 a invariant_hasA_inv invariant_hasE_inv invariant_hasI_inv invariant_hasO_inv invariant_hasU_inv i_7)
end Proof
