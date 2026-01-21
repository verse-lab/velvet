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
    secondSmallest: find the second-smallest number in an array of integers.
    Natural language breakdown:
    1. Input is an array `s` of integers.
    2. The array has at least two elements.
    3. There exist at least two distinct values in the array.
    4. The output is an element of the array.
    5. The output is strictly larger than the smallest value present in the array.
    6. Among all values in the array that are strictly larger than the minimum, the output is the least.
    7. The input array is not modified (functional setting: result depends only on `s`).
-/

section Specs
-- Helper: membership in an Array via a bounded Nat index
-- (Using Nat indices with `arr[i]!` as required by the guidelines.)
def InArray (s : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < s.size ∧ s[i]! = x

-- Helper: x is a minimum value of the array
-- We keep this relational and computation-friendly (no finsets/min' required).
def IsMinVal (s : Array Int) (m : Int) : Prop :=
  InArray s m ∧ ∀ i : Nat, i < s.size → m ≤ s[i]!

-- Helper: x is the least value strictly above a given minimum m
-- This characterizes the second-smallest uniquely when it exists.
def IsSecondAboveMin (s : Array Int) (m : Int) (x : Int) : Prop :=
  InArray s x ∧ m < x ∧
    (∀ y : Int, InArray s y → m < y → x ≤ y)

-- Preconditions
-- 1) at least two elements
-- 2) there exist two distinct indices with different values (guarantees a strict minimum exists
--    and at least one value above it, hence a unique second-smallest).
def precondition (s : Array Int) : Prop :=
  s.size ≥ 2 ∧
  (∃ i : Nat, ∃ j : Nat,
    i < s.size ∧ j < s.size ∧ i ≠ j ∧ s[i]! ≠ s[j]!)

-- Postcondition: result is the least element strictly above the minimum element.
-- We existentially quantify the minimum value `m` to avoid committing to a specific implementation.
def postcondition (s : Array Int) (result : Int) : Prop :=
  ∃ m : Int, IsMinVal s m ∧ IsSecondAboveMin s m result
end Specs

section Impl
method secondSmallest (s : Array Int)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  -- First pass: find minimum value
  let mut minVal := s[0]!
  let mut i : Nat := 1
  while i < s.size
    -- i stays within bounds
    -- init: i=1 and precondition implies s.size ≥ 2; preserved by i := i+1
    invariant "min1_bounds" i ≤ s.size
    -- minVal is always some element seen so far
    -- init: minVal = s[0]!; preserved since updates only assign s[i]!
    invariant "min2_inArray_prefix" (∃ j : Nat, j < i ∧ s[j]! = minVal)
    -- minVal is a lower bound of all elements seen so far
    -- init: holds for prefix {0}; preserved by taking min with next element
    invariant "min3_lowerBound_prefix" (∀ j : Nat, j < i → minVal ≤ s[j]!)
  do
    if s[i]! < minVal then
      minVal := s[i]!
    i := i + 1

  -- Second pass: find minimum value strictly greater than minVal
  -- We use a "found" flag to initialize candidate safely.
  let mut found := false
  let mut secondVal := 0
  i := 0
  while i < s.size
    -- i stays within bounds
    -- init: i=0; preserved by i := i+1
    invariant "sec1_bounds" i ≤ s.size
    -- If we have found a candidate, it comes from the scanned prefix and is above minVal
    -- init: found=false; preserved since we only set secondVal := s[i]!
    invariant "sec2_candidate_from_prefix"
      (found = true → (∃ j : Nat, j < i ∧ s[j]! = secondVal ∧ minVal < secondVal))
    -- If found, secondVal is ≤ every scanned element that is strictly above minVal
    -- init: vacuous when found=false; preserved by updating to smaller candidate
    invariant "sec3_min_among_above_in_prefix"
      (found = true → (∀ j : Nat, j < i → minVal < s[j]! → secondVal ≤ s[j]!))
    -- If not found yet, no scanned element is strictly above minVal
    -- init: i=0; preserved since found becomes true at first such element
    invariant "sec4_notFound_means_none_above"
      (found = false → (∀ j : Nat, j < i → ¬ (minVal < s[j]!)))
  do
    let v := s[i]!
    if minVal < v then
      if found = false then
        secondVal := v
        found := true
      else
        if v < secondVal then
          secondVal := v
    i := i + 1

  -- By precondition, there exists a value strictly above minVal, so found must be true.
  return secondVal
end Impl

section TestCases
-- Test case 1: example from prompt
-- s = #[5, 3, 1, 4, 2] -> second-smallest is 2

def test1_s : Array Int := #[5, 3, 1, 4, 2]
def test1_Expected : Int := 2

-- Test case 2: typical mixed order

def test2_s : Array Int := #[7, 2, 5, 3]
def test2_Expected : Int := 3

-- Test case 3: exactly two elements increasing

def test3_s : Array Int := #[10, 20]
def test3_Expected : Int := 20

-- Test case 4: exactly two elements decreasing

def test4_s : Array Int := #[20, 10]
def test4_Expected : Int := 20

-- Test case 5: small array

def test5_s : Array Int := #[3, 1, 2]
def test5_Expected : Int := 2

-- Test case 6: duplicates present but still at least two distinct values; second-smallest ignores extra mins

def test6_s : Array Int := #[1, 1, 2, 2, 3]
def test6_Expected : Int := 2

-- Test case 7: includes negative values

def test7_s : Array Int := #[-5, -1, -3, 0]
def test7_Expected : Int := -3

-- Test case 8: multiple occurrences of second-smallest value

def test8_s : Array Int := #[0, 2, 2, 1]
def test8_Expected : Int := 1

-- Test case 9: large range of values

def test9_s : Array Int := #[100, 50, 75, 25, 0]
def test9_Expected : Int := 25

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 6, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((secondSmallest test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((secondSmallest test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((secondSmallest test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((secondSmallest test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((secondSmallest test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((secondSmallest test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((secondSmallest test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((secondSmallest test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((secondSmallest test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 186, Column 0
-- Message: unsolved goals
-- s : Array ℤ
-- result : ℤ
-- ⊢ Decidable (postcondition s result)
-- Line: prove_postcondition_decidable_for secondSmallest
-- [ERROR] Line 188, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for secondSmallest
-- prove_precondition_decidable_for secondSmallest
-- prove_postcondition_decidable_for secondSmallest
-- derive_tester_for secondSmallest
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
--     let res := secondSmallestTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct secondSmallest by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : Array ℤ)
    (require_1 : precondition s)
    : 1 ≤ s.size := by
  have hsize : 2 ≤ s.size := by
    simpa [precondition] using (And.left require_1)
  exact le_trans (by decide : (1 : Nat) ≤ 2) hsize

theorem goal_1
    (s : Array ℤ)
    (require_1 : precondition s)
    (i : ℕ)
    (minVal : ℤ)
    (invariant_min1_bounds : i ≤ s.size)
    (invariant_min2_inArray_prefix : ∃ j < i, s[j]! = minVal)
    (invariant_min3_lowerBound_prefix : ∀ j < i, minVal ≤ s[j]!)
    (i_1 : ℕ)
    (minVal_1 : ℤ)
    (found : Bool)
    (i_3 : ℕ)
    (secondVal : ℤ)
    (invariant_sec1_bounds : i_3 ≤ s.size)
    (invariant_sec2_candidate_from_prefix :
      found = true → ∃ j < i_3, s[j]! = secondVal ∧ minVal_1 < secondVal)
    (invariant_sec3_min_among_above_in_prefix :
      found = true → ∀ j < i_3, minVal_1 < s[j]! → secondVal ≤ s[j]!)
    (i_4 : Bool)
    (i_5 : ℕ)
    (secondVal_1 : ℤ)
    (done_1 : s.size ≤ i)
    (i_2 : i = i_1 ∧ minVal = minVal_1)
    (invariant_sec4_notFound_means_none_above :
      found = false → ∀ j < i_3, s[j]! ≤ minVal_1)
    (done_2 : s.size ≤ i_3)
    (i_6 : found = i_4 ∧ i_3 = i_5 ∧ secondVal = secondVal_1)
    : postcondition s secondVal_1 := by
  classical
  rcases i_2 with ⟨_hi_eq, hmin_eq⟩
  rcases i_6 with ⟨_hfound_eq, _hi3_eq, hsec_eq⟩

  -- minVal_1 is a global minimum
  have hIsMin_minVal1 : IsMinVal s minVal_1 := by
    have hIn : InArray s minVal_1 := by
      rcases invariant_min2_inArray_prefix with ⟨j, hj_lt_i, hj_eq⟩
      refine ⟨j, ?_, ?_⟩
      · exact Nat.lt_of_lt_of_le hj_lt_i invariant_min1_bounds
      · simpa [hmin_eq] using hj_eq
    have hLB : ∀ k : Nat, k < s.size → minVal_1 ≤ s[k]! := by
      intro k hk
      have hk_lt_i : k < i := Nat.lt_of_lt_of_le hk done_1
      have : minVal ≤ s[k]! := invariant_min3_lowerBound_prefix k hk_lt_i
      simpa [hmin_eq] using this
    exact ⟨hIn, hLB⟩

  -- existence of an element strictly above minVal_1 using the two distinct values from the precondition
  have hexists_above : ∃ j : Nat, j < s.size ∧ minVal_1 < s[j]! := by
    rcases require_1 with ⟨_hsz2, hdiff⟩
    rcases hdiff with ⟨a, b, ha, hb, _hab_ne, hab_val_ne⟩
    have hmina : minVal_1 ≤ s[a]! := (hIsMin_minVal1.2 a ha)
    have hminb : minVal_1 ≤ s[b]! := (hIsMin_minVal1.2 b hb)

    have hne_or : s[a]! ≠ minVal_1 ∨ s[b]! ≠ minVal_1 := by
      by_contra h
      have hEqA : s[a]! = minVal_1 := by
        have : ¬ s[a]! ≠ minVal_1 := by
          intro hna; exact h (Or.inl hna)
        exact not_ne_iff.mp this
      have hEqB : s[b]! = minVal_1 := by
        have : ¬ s[b]! ≠ minVal_1 := by
          intro hnb; exact h (Or.inr hnb)
        exact not_ne_iff.mp this
      exact hab_val_ne (by simpa [hEqA, hEqB])

    cases hne_or with
    | inl hA_ne =>
        refine ⟨a, ha, ?_⟩
        exact lt_of_le_of_ne hmina (Ne.symm hA_ne)
    | inr hB_ne =>
        refine ⟨b, hb, ?_⟩
        exact lt_of_le_of_ne hminb (Ne.symm hB_ne)

  -- found must be true at the end
  have hfound_true : found = true := by
    cases hfound : found with
    | false =>
        -- derive contradiction from existence of some element > minVal_1
        have hall_le : ∀ j < i_3, s[j]! ≤ minVal_1 :=
          invariant_sec4_notFound_means_none_above (by simpa [hfound])
        rcases hexists_above with ⟨j, hj_sz, hj_gt⟩
        have hj_lt_i3 : j < i_3 := Nat.lt_of_lt_of_le hj_sz done_2
        have hle : s[j]! ≤ minVal_1 := hall_le j hj_lt_i3
        have : False := (not_lt_of_ge hle) hj_gt
        exact False.elim this
    | true =>
        simpa [hfound]

  -- build IsSecondAboveMin, then rewrite secondVal = secondVal_1
  have hIsSecond : IsSecondAboveMin s minVal_1 secondVal_1 := by
    have hCand : ∃ j < i_3, s[j]! = secondVal ∧ minVal_1 < secondVal :=
      invariant_sec2_candidate_from_prefix hfound_true
    rcases hCand with ⟨j, hj_lt_i3, hj_eq, hmin_lt_sec⟩
    have hj_lt_sz : j < s.size := Nat.lt_of_lt_of_le hj_lt_i3 invariant_sec1_bounds
    have hInSecond : InArray s secondVal_1 := by
      refine ⟨j, hj_lt_sz, ?_⟩
      simpa [hsec_eq] using hj_eq
    have hmin_lt_res : minVal_1 < secondVal_1 := by
      simpa [hsec_eq] using hmin_lt_sec
    have hLeast : ∀ y : ℤ, InArray s y → minVal_1 < y → secondVal_1 ≤ y := by
      intro y hyIn hyGt
      rcases hyIn with ⟨k, hk_sz, hk_eq⟩
      have hk_lt_i3 : k < i_3 := Nat.lt_of_lt_of_le hk_sz done_2
      have hk_gt' : minVal_1 < s[k]! := by simpa [hk_eq] using hyGt
      have hsec_le : secondVal ≤ s[k]! :=
        (invariant_sec3_min_among_above_in_prefix hfound_true) k hk_lt_i3 hk_gt'
      simpa [hsec_eq, hk_eq] using hsec_le
    exact ⟨hInSecond, hmin_lt_res, hLeast⟩

  exact ⟨minVal_1, hIsMin_minVal1, hIsSecond⟩


prove_correct secondSmallest by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1)
  exact (goal_1 s require_1 i minVal invariant_min1_bounds invariant_min2_inArray_prefix invariant_min3_lowerBound_prefix i_1 minVal_1 found i_3 secondVal invariant_sec1_bounds invariant_sec2_candidate_from_prefix invariant_sec3_min_among_above_in_prefix i_4 i_5 secondVal_1 done_1 i_2 invariant_sec4_notFound_means_none_above done_2 i_6)
end Proof
