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
    copy: Replace a segment of a destination array with a segment from a source array.
    Natural language breakdown:
    1. Inputs are two arrays of integers: src and dest.
    2. We are given starting indices sStart (into src) and dStart (into dest), and a length len.
    3. The output is a new array result with the same size as dest.
    4. Only the segment of dest from indices dStart .. dStart+len-1 is replaced.
    5. For every offset i with 0 ≤ i < len, result[dStart+i] equals src[sStart+i].
    6. For indices j < dStart, result[j] equals dest[j] (prefix unchanged).
    7. For indices j with dStart+len ≤ j < dest.size, result[j] equals dest[j] (suffix unchanged).
    8. The operation is only required to behave this way when src.size ≥ sStart + len and dest.size ≥ dStart + len.
-/

section Specs
-- Preconditions from the problem statement.
-- These ensure that the copied source slice and the overwritten destination segment are in-bounds.
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  sStart + len ≤ src.size ∧ dStart + len ≤ dest.size

-- Postcondition: size preserved and elementwise behavior is specified by cases.
-- The specification is extensional over indices < dest.size.
-- We inline the segment-membership test so Lean can synthesize its decidability.
def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
    (result : Array Int) : Prop :=
  result.size = dest.size ∧
  (∀ j : Nat, j < dest.size →
    (if h : (dStart ≤ j ∧ j < dStart + len) then
      result[j]! = src[sStart + (j - dStart)]!
    else
      result[j]! = dest[j]!))
end Specs

section Impl
method copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
  return (result : Array Int)
  require precondition src sStart dest dStart len
  ensures postcondition src sStart dest dStart len result
  do
    let mut result := dest
    let mut i : Nat := 0
    while i < len
      -- i is always within [0, len]; gives i = len on exit.
      invariant "inv_i_le_len" i ≤ len
      -- Result array size is preserved by set!.
      invariant "inv_size_preserved" result.size = dest.size
      -- All already-written positions in the destination segment agree with src.
      invariant "inv_copied_prefix" (∀ k : Nat, k < i → result[dStart + k]! = src[sStart + k]!)
      -- Positions outside the overwritten segment remain equal to dest.
      invariant "inv_outside_unchanged" (∀ j : Nat, j < dest.size → (j < dStart ∨ dStart + len ≤ j) → result[j]! = dest[j]!)
      done_with (i = len)
    do
      result := result.set! (dStart + i) (src[sStart + i]!)
      i := i + 1
    return result
end Impl

section TestCases
-- Test case 1: Provided example: replace dest[3..4] with src[1..2]
def test1_src : Array Int := #[10, 20, 30, 40, 50]
def test1_sStart : Nat := 1
def test1_dest : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_dStart : Nat := 3
def test1_len : Nat := 2
def test1_Expected : Array Int := #[1, 2, 3, 20, 30, 6]

-- Test case 2: Provided example: middle replacement length 3
def test2_src : Array Int := #[5, 6, 7, 8]
def test2_sStart : Nat := 0
def test2_dest : Array Int := #[9, 9, 9, 9, 9]
def test2_dStart : Nat := 1
def test2_len : Nat := 3
def test2_Expected : Array Int := #[9, 5, 6, 7, 9]

-- Test case 3: Provided example: len = 0 means unchanged
def test3_src : Array Int := #[100, 200]
def test3_sStart : Nat := 0
def test3_dest : Array Int := #[1, 2, 3]
def test3_dStart : Nat := 1
def test3_len : Nat := 0
def test3_Expected : Array Int := #[1, 2, 3]

-- Test case 4: Provided example: full overwrite
def test4_src : Array Int := #[10, 20, 30, 40, 50]
def test4_sStart : Nat := 0
def test4_dest : Array Int := #[0, 0, 0, 0, 0]
def test4_dStart : Nat := 0
def test4_len : Nat := 5
def test4_Expected : Array Int := #[10, 20, 30, 40, 50]

-- Test case 5: Provided example: overwrite last two positions using src starting at 2
def test5_src : Array Int := #[7, 8, 9, 10]
def test5_sStart : Nat := 2
def test5_dest : Array Int := #[1, 2, 3, 4, 5, 6]
def test5_dStart : Nat := 4
def test5_len : Nat := 2
def test5_Expected : Array Int := #[1, 2, 3, 4, 9, 10]

-- Test case 6: Edge: dest is empty, len = 0, result must be empty
def test6_src : Array Int := #[1, 2, 3]
def test6_sStart : Nat := 0
def test6_dest : Array Int := #[]
def test6_dStart : Nat := 0
def test6_len : Nat := 0
def test6_Expected : Array Int := #[]

-- Test case 7: Replace prefix of dest with a slice from src
def test7_src : Array Int := #[11, 12, 13, 14]
def test7_sStart : Nat := 1
def test7_dest : Array Int := #[0, 1, 2, 3, 4]
def test7_dStart : Nat := 0
def test7_len : Nat := 3
def test7_Expected : Array Int := #[12, 13, 14, 3, 4]

-- Test case 8: Replace suffix (dStart at last index), len = 1
def test8_src : Array Int := #[99, 100]
def test8_sStart : Nat := 1
def test8_dest : Array Int := #[5, 6, 7]
def test8_dStart : Nat := 2
def test8_len : Nat := 1
def test8_Expected : Array Int := #[5, 6, 100]

-- Test case 9: No-op in the middle with len = 0 (different starts)
def test9_src : Array Int := #[3, 4, 5]
def test9_sStart : Nat := 2
def test9_dest : Array Int := #[8, 9]
def test9_dStart : Nat := 1
def test9_len : Nat := 0
def test9_Expected : Array Int := #[8, 9]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((copy test1_src test1_sStart test1_dest test1_dStart test1_len).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((copy test2_src test2_sStart test2_dest test2_dStart test2_len).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((copy test3_src test3_sStart test3_dest test3_dStart test3_len).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((copy test4_src test4_sStart test4_dest test4_dStart test4_len).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((copy test5_src test5_sStart test5_dest test5_dStart test5_len).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((copy test6_src test6_sStart test6_dest test6_dStart test6_len).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((copy test7_src test7_sStart test7_dest test7_dStart test7_len).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((copy test8_src test8_sStart test8_dest test8_dStart test8_len).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((copy test9_src test9_sStart test9_dest test9_dStart test9_len).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for copy
prove_precondition_decidable_for copy
prove_postcondition_decidable_for copy
derive_tester_for copy
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Nat)
    let arg_2 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_3 ← Plausible.SampleableExt.interpSample (Nat)
    let arg_4 ← Plausible.SampleableExt.interpSample (Nat)
    let res := copyTester arg_0 arg_1 arg_2 arg_3 arg_4
    pure ((arg_0, arg_1, arg_2, arg_3, arg_4), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt


section Proof
set_option maxHeartbeats 10000000


-- prove_correct copy by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (require_1 : precondition src sStart dest dStart len)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_size_preserved : result.size = dest.size)
    (if_pos : i < len)
    (k : ℕ)
    (hk_lt_i : k < i)
    : dStart + k < result.size := by
    rcases require_1 with ⟨_hs, hd⟩
    have hkLen : k < len := Nat.lt_trans hk_lt_i if_pos
    have hdk : dStart + k < dStart + len := Nat.add_lt_add_left hkLen dStart
    have hdest : dStart + k < dest.size := lt_of_lt_of_le hdk hd
    simpa [invariant_inv_size_preserved] using hdest


theorem goal_0_1
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_copied_prefix : ∀ k < i, result[dStart + k]! = src[sStart + k]!)
    (invariant_inv_outside_unchanged : ∀ j < dest.size, j < dStart ∨ dStart + len ≤ j → result[j]! = dest[j]!)
    (if_pos : i < len)
    (k : ℕ)
    (hk : k < i + 1)
    (hk_le_i : k ≤ i)
    (hk_lt_i : k < i)
    (hdsz : dStart + k < result.size)
    (hne_ki : ¬k = i)
    : (result.setIfInBounds (dStart + i) src[sStart + i]!)[dStart + k]! = result[dStart + k]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_2
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (require_1 : precondition src sStart dest dStart len)
    (i : ℕ)
    (result : Array ℤ)
    (k : ℕ)
    : dStart + len ≤ dest.size := by
    exact require_1.2


theorem goal_0_3
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_le_len : i ≤ len)
    (invariant_inv_copied_prefix : ∀ k < i, result[dStart + k]! = src[sStart + k]!)
    (invariant_inv_outside_unchanged : ∀ j < dest.size, j < dStart ∨ dStart + len ≤ j → result[j]! = dest[j]!)
    (if_pos : i < len)
    (k : ℕ)
    (hk : k < i + 1)
    (hk_le_i : k ≤ i)
    (hk_eq_i : k = i)
    (h_dest_bound : dStart + len ≤ dest.size)
    (h_add_lt_add : i < len)
    : dStart + i < dest.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_4
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_size_preserved : result.size = dest.size)
    (invariant_inv_copied_prefix : ∀ k < i, result[dStart + k]! = src[sStart + k]!)
    (invariant_inv_outside_unchanged : ∀ j < dest.size, j < dStart ∨ dStart + len ≤ j → result[j]! = dest[j]!)
    (if_pos : i < len)
    (k : ℕ)
    (hk : k < i + 1)
    (hk_le_i : k ≤ i)
    (hk_eq_i : k = i)
    (h_dest_bound : dStart + len ≤ dest.size)
    (h_di_lt_dest : dStart + i < dest.size)
    (h_di_lt_result : dStart + i < result.size)
    (h_add_lt_add : i < len)
    : (result.setIfInBounds (dStart + i) src[sStart + i]!)[dStart + i]! = src[sStart + i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (require_1 : precondition src sStart dest dStart len)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_le_len : i ≤ len)
    (invariant_inv_size_preserved : result.size = dest.size)
    (invariant_inv_copied_prefix : ∀ k < i, result[dStart + k]! = src[sStart + k]!)
    (invariant_inv_outside_unchanged :
      ∀ j < dest.size, j < dStart ∨ dStart + len ≤ j → result[j]! = dest[j]!)
    (if_pos : i < len)
    : ∀ k < i + 1,
        (result.setIfInBounds (dStart + i) src[sStart + i]!)[dStart + k]! = src[sStart + k]! := by
  intro k hk
  have hk_le_i : k ≤ i := by (try simp at *; expose_names); exact Nat.le_of_lt_succ hk; done
  have hk_cases : k < i ∨ k = i := by (try simp at *; expose_names); exact (Nat.lt_succ_iff_lt_or_eq.mp hk); done
  cases hk_cases with
  | inl hk_lt_i =>
      have hne_ki : dStart + k ≠ dStart + i := by (try simp at *; expose_names); exact (Nat.ne_of_lt hk_lt_i); done
      have hdsz : dStart + k < result.size := by (try simp at *; expose_names); exact (goal_0_0 src sStart dest dStart len require_1 i result invariant_inv_size_preserved if_pos k hk_lt_i); done
      have hget_set_ne :
          (result.setIfInBounds (dStart + i) src[sStart + i]!)[dStart + k]! = result[dStart + k]! := by
        (try simp at *; expose_names); exact (goal_0_1 src sStart dest dStart len i result invariant_inv_copied_prefix invariant_inv_outside_unchanged if_pos k hk hk_le_i hk_lt_i hdsz hne_ki); done
      have hold : result[dStart + k]! = src[sStart + k]! := by (try simp at *; expose_names); exact (invariant_inv_copied_prefix k hk_lt_i); done
      calc
        (result.setIfInBounds (dStart + i) src[sStart + i]!)[dStart + k]! =
            result[dStart + k]! := by simpa using hget_set_ne
        _ = src[sStart + k]! := by simpa using hold
  | inr hk_eq_i =>
      have h_dest_bound : dStart + len ≤ dest.size := by (try simp at *; expose_names); exact (goal_0_2 src sStart dest dStart len require_1 i result k); done
      have h_add_lt_add : dStart + i < dStart + len := by (try simp at *; expose_names); exact (if_pos); done
      have h_di_lt_dest : dStart + i < dest.size := by (try simp at *; expose_names); exact (goal_0_3 src sStart dest dStart len i result invariant_inv_i_le_len invariant_inv_copied_prefix invariant_inv_outside_unchanged if_pos k hk hk_le_i hk_eq_i h_dest_bound h_add_lt_add); done
      have h_di_lt_result : dStart + i < result.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq h_di_lt_dest (id (Eq.symm invariant_inv_size_preserved))); done
      have hget_set_eq :
          (result.setIfInBounds (dStart + i) src[sStart + i]!)[dStart + i]! = src[sStart + i]! := by
        (try simp at *; expose_names); exact (goal_0_4 src sStart dest dStart len i result invariant_inv_size_preserved invariant_inv_copied_prefix invariant_inv_outside_unchanged if_pos k hk hk_le_i hk_eq_i h_dest_bound h_di_lt_dest h_di_lt_result h_add_lt_add); done
      simpa [hk_eq_i] using hget_set_eq

theorem goal_1
    (src : Array ℤ)
    (sStart : ℕ)
    (dest : Array ℤ)
    (dStart : ℕ)
    (len : ℕ)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_size_preserved : result.size = dest.size)
    (invariant_inv_copied_prefix : ∀ k < i, result[dStart + k]! = src[sStart + k]!)
    (invariant_inv_outside_unchanged : ∀ j < dest.size, j < dStart ∨ dStart + len ≤ j → result[j]! = dest[j]!)
    (done_1 : i = len)
    (i_1 : ℕ)
    (result_1 : Array ℤ)
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition src sStart dest dStart len result_1 := by
    rcases i_2 with ⟨hi, hres⟩
    subst hi
    -- rewrite invariants to talk about `result_1`
    have hsize : result_1.size = dest.size := by
      simpa [hres] using invariant_inv_size_preserved
    constructor
    · exact hsize
    · intro j hj
      -- prove the conditional elementwise property by cases on membership in the overwrite segment
      by_cases h : (dStart ≤ j ∧ j < dStart + len)
      · -- inside segment: use copied-prefix invariant with k = j - dStart
        have hdj : dStart ≤ j := h.1
        have hjlt : j < dStart + len := h.2
        have hklt : j - dStart < len := by
          exact Nat.sub_lt_left_of_lt_add hdj hjlt
        have hklt' : j - dStart < i := by
          -- i = len
          simpa [done_1] using hklt
        have hcopy : result[dStart + (j - dStart)]! = src[sStart + (j - dStart)]! :=
          invariant_inv_copied_prefix (j - dStart) hklt'
        have hadd : dStart + (j - dStart) = j := Nat.add_sub_cancel' hdj
        -- assemble
        simp [postcondition, h, hres, hadd] at *
        -- goal is now exactly `result_1[j]! = src[sStart + (j - dStart)]!`
        simpa [hres, hadd] using hcopy
      · -- outside segment: use outside-unchanged invariant
        have hout : j < dStart ∨ dStart + len ≤ j := by
          by_cases hd : dStart ≤ j
          · -- must be ¬ j < dStart, hence not (j < dStart + len), so dStart+len ≤ j
            have : ¬ j < dStart + len := by
              intro hjlt
              exact h ⟨hd, hjlt⟩
            exact Or.inr (Nat.le_of_not_lt this)
          · exact Or.inl (Nat.lt_of_not_ge hd)
        have hunch : result[j]! = dest[j]! := invariant_inv_outside_unchanged j hj hout
        simp [postcondition, h, hres] at *
        simpa [hres] using hunch


prove_correct copy by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 src sStart dest dStart len require_1 i result invariant_inv_i_le_len invariant_inv_size_preserved invariant_inv_copied_prefix invariant_inv_outside_unchanged if_pos)
  exact (goal_1 src sStart dest dStart len i result invariant_inv_size_preserved invariant_inv_copied_prefix invariant_inv_outside_unchanged done_1 i_1 result_1 i_2)
end Proof
