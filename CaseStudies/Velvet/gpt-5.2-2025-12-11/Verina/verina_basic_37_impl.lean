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
    findFirstOccurrence: locate the first occurrence index of a target integer in a sorted array.
    Natural language breakdown:
    1. Input is an array of integers `arr` and an integer `target`.
    2. The array is assumed to be sorted in non-decreasing order.
    3. If `target` appears in `arr`, return the smallest index (0-based) where `arr[i] = target`.
    4. If `target` does not appear in `arr`, return -1.
    5. The method does not modify the array (arrays are immutable values in this setting).
-/

section Specs
-- Helper: array is sorted in non-decreasing order.
-- Uses natural-number indices and safe access `arr[i]!` guarded by bounds.
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: `target` occurs in `arr` at some index.
def occurs (arr : Array Int) (target : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = target

-- Helper: `idx : Int` corresponds to a valid Nat index.
def intIndexInBounds (arr : Array Int) (idx : Int) : Prop :=
  0 ≤ idx ∧ (idx.toNat) < arr.size

-- Precondition: input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedNonDecreasing arr

-- Postcondition: returns -1 iff target absent; otherwise returns the first index of target.
-- Characterization is via bounds + pointwise conditions and minimality.
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ↔ ¬ occurs arr target) ∧
  (result ≠ (-1) →
    intIndexInBounds arr result ∧
    arr[result.toNat]! = target ∧
    (∀ (j : Nat), j < result.toNat → arr[j]! ≠ target))
end Specs

section Impl
method findFirstOccurrence (arr : Array Int) (target : Int) return (result : Int)
  require precondition arr target
  ensures postcondition arr target result
  do
  let mut i : Nat := 0
  let mut ans : Int := (-1)
  let mut found : Bool := false

  while i < arr.size ∧ found = false
    -- Invariant: loop index stays within array bounds.
    -- Init: i=0. Preserved: i increases only under guard i < arr.size.
    invariant "inv_i_bounds" i ≤ arr.size

    -- Invariant: found/ans are consistent: while running we have not found and ans is still -1.
    -- Init: found=false and ans=-1. Preserved: loop guard enforces found=false; ans changes only when found becomes true.
    invariant "inv_running_ans" (found = false → ans = (-1))

    -- Invariant: if ans is set, it witnesses a first occurrence (index in bounds, arr[ans]=target, and no earlier target).
    -- Init: ans=-1. Preserved: only assignment sets ans := ofNat i exactly when x=target.
    invariant "inv_ans_characterization"
      (ans = (-1) ∨
        (intIndexInBounds arr ans ∧
         arr[ans.toNat]! = target ∧
         (∀ (j : Nat), j < ans.toNat → arr[j]! ≠ target)))

    -- Invariant: all indices strictly before i have been ruled out as a match.
    -- Init: vacuous for i=0. Preserved: we advance i only when current x < target, hence x ≠ target.
    invariant "inv_prefix_ne_target" ∀ (j : Nat), j < i → arr[j]! ≠ target

    -- Invariant: if still searching, then all examined elements are strictly less than target.
    -- Used with sortedness to conclude absence when stopping early due to x > target.
    invariant "inv_prefix_lt_target" (found = false → ∀ (j : Nat), j < i → arr[j]! < target)

    -- Invariant: if we have stopped with no answer, then we stopped early at some in-bounds i with arr[i] > target.
    -- This matches the exit reasoning needed to rule out later indices using sortedness.
    invariant "inv_found_noans_implies_gt"
      ((found = true ∧ ans = (-1)) → i < arr.size ∧ arr[i]! > target)

    done_with (i ≥ arr.size ∨ found = true)
  do
    let x := arr[i]!
    if x = target then
      ans := (Int.ofNat i)
      found := true
    else
      if x > target then
        found := true
      else
        i := i + 1

  return ans
end Impl

section TestCases
-- Test case 1: example with duplicates; first occurrence should be index 1
-- From prompt tests

def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_target : Int := 2
def test1_Expected : Int := 1

-- Test case 2: target absent (larger than all)

def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_target : Int := 6
def test2_Expected : Int := (-1)

-- Test case 3: target present at first index

def test3_arr : Array Int := #[1, 2, 3, 4, 5]
def test3_target : Int := 1
def test3_Expected : Int := 0

-- Test case 4: target present at last index

def test4_arr : Array Int := #[1, 2, 3, 4, 5]
def test4_target : Int := 5
def test4_Expected : Int := 4

-- Test case 5: target absent (smaller than all)

def test5_arr : Array Int := #[1, 2, 3, 4, 5]
def test5_target : Int := 0
def test5_Expected : Int := (-1)

-- Test case 6: empty array

def test6_arr : Array Int := #[]
def test6_target : Int := 10
def test6_Expected : Int := (-1)

-- Test case 7: all elements equal to target

def test7_arr : Array Int := #[7, 7, 7]
def test7_target : Int := 7
def test7_Expected : Int := 0

-- Test case 8: negative numbers with duplicates

def test8_arr : Array Int := #[-5, -3, -3, 0, 2]
def test8_target : Int := (-3)
def test8_Expected : Int := 1

-- Test case 9: single-element array, absent

def test9_arr : Array Int := #[4]
def test9_target : Int := 3
def test9_Expected : Int := (-1)

-- Recommend to validate: 1, 6, 8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findFirstOccurrence test1_arr test1_target).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findFirstOccurrence test2_arr test2_target).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findFirstOccurrence test3_arr test3_target).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findFirstOccurrence test4_arr test4_target).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findFirstOccurrence test5_arr test5_target).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findFirstOccurrence test6_arr test6_target).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findFirstOccurrence test7_arr test7_target).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findFirstOccurrence test8_arr test8_target).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((findFirstOccurrence test9_arr test9_target).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for findFirstOccurrence
prove_precondition_decidable_for findFirstOccurrence
prove_postcondition_decidable_for findFirstOccurrence
derive_tester_for findFirstOccurrence
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := findFirstOccurrenceTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct findFirstOccurrence by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (a : i < arr.size)
    (a_1 : found = false)
    (if_pos : arr[i]! = target)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    : intIndexInBounds arr ↑i ∧ arr[i]! = target ∧ ∀ j < i, ¬arr[j]! = target := by
  constructor
  · -- intIndexInBounds arr (↑i)
    unfold intIndexInBounds
    constructor
    · simpa using (Int.ofNat_nonneg i)
    · simpa [Int.toNat_ofNat] using a
  · constructor
    · exact if_pos
    · exact invariant_inv_prefix_ne_target

theorem goal_1_0
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    (done_1 : arr.size ≤ i ∨ found = true)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    : ans = i_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_1
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    (done_1 : arr.size ≤ i ∨ found = true)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    (hans : ans = i_1)
    (hi1s : i_1 = ans)
    (hi1neg : i_1 = -1)
    : ans = -1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_2
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    (hans : ans = i_1)
    (hi1s : i_1 = ans)
    (hi1neg : i_1 = -1)
    (hansneg : ans = -1)
    (hfound : found = true)
    (hgt : i < arr.size ∧ target < arr[i]!)
    (hsorted : isSortedNonDecreasing arr)
    (k : ℕ)
    (hk : k < arr.size)
    (hik : i < k ∨ i = k ∨ k < i)
    (hklt : i ≤ k)
    : ¬arr[k]! = target := by
    have hti : target < arr[i]! := hgt.2
    have hkCases : i < k ∨ i = k := by
      exact Nat.lt_or_eq_of_le hklt
    cases hkCases with
    | inl hiklt =>
        have hikle : arr[i]! ≤ arr[k]! := hsorted i k hiklt hk
        have htk : target < arr[k]! := lt_of_lt_of_le hti hikle
        exact (Int.ne_of_lt htk).symm
    | inr hikeq =>
        subst hikeq
        exact (Int.ne_of_lt hti).symm

theorem goal_1_3
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    (done_1 : arr.size ≤ i ∨ found = true)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    (hans : ans = i_1)
    (hi1s : i_1 = ans)
    (hi1ne : ¬i_1 = -1)
    (hansne : ¬ans = -1)
    (hgood : intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    : intIndexInBounds arr i_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_4
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    (done_1 : arr.size ≤ i ∨ found = true)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    (hans : ans = i_1)
    (hi1s : i_1 = ans)
    (hi1ne : ¬i_1 = -1)
    (hansne : ¬ans = -1)
    (hgood : intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (hbounds : intIndexInBounds arr i_1)
    : arr[i_1.toNat]! = target := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (arr : Array ℤ)
    (target : ℤ)
    (require_1 : precondition arr target)
    (ans : ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_running_ans : found = false → ans = -1)
    (invariant_inv_prefix_ne_target : ∀ j < i, ¬arr[j]! = target)
    (invariant_inv_prefix_lt_target : found = false → ∀ j < i, arr[j]! < target)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_inv_ans_characterization : ans = -1 ∨ intIndexInBounds arr ans ∧ arr[ans.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target)
    (invariant_inv_found_noans_implies_gt : found = true → ans = -1 → i < arr.size ∧ target < arr[i]!)
    (done_1 : arr.size ≤ i ∨ found = true)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    : postcondition arr target i_1 := by
  have hans : ans = i_1 := by (try simp at *; expose_names); exact (goal_1_0 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target i_1 i_2 i_3 invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt done_1 i_4); done
  have hi1s : i_1 = ans := by (try simp at *; expose_names); exact id (Eq.symm hans); done

  -- Main split of the postcondition
  refine And.intro ?hleft ?hright

  · -- (i_1 = -1 ↔ ¬ occurs arr target)
    refine Iff.intro ?himp ?hrev

    · -- (→) i_1 = -1 → ¬ occurs arr target
      intro hi1neg
      have hansneg : ans = -1 := by (try simp at *; expose_names); exact (goal_1_1 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target i_1 i_2 i_3 invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt done_1 i_4 hans hi1s hi1neg); done

      -- Use loop termination condition to show absence
      have hnoOcc : ¬ occurs arr target := by
        cases done_1 with
        | inl hsize_le_i =>
          -- scanned past end, use prefix_ne_target to rule out all valid indices
          have hall_ne : ∀ k < arr.size, arr[k]! ≠ target := by
            intro k hk
            have hklt : k < i := by
              exact Nat.lt_of_lt_of_le hk hsize_le_i
            have hkne : ¬ arr[k]! = target := by
              exact invariant_inv_prefix_ne_target k hklt
            exact hkne
          have hnotOccurs : ¬ occurs arr target := by
            intro hoc
            rcases hoc with ⟨k, hk, hkeq⟩
            have hkne : arr[k]! ≠ target := hall_ne k hk
            exact hkne hkeq
          exact hnotOccurs
        | inr hfound =>
          -- stopped with found=true; if ans=-1 then we stopped due to arr[i] > target and sortedness implies absence
          -- (if ans ≠ -1 then occurs holds, contradiction with hansneg)
          have hgt : i < arr.size ∧ target < arr[i]! := by
            exact invariant_inv_found_noans_implies_gt hfound hansneg
          have hsorted : isSortedNonDecreasing arr := by
            simpa [precondition] using require_1
          have hall_ne : ∀ k < arr.size, arr[k]! ≠ target := by
            intro k hk
            by_cases hklt : k < i
            · -- k < i: use prefix_ne_target
              have hkne : ¬ arr[k]! = target := invariant_inv_prefix_ne_target k hklt
              exact hkne
            · -- i ≤ k: use sortedness + target < arr[i] to show target < arr[k], hence not equal
              have hik : i < k ∨ i = k ∨ k < i := by (try simp at *; expose_names); exact (Nat.lt_trichotomy i k); done
              have hkne : arr[k]! ≠ target := by (try simp at *; expose_names); exact (goal_1_2 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target i_1 i_2 i_3 invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt i_4 hans hi1s hi1neg hansneg hfound hgt hsorted k hk hik hklt); done
              exact hkne
          have hnotOccurs : ¬ occurs arr target := by
            intro hoc
            rcases hoc with ⟨k, hk, hkeq⟩
            have hkne : arr[k]! ≠ target := hall_ne k hk
            exact hkne hkeq
          exact hnotOccurs

      exact hnoOcc

    · -- (←) ¬ occurs arr target → i_1 = -1
      intro hnoOcc
      by_contra hi1ne
      have hansne : ans ≠ -1 := by (try simp at *; expose_names); exact (ne_of_eq_of_ne hans hi1ne); done
      have hgood :
          intIndexInBounds arr ans ∧
          arr[ans.toNat]! = target ∧
          ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target := by
        exact Or.resolve_left invariant_inv_ans_characterization hansne
      have hoc : occurs arr target := by
        rcases hgood with ⟨hb, hval, hmin⟩
        refine ⟨ans.toNat, ?_, ?_⟩
        · -- bounds from intIndexInBounds
          exact (And.right hb)
        · exact hval
      exact hnoOcc hoc

  · -- (i_1 ≠ -1 → intIndexInBounds ... ∧ arr[...] = target ∧ minimality)
    intro hi1ne
    have hansne : ans ≠ -1 := by (try simp at *; expose_names); exact (ne_of_eq_of_ne hans hi1ne); done
    have hgood :
        intIndexInBounds arr ans ∧
        arr[ans.toNat]! = target ∧
        ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target := by
      exact Or.resolve_left invariant_inv_ans_characterization hansne

    have hbounds : intIndexInBounds arr i_1 := by (try simp at *; expose_names); exact (goal_1_3 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target i_1 i_2 i_3 invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt done_1 i_4 hans hi1s hi1ne hansne hgood); done
    have hval : arr[i_1.toNat]! = target := by (try simp at *; expose_names); exact (goal_1_4 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target i_1 i_2 i_3 invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt done_1 i_4 hans hi1s hi1ne hansne hgood hbounds); done
    have hminNat : ∀ (j : ℕ), j < i_1.toNat → arr[j]! ≠ target := by
      intro j hj
      -- convert j < i_1.toNat into (↑j : ℤ) < i_1 = ans, then use hgood's minimality
      have hjInt : (↑j : ℤ) < i_1 := by (try simp at *; expose_names); exact hj; done
      have hjInt' : (↑j : ℤ) < ans := by (try simp at *; expose_names); exact (lt_of_lt_of_eq hjInt hi1s); done
      have hminInt : ∀ (j : ℕ), ↑j < ans → ¬arr[j]! = target := by
        exact (And.right (And.right hgood))
      have hjne : ¬ arr[j]! = target := hminInt j hjInt'
      exact hjne

    exact And.intro hbounds (And.intro hval hminNat)


prove_correct findFirstOccurrence by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target a a_1 if_pos invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt)
  exact (goal_1 arr target require_1 ans found i invariant_inv_i_bounds invariant_inv_running_ans invariant_inv_prefix_ne_target invariant_inv_prefix_lt_target i_1 i_2 i_3 invariant_inv_ans_characterization invariant_inv_found_noans_implies_gt done_1 i_4)
end Proof
