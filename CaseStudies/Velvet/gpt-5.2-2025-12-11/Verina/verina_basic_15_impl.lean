import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsConsecutiveNumbers: determine whether an array of integers contains at least one pair of consecutive numbers
    Natural language breakdown:
    1. Input is an array `a` of integers; it may be empty or non-empty.
    2. A "consecutive pair" means there exists an index `i` such that `i + 1 < a.size` and `a[i] + 1 = a[i+1]`.
    3. The result is `true` iff such an index exists.
    4. If the array has size 0 or 1, then no such index exists and the result is `false`.
    5. There are no preconditions.
-/

section Specs
-- Helper predicate: there exists an adjacent index with successor-by-1 relation.
-- Using Nat indices with bounds and `a[i]!` access as required by the guidelines.
def HasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

-- No preconditions.
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is true exactly when the array has a consecutive pair.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasConsecutivePair a)
end Specs

section Impl
method containsConsecutiveNumbers (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
    if a.size < 2 then
      return false
    else
      let mut i : Nat := 0
      let mut found : Bool := false
      while i + 1 < a.size ∧ found = false
        -- Bounds: loop condition gives i+1 < a.size; keep a weaker, stable form.
        invariant "inv_bounds" (i + 1 ≤ a.size)
        -- Progress information: as long as we haven't found a pair, indices before i are checked.
        invariant "inv_no_pair_so_far" (found = false → (∀ j : Nat, j < i → a[j]! + 1 ≠ a[j + 1]!))
        -- If found is true, we have a witness consecutive pair.
        invariant "inv_found_witness" (found = true → HasConsecutivePair a)
        done_with (i + 1 ≥ a.size ∨ found = true)
      do
        if a[i]! + 1 = a[i + 1]! then
          found := true
        else
          i := i + 1
      return found
end Impl

section TestCases
-- Test case 1: example from prompt
def test1_a : Array Int := #[1, 2, 3, 5]
def test1_Expected : Bool := true

-- Test case 2: no consecutive numbers
def test2_a : Array Int := #[1, 3, 5, 7]
def test2_Expected : Bool := false

-- Test case 3: empty array
def test3_a : Array Int := #[]
def test3_Expected : Bool := false

-- Test case 4: single element
def test4_a : Array Int := #[10]
def test4_Expected : Bool := false

-- Test case 5: minimal positive case (two elements consecutive)
def test5_a : Array Int := #[5, 6]
def test5_Expected : Bool := true

-- Test case 6: consecutive pair occurs in the middle
def test6_a : Array Int := #[5, 7, 8, 10]
def test6_Expected : Bool := true

-- Test case 7: duplicates then consecutive (9,9,10 has 9+1=10)
def test7_a : Array Int := #[9, 9, 10]
def test7_Expected : Bool := true

-- Test case 8: all equal, no consecutive increment
def test8_a : Array Int := #[3, 3, 3]
def test8_Expected : Bool := false

-- Recommend to validate: 1, 3, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((containsConsecutiveNumbers test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((containsConsecutiveNumbers test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((containsConsecutiveNumbers test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((containsConsecutiveNumbers test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((containsConsecutiveNumbers test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((containsConsecutiveNumbers test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((containsConsecutiveNumbers test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((containsConsecutiveNumbers test8_a).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for containsConsecutiveNumbers
prove_precondition_decidable_for containsConsecutiveNumbers
prove_postcondition_decidable_for containsConsecutiveNumbers
derive_tester_for containsConsecutiveNumbers
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := containsConsecutiveNumbersTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct containsConsecutiveNumbers by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (if_pos : a.size < 2)
    : postcondition a false ↔ ¬HasConsecutivePair a := by
  simp [postcondition, HasConsecutivePair]

theorem goal_0_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (if_pos : a.size < 2)
    (h_post_unfold : postcondition a false = (false = true ↔ HasConsecutivePair a))
    (h_false_eq_true : (false = true) = False)
    : (false = true ↔ HasConsecutivePair a) ↔ ¬HasConsecutivePair a := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (if_pos : a.size < 2)
    : postcondition a false := by
    -- Step 1: unfold the postcondition at result = false
    have h_post_unfold : postcondition a false = ((false = true) ↔ HasConsecutivePair a) := by
      (try simp at *; expose_names); try exact?; done

    -- Step 2: simplify `false = true` to `False` inside the iff
    have h_false_eq_true : (false = true) = False := by
      (try simp at *; expose_names); exact Bool.false_eq_true; done

    -- Step 3: reduce the goal to proving `¬ HasConsecutivePair a`
    have h_reduce : ((false = true) ↔ HasConsecutivePair a) ↔ (¬ HasConsecutivePair a) := by
      (try simp at *; expose_names); try exact?; done

    -- Step 4: show the existential in `HasConsecutivePair` is impossible from `a.size < 2`
    have h_no_consecutive : ¬ HasConsecutivePair a := by
      -- Unfold the definition to expose the witness `i` and the bound `i + 1 < a.size`
      have h_unfold_hcp :
          HasConsecutivePair a = (∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!) := by
        (try simp at *; expose_names); exact Eq.to_iff rfl; done
      -- Use the bound `i+1 < a.size` and `a.size < 2` to derive `i+1 < 2`
      have h_no_witness : ¬ (∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!) := by
        intro h
        rcases h with ⟨i, hi_lt, hi_eq⟩
        have h_i1_lt_2 : i + 1 < 2 := by
          -- chain: i+1 < a.size and a.size < 2
          exact Nat.lt_trans hi_lt if_pos
        -- from i+1 < 2 we get i+1 ≤ 1, hence i = 0 and thus need 1 < a.size, which contradicts a.size < 2
        have h_asize_le_1 : a.size ≤ 1 := by
          (try simp at *; expose_names); exact Nat.le_of_lt_succ if_pos; done
        have h_not_one_lt : ¬ (1 < a.size) := by
          (try simp at *; expose_names); exact h_asize_le_1; done
        have h_one_lt_asize : 1 < a.size := by
          -- from hi_lt with i = 0 would yield 1 < a.size; we extract that contradiction path
          (try simp at *; expose_names); exact Nat.lt_of_add_left_lt hi_lt; done
        exact (h_not_one_lt h_one_lt_asize)
      -- convert the `¬ ∃ ...` back into `¬ HasConsecutivePair a`
      have h_no_consecutive' : ¬ HasConsecutivePair a := by
        -- rewrite using the unfolding lemma
        simpa [h_unfold_hcp] using h_no_witness
      exact h_no_consecutive'

    -- Step 5: finish the main goal by rewriting and applying the reduction
    -- (no `(try simp at *; expose_names); try exact?; done` for the main goal)
    have h_main_iff : (false = true ↔ HasConsecutivePair a) := by
      -- use the reduction to turn `h_no_consecutive` into the desired iff
      have : ¬ HasConsecutivePair a := h_no_consecutive
      -- rearrange via h_reduce
      exact (h_reduce).2 this

    -- conclude `postcondition a false`
    -- via unfolding postcondition and the established iff
    simpa [postcondition] using h_main_iff

theorem goal_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_bounds : i + 1 ≤ a.size)
    (invariant_inv_no_pair_so_far : found = false → ∀ j < i, ¬a[j]! + 1 = a[j + 1]!)
    (invariant_inv_found_witness : found = true → HasConsecutivePair a)
    (a_1 : i + 1 < a.size)
    (a_2 : found = false)
    (if_pos : a[i]! + 1 = a[i + 1]!)
    (if_neg : 2 ≤ a.size)
    : HasConsecutivePair a := by
  refine ⟨i, a_1, if_pos⟩


theorem goal_2
    (a : Array ℤ)
    (require_1 : precondition a)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_bounds : i + 1 ≤ a.size)
    (invariant_inv_no_pair_so_far : found = false → ∀ j < i, ¬a[j]! + 1 = a[j + 1]!)
    (invariant_inv_found_witness : found = true → HasConsecutivePair a)
    (i_1 : Bool)
    (i_2 : ℕ)
    (if_neg : 2 ≤ a.size)
    (done_1 : a.size ≤ i + 1 ∨ found = true)
    (i_3 : found = i_1 ∧ i = i_2)
    : postcondition a i_1 := by
  rcases i_3 with ⟨hfound, hi⟩
  unfold postcondition
  have hiff : (found = true ↔ HasConsecutivePair a) := by
    constructor
    · intro hft
      exact invariant_inv_found_witness hft
    · intro hpair
      -- use how the loop terminated
      cases done_1 with
      | inr hft =>
          exact hft
      | inl hsize_le =>
          -- if the loop ended by bounds, show `found` cannot be false (else contradict hpair)
          by_contra hnot_true
          have hff : found = false := by
            cases found <;> simp at hnot_true ⊢
          have hno : ∀ j < i, ¬a[j]! + 1 = a[j + 1]! :=
            invariant_inv_no_pair_so_far hff
          have hEq : i + 1 = a.size :=
            Nat.le_antisymm invariant_inv_bounds hsize_le
          have hcontra : ¬ HasConsecutivePair a := by
            intro hex
            rcases hex with ⟨j, hjlt, hconsec⟩
            -- from j+1 < a.size = i+1 get j < i
            have hj1lt : j + 1 < i + 1 := by
              -- rewrite a.size as i+1
              simpa [hEq] using hjlt
            have hjlt_i : j < i := by
              -- cancel +1
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                (Nat.lt_of_add_lt_add_right (k := j) (m := i) (n := 1) hj1lt)
            exact (hno j hjlt_i) hconsec
          exact hcontra hpair
  simpa [hfound] using hiff


prove_correct containsConsecutiveNumbers by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
  exact (goal_1 a require_1 found i invariant_inv_bounds invariant_inv_no_pair_so_far invariant_inv_found_witness a_1  a_2 if_pos if_neg)
  exact (goal_2 a require_1  found  i invariant_inv_bounds invariant_inv_no_pair_so_far  invariant_inv_found_witness i_1 i_2 if_neg  done_1 i_3)
end Proof
