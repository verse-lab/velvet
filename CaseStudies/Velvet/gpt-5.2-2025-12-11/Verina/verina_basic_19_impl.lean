import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSorted: check whether an array of integers is sorted in non-decreasing order.
    Natural language breakdown:
    1. Input is an array of integers `a`; it may be empty or any length.
    2. The result is a boolean.
    3. The result is true exactly when every adjacent pair is ordered: for each index i with i+1 in bounds,
       we have a[i] ≤ a[i+1].
    4. When the result is true, the array is globally non-decreasing: for any indices i < j within bounds,
       a[i] ≤ a[j].
    5. When the result is false, the array is not adjacent-sorted, meaning there exists some adjacent inversion.
-/

section Specs
-- Adjacent non-decreasing order.
-- Using Nat indices and `a[i]!` with explicit bounds checks.
def AdjacentSorted (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Global non-decreasing order (matches the Note text).
def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- No input restrictions.
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) The boolean result reflects adjacent sortedness.
-- 2) If true, also satisfies the global non-decreasing guarantee.
-- 3) If false, then adjacent sortedness does not hold.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ AdjacentSorted a) ∧
  (result = true → GloballySorted a) ∧
  (result = false ↔ ¬ AdjacentSorted a)
end Specs

section Impl
method isSorted (a : Array Int) return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
    let mut sorted := true
    let mut i : Nat := 0
    -- Scan adjacent pairs; if we find an inversion, mark as unsorted and stop.
    while i + 1 < a.size ∧ sorted
      -- Invariant: i stays within array bounds; always true for Nat index and needed for safe reads when loop cond holds.
      -- Init: i=0. Preserved: i increments. Sufficient: helps show indices mentioned in other invariants are in-range.
      invariant "inv_i_le_size" i ≤ a.size
      -- Invariant: if still marked sorted, all already-checked adjacent pairs (with index < i) are ordered.
      -- Init: i=0, vacuous. Preserved: when a[i] ≤ a[i+1], incrementing i makes the new checked pair become part of the prefix.
      invariant "inv_checked_prefix" (sorted = true → ∀ k : Nat, k < i → a[k]! ≤ a[k + 1]!)
      -- Invariant: if sorted=false, we have witnessed an inversion at some index k that is within the already-scanned range (k ≤ i).
      -- Init: sorted=true so vacuous. Preserved: when we set sorted:=false at index i, we can witness k=i.
      invariant "inv_witness_if_false" (sorted = false → ∃ k : Nat, k ≤ i ∧ k + 1 < a.size ∧ a[k]! > a[k + 1]!)
      done_with (i + 1 ≥ a.size ∨ sorted = false)
    do
      if a[i]! > a[i + 1]! then
        sorted := false
      i := i + 1
    return sorted
end Impl

section TestCases
-- Test case 1: example from prompt, already sorted
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: strictly decreasing
def test2_a : Array Int := #[5, 4, 3, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: one local inversion in the middle
def test3_a : Array Int := #[1, 3, 2, 4, 5]
def test3_Expected : Bool := false

-- Test case 4: empty array (vacuously sorted)
def test4_a : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: singleton array (vacuously sorted)
def test5_a : Array Int := #[10]
def test5_Expected : Bool := true

-- Test case 6: all equal elements (non-decreasing)
def test6_a : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: has equal neighbors and increasing steps
def test7_a : Array Int := #[1, 2, 2, 3]
def test7_Expected : Bool := true

-- Test case 8: minimal unsorted length-2 array
def test8_a : Array Int := #[2, 1]
def test8_Expected : Bool := false

-- Test case 9: sorted with negatives and duplicates
def test9_a : Array Int := #[-3, -3, -1, 0, 0, 2]
def test9_Expected : Bool := true

-- Recommend to validate: 1, 3, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isSorted test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isSorted test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isSorted test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isSorted test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isSorted test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isSorted test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isSorted test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isSorted test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isSorted test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for isSorted
prove_precondition_decidable_for isSorted
prove_postcondition_decidable_for isSorted
derive_tester_for isSorted
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := isSortedTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isSorted by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (sorted : Bool)
    (invariant_inv_i_le_size : i ≤ a.size)
    (invariant_inv_checked_prefix : sorted = true → ∀ k < i, a[k]! ≤ a[k + 1]!)
    (i_1 : ℕ)
    (sorted_1 : Bool)
    (invariant_inv_witness_if_false : sorted = false → ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]!)
    (done_1 : a.size ≤ i + 1 ∨ sorted = false)
    (i_2 : i = i_1 ∧ sorted = sorted_1)
    : sorted = sorted_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (sorted : Bool)
    (invariant_inv_i_le_size : i ≤ a.size)
    (invariant_inv_checked_prefix : sorted = true → ∀ k < i, a[k]! ≤ a[k + 1]!)
    (i_1 : ℕ)
    (sorted_1 : Bool)
    (invariant_inv_witness_if_false : sorted = false → ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]!)
    (i_2 : i = i_1 ∧ sorted = sorted_1)
    (hsorted_eq : sorted = sorted_1)
    (hsorted1_eq : sorted_1 = sorted)
    (h_size_le : a.size ≤ i + 1)
    : ∀ (k : ℕ), k + 1 < a.size → k < i := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_2
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (sorted : Bool)
    (invariant_inv_i_le_size : i ≤ a.size)
    (invariant_inv_checked_prefix : sorted = true → ∀ k < i, a[k]! ≤ a[k + 1]!)
    (i_1 : ℕ)
    (sorted_1 : Bool)
    (invariant_inv_witness_if_false : sorted = false → ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]!)
    (i_2 : i = i_1 ∧ sorted = sorted_1)
    (hsorted_eq : sorted = sorted_1)
    (hsorted1_eq : sorted_1 = sorted)
    (h_size_le : a.size ≤ i + 1)
    (h_k_lt_i : ∀ (k : ℕ), k + 1 < a.size → k < i)
    (h_adj_of_sorted_true : sorted = true → AdjacentSorted a)
    : AdjacentSorted a → GloballySorted a := by
  intro hadj
  intro p q hpq hq
  -- write q = p + (d+1)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
  -- Now it suffices to chain adjacent inequalities from p to p+d
  have hchain :
      ∀ d : Nat, p + d.succ < a.size → a[p]! ≤ a[p + d.succ]! := by
    intro d
    induction d with
    | zero =>
        intro hbound
        -- need a[p]! ≤ a[p+1]!
        simpa using hadj p (by simpa using hbound)
    | succ d ih =>
        intro hbound
        -- use ih for p+(d+1) and then one more adjacent step to p+(d+2)
        have hbound_prev : p + d.succ < a.size := by
          exact Nat.lt_trans (Nat.lt_succ_self (p + d.succ)) hbound
        have hprev : a[p]! ≤ a[p + d.succ]! := ih hbound_prev
        have hstep : a[p + d.succ]! ≤ a[p + d.succ.succ]! := by
          apply hadj (p + d.succ)
          -- (p + (d+1)) + 1 < a.size
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound
        exact le_trans hprev hstep
  exact hchain d (by simpa using hq)

theorem goal_0_3
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (sorted : Bool)
    (invariant_inv_i_le_size : i ≤ a.size)
    (invariant_inv_checked_prefix : sorted = true → ∀ k < i, a[k]! ≤ a[k + 1]!)
    (i_1 : ℕ)
    (sorted_1 : Bool)
    (invariant_inv_witness_if_false : sorted = false → ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]!)
    (i_2 : i = i_1 ∧ sorted = sorted_1)
    (hsorted_eq : sorted = sorted_1)
    (hsorted1_eq : sorted_1 = sorted)
    (h_sorted_false : sorted = false)
    (k : ℕ)
    (hk_le : k ≤ i)
    (hk1 : k + 1 < a.size)
    (hlt : a[k + 1]! < a[k]!)
    (h_not_adj : ¬AdjacentSorted a)
    (hst : sorted = true)
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_4
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (sorted : Bool)
    (invariant_inv_i_le_size : i ≤ a.size)
    (invariant_inv_checked_prefix : sorted = true → ∀ k < i, a[k]! ≤ a[k + 1]!)
    (i_1 : ℕ)
    (sorted_1 : Bool)
    (invariant_inv_witness_if_false : sorted = false → ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]!)
    (i_2 : i = i_1 ∧ sorted = sorted_1)
    (hsorted_eq : sorted = sorted_1)
    (hsorted1_eq : sorted_1 = sorted)
    (h_sorted_false : sorted = false)
    (k : ℕ)
    (hk_le : k ≤ i)
    (hk1 : k + 1 < a.size)
    (hlt : a[k + 1]! < a[k]!)
    (h_not_adj : ¬AdjacentSorted a)
    (hst : sorted = true)
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (sorted : Bool)
    (invariant_inv_i_le_size : i ≤ a.size)
    (invariant_inv_checked_prefix : sorted = true → ∀ k < i, a[k]! ≤ a[k + 1]!)
    (i_1 : ℕ)
    (sorted_1 : Bool)
    (invariant_inv_witness_if_false : sorted = false → ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]!)
    (done_1 : a.size ≤ i + 1 ∨ sorted = false)
    (i_2 : i = i_1 ∧ sorted = sorted_1)
    : postcondition a sorted_1 := by
    have hsorted_eq : sorted = sorted_1 := by (try simp at *; expose_names); exact (goal_0_0 a require_1 i sorted invariant_inv_i_le_size invariant_inv_checked_prefix i_1 sorted_1 invariant_inv_witness_if_false done_1 i_2); done
    have hsorted1_eq : sorted_1 = sorted := by (try simp at *; expose_names); exact (id (Eq.symm hsorted_eq)); done

    -- We prove the postcondition for `sorted` and then rewrite to `sorted_1`.
    have h_post_sorted : postcondition a sorted := by
      -- Split on the loop exit condition
      cases done_1 with
      | inl h_size_le =>
        -- CASE A: a.size ≤ i + 1
        -- Subgoal: AdjacentSorted a (this is what we can get from checked_prefix + bounds)
        have h_k_lt_i : ∀ k : Nat, k + 1 < a.size → k < i := by (try simp at *; expose_names); exact (goal_0_1 a require_1 i sorted invariant_inv_i_le_size invariant_inv_checked_prefix i_1 sorted_1 invariant_inv_witness_if_false i_2 hsorted_eq hsorted1_eq h_size_le); done
        have h_adj_of_sorted_true : sorted = true → AdjacentSorted a := by
          intro hst
          intro k hk1
          have hklt : k < i := by
            exact h_k_lt_i k hk1
          have hprefix : ∀ t : Nat, t < i → a[t]! ≤ a[t + 1]! := by
            exact invariant_inv_checked_prefix hst
          have hkineq : a[k]! ≤ a[k + 1]! := by
            exact hprefix k hklt
          exact hkineq

        -- Subgoal: AdjacentSorted a → GloballySorted a (standard chaining argument)
        have h_global_of_adj : AdjacentSorted a → GloballySorted a := by (try simp at *; expose_names); exact (goal_0_2 a require_1 i sorted invariant_inv_i_le_size invariant_inv_checked_prefix i_1 sorted_1 invariant_inv_witness_if_false i_2 hsorted_eq hsorted1_eq h_size_le h_k_lt_i h_adj_of_sorted_true); done

        -- Now assemble postcondition; note: without extra hypotheses we cannot decide `sorted`,
        -- so we keep implications conditional on `sorted = true/false` and use classical reasoning where needed.
        refine And.intro ?_ (And.intro ?_ ?_)
        · -- (sorted = true ↔ AdjacentSorted a)
          refine Iff.intro ?_ ?_
          · intro hst
            exact h_adj_of_sorted_true hst
          · intro hadj
            -- This direction is not derivable from the given local hypotheses alone in general;
            -- in the full loop proof it follows from completeness of the scan.
            -- Here we use a Bool case split and discharge by contradiction in the `sorted=false` branch.
            by_cases hsf : sorted = false
            · have hw : ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]! := by
                exact invariant_inv_witness_if_false hsf
              rcases hw with ⟨k, hk_le, hk1, hlt⟩
              have : False := by
                have hkadj : a[k]! ≤ a[k + 1]! := by
                  exact hadj k hk1
                have hnle : ¬ a[k]! ≤ a[k + 1]! := by
                  -- from a[k+1] < a[k] derive ¬(a[k] ≤ a[k+1])
                  exact by
                    -- Int.lt_of_le_of_ne / lt_le_asymm style; keep as a placeholder
                    (try simp at *; expose_names); exact hlt; done
                exact (hnle hkadj).elim
              exact False.elim this
            · -- sorted ≠ false, hence sorted = true
              have : sorted = true := by
                -- Bool is two-valued
                (try simp at *; expose_names); exact hsf; done
              exact this
        · -- (sorted = true → GloballySorted a)
          intro hst
          have hadj : AdjacentSorted a := by
            exact h_adj_of_sorted_true hst
          have hglob : GloballySorted a := by
            exact h_global_of_adj hadj
          exact hglob
        · -- (sorted = false ↔ ¬ AdjacentSorted a)
          refine Iff.intro ?_ ?_
          · intro hsf
            have hw : ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]! := by
              exact invariant_inv_witness_if_false hsf
            rcases hw with ⟨k, hk_le, hk1, hlt⟩
            intro hadj
            have hkadj : a[k]! ≤ a[k + 1]! := by
              exact hadj k hk1
            have : False := by
              have hnle : ¬ a[k]! ≤ a[k + 1]! := by
                -- from a[k+1] < a[k] derive ¬(a[k] ≤ a[k+1])
                (try simp at *; expose_names); exact hlt; done
              exact (hnle hkadj).elim
            exact this.elim
          · intro hnadj
            -- This direction (¬AdjacentSorted -> sorted=false) is not derivable from the given hypotheses alone;
            -- in the full loop proof it follows from completeness of scanning.
            -- We again use a Bool split and rule out sorted=true using the already-proved direction.
            by_cases hst : sorted = true
            · have hadj : AdjacentSorted a := by
                -- use the (sorted=true -> AdjacentSorted) direction already established above
                exact (by
                  have : sorted = true → AdjacentSorted a := by
                    exact h_adj_of_sorted_true
                  exact this hst)
              have : False := by
                exact (hnadj hadj)
              exact False.elim this
            · have : sorted = false := by
                -- Bool is two-valued
                (try simp at *; expose_names); exact hst; done
              exact this
      | inr h_sorted_false =>
        -- CASE B: sorted = false
        have hw : ∃ k ≤ i, k + 1 < a.size ∧ a[k + 1]! < a[k]! := by
          exact invariant_inv_witness_if_false h_sorted_false
        rcases hw with ⟨k, hk_le, hk1, hlt⟩

        -- Subgoal: ¬ AdjacentSorted a from the witness inversion
        have h_not_adj : ¬ AdjacentSorted a := by
          intro hadj
          have hkadj : a[k]! ≤ a[k + 1]! := by
            exact hadj k hk1
          have : False := by
            have hnle : ¬ a[k]! ≤ a[k + 1]! := by
              -- from a[k+1] < a[k] derive ¬(a[k] ≤ a[k+1])
              (try simp at *; expose_names); exact hlt; done
            exact (hnle hkadj).elim
          exact this.elim

        -- Assemble postcondition in the false case
        refine And.intro ?_ (And.intro ?_ ?_)
        · -- (sorted = true ↔ AdjacentSorted a)
          refine Iff.intro ?_ ?_
          · intro hst
            -- sorted=true contradicts sorted=false
            have : False := by
              -- Bool equality contradiction
              (try simp at *; expose_names); exact (goal_0_3 a require_1 i sorted invariant_inv_i_le_size invariant_inv_checked_prefix i_1 sorted_1 invariant_inv_witness_if_false i_2 hsorted_eq hsorted1_eq h_sorted_false k hk_le hk1 hlt h_not_adj hst); done
            exact False.elim this
          · intro hadj
            -- AdjacentSorted contradicts the witnessed inversion
            have : False := by
              exact (h_not_adj hadj)
            exact False.elim this
        · -- (sorted = true → GloballySorted a) (vacuous)
          intro hst
          have : False := by
            -- sorted=true contradicts sorted=false
            (try simp at *; expose_names); exact (goal_0_4 a require_1 i sorted invariant_inv_i_le_size invariant_inv_checked_prefix i_1 sorted_1 invariant_inv_witness_if_false i_2 hsorted_eq hsorted1_eq h_sorted_false k hk_le hk1 hlt h_not_adj hst); done
          exact False.elim this
        · -- (sorted = false ↔ ¬ AdjacentSorted a)
          refine Iff.intro ?_ ?_
          · intro _
            exact h_not_adj
          · intro _
            exact h_sorted_false

    -- Rewrite result from `sorted` to `sorted_1`
    -- using sorted = sorted_1.
    simpa [hsorted1_eq] using h_post_sorted


prove_correct isSorted by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1 i sorted invariant_inv_i_le_size invariant_inv_checked_prefix i_1 sorted_1 invariant_inv_witness_if_false done_1 i_2)
end Proof
