import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSorted: check whether an array of integers is sorted in non-decreasing order.
-/

section Specs
def AdjacentSorted (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

def precondition (_ : Array Int) : Prop :=
  True

abbrev postcondition (a : Array Int) (result : Bool) : Prop :=
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
    while i + 1 < a.size ∧ sorted
      invariant "inv_i_le_size" i ≤ a.size
      invariant "inv_checked_prefix" (sorted = true → ∀ k : Nat, k < i → a[k]! ≤ a[k + 1]!)
      invariant "inv_witness_if_false" (sorted = false → ∃ k : Nat, k ≤ i ∧ k + 1 < a.size ∧ a[k]! > a[k + 1]!)
      done_with (i + 1 ≥ a.size ∨ sorted = false)
    do
      if a[i]! > a[i + 1]! then
        sorted := false
      i := i + 1
    return sorted
end Impl

section Proof
set_option maxHeartbeats 10000000

-- Compact helper: chaining adjacent sortedness gives global sortedness
lemma adjacent_implies_global (a : Array Int) (hadj : AdjacentSorted a) : GloballySorted a := by
  intro p q hpq hq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
  have : ∀ d : Nat, p + d.succ < a.size → a[p]! ≤ a[p + d.succ]! := by
    intro d
    induction d with
    | zero => intro h; simpa using hadj p (by simpa using h)
    | succ d ih =>
        intro hbound
        have h1 := ih (Nat.lt_trans (Nat.lt_succ_self _) hbound)
        have h2 := hadj (p + d.succ) (by simpa [Nat.add_assoc] using hbound)
        exact le_trans h1 h2
  exact this d (by simpa using hq)

prove_correct isSorted by
  loom_solve <;> (try simp at *; expose_names)
  -- Main proof goal
  rcases i_2 with ⟨hi, hres⟩
  cases done_1 with
  | inl h_size_le =>
    -- Case: loop exited because i+1 >= a.size
    have h_adj_of_true : sorted = true → AdjacentSorted a := by
      intro hst k hk1
      exact invariant_inv_checked_prefix hst k (by omega)
    constructor
    · -- sorted = true ↔ AdjacentSorted a
      constructor
      · grind
      · intro hadj
        by_cases hsf : sorted = false
        · rcases invariant_inv_witness_if_false hsf with ⟨k, _, hk1, hlt⟩
          exact absurd (hadj k hk1) (by omega)
        · simp at hsf; simp [← hres, hsf]
    constructor
    · -- sorted = true → GloballySorted a
      intro hst
      subst sorted_1
      exact adjacent_implies_global a (h_adj_of_true hst)
    · -- sorted = false ↔ ¬AdjacentSorted a
      constructor
      · intro hsf
        subst sorted_1
        rcases invariant_inv_witness_if_false hsf with ⟨k, _, hk1, hlt⟩
        intro hadj
        exact absurd (hadj k hk1) (by omega)
      · intro hnadj
        by_cases hst : sorted = true
        · exact absurd (h_adj_of_true hst) hnadj
        · simp at hst; subst sorted_1; exact hst
  | inr h_sorted_false =>
    -- Case: loop exited because sorted = false
    rcases invariant_inv_witness_if_false h_sorted_false with ⟨k, _, hk1, hlt⟩
    have h_not_adj : ¬AdjacentSorted a := by
      intro hadj
      exact absurd (hadj k hk1) (by omega)
    constructor
    · -- sorted = true ↔ AdjacentSorted a (both false)
      constructor
      · intro hst; subst sorted_1; rw [h_sorted_false] at hst; contradiction
      · intro hadj; exact absurd hadj h_not_adj
    constructor
    · -- sorted = true → GloballySorted a (vacuous)
      intro hst; rw [h_sorted_false, hst] at hres; contradiction
      -- rcases invariant_inv_witness_if_false with ⟨k, hkle, hk1, hlt⟩
    · -- sorted = false ↔ ¬AdjacentSorted a
      simp [← hres, h_sorted_false, h_not_adj]

end Proof
