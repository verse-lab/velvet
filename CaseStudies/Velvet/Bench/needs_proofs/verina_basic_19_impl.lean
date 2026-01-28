import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSorted: check whether an array of integers is sorted in non-decreasing order.
-/

def AdjacentSorted (a : Array Int) : Prop :=
  ∀ i, 0 ≤ i → i < a.size - 1 → a[i]! ≤ a[i + 1]!

def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

section Impl
method isSorted (a : Array Int) return (result : Bool)
  ensures result = true ↔ GloballySorted a
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
lemma adjacent_implies_global (a : Array Int) (hadj : AdjacentSorted a)
  : GloballySorted a := by
  intro p q hpq hq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
  have : ∀ d : Nat, p + d.succ < a.size → a[p]! ≤ a[p + d.succ]! := by
    intro d
    induction d with
    | zero => grind [AdjacentSorted]
    | succ _ _ => grind [AdjacentSorted]
  exact this d (by simpa using hq)

prove_correct isSorted by
  loom_solve <;> (try simp at *; expose_names)
  -- Main proof goal
  rcases i_2 with ⟨hi, hres⟩
  cases done_1 with
  | inl h_size_le =>
    -- Case: loop exited because i+1 >= a.size
    constructor
    · -- sorted = true ↔ AdjacentSorted a
      have h_adj_of_true : sorted = true → AdjacentSorted a := by
        intro hst k hk1 hk2
        exact invariant_inv_checked_prefix hst k (by omega)
      grind [adjacent_implies_global]
    · -- sorted = false ↔ ¬AdjacentSorted a
      intro hsort
      by_cases hst : sorted = true
      · grind
      · rcases (invariant_inv_witness_if_false (by grind)) with ⟨ k, hk ⟩
        specialize hsort k (k + 1)
        grind
  | inr h_sorted_false => aesop; specialize a_1 w (w + 1); grind

end Proof
