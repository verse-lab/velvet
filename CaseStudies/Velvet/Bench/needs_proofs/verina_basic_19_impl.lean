import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSorted: check whether an array of integers is sorted in non-decreasing order.
-/

@[grind]
def AdjacentSorted (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!
@[grind]
def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

section Impl
method isSorted (a : Array Int) return (result : Bool)
  ensures result = true ↔ AdjacentSorted a
  ensures result = true → GloballySorted a
  ensures result = false ↔ ¬ AdjacentSorted a
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
@[grind]
lemma adjacent_implies_global (a : Array Int) (hadj : AdjacentSorted a) : GloballySorted a := by
  intro p q hpq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
  induction d <;> grind

prove_correct isSorted by
  loom_solve

end Proof
