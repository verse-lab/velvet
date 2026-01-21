import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (xs : List Nat) :=
  xs.length > 0 ∧ ∃ x ∈ xs, xs.count x > xs.length / 2



def postcondition (xs : List Nat) (result : Nat) :=
  result ∈ xs ∧ xs.count result > xs.length / 2


def test1_xs : List Nat := [3, 3, 4, 2, 3, 3, 3]

def test1_Expected : Nat := 3

def test3_xs : List Nat := [2, 2, 2, 1, 1]

def test3_Expected : Nat := 2

def test6_xs : List Nat := [42]

def test6_Expected : Nat := 42







section Proof
theorem test1_precondition :
  precondition test1_xs := by
  unfold precondition test1_xs
  constructor
  · native_decide
  · exact ⟨3, by native_decide, by native_decide⟩

theorem test1_postcondition :
  postcondition test1_xs test1_Expected := by
  unfold postcondition test1_xs test1_Expected
  native_decide

theorem test3_precondition :
  precondition test3_xs := by
  unfold precondition test3_xs
  constructor
  · native_decide
  · exact ⟨2, by native_decide, by native_decide⟩

theorem test3_postcondition :
  postcondition test3_xs test3_Expected := by
  unfold postcondition test3_xs test3_Expected
  native_decide

theorem test6_precondition :
  precondition test6_xs := by
  unfold precondition test6_xs
  constructor
  · native_decide
  · exact ⟨42, by native_decide, by native_decide⟩

theorem test6_postcondition :
  postcondition test6_xs test6_Expected := by
  unfold postcondition test6_xs test6_Expected
  constructor
  · simp
  · native_decide

theorem uniqueness_0
    (xs : List ℕ)
    (hpre : precondition xs)
    (ret1 : ℕ)
    (ret2 : ℕ)
    (hmem1 : ret1 ∈ xs)
    (hmem2 : ret2 ∈ xs)
    (hne : ¬ret1 = ret2)
    (hne' : ¬ret1 = ret2)
    (hcount1 : xs.length / 2 < List.count ret1 xs)
    (hcount2 : xs.length / 2 < List.count ret2 xs)
    (count1_bound : xs.length / 2 + 1 ≤ List.count ret1 xs)
    (count2_bound : xs.length / 2 + 1 ≤ List.count ret2 xs)
    (sum_bound : xs.length / 2 + 1 + (xs.length / 2 + 1) ≤ List.count ret1 xs + List.count ret2 xs)
    : xs.length / 2 + 1 + (xs.length / 2 + 1) = xs.length / 2 * 2 + 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_1
    (xs : List ℕ)
    (hpre : precondition xs)
    (ret1 : ℕ)
    (ret2 : ℕ)
    (hmem1 : ret1 ∈ xs)
    (hmem2 : ret2 ∈ xs)
    (hne : ¬ret1 = ret2)
    (hne' : ¬ret1 = ret2)
    (sum_simplified : xs.length / 2 + 1 + (xs.length / 2 + 1) = xs.length / 2 * 2 + 2)
    (hcount1 : xs.length / 2 < List.count ret1 xs)
    (hcount2 : xs.length / 2 < List.count ret2 xs)
    (count1_bound : xs.length / 2 + 1 ≤ List.count ret1 xs)
    (count2_bound : xs.length / 2 + 1 ≤ List.count ret2 xs)
    (sum_bound : xs.length / 2 + 1 + (xs.length / 2 + 1) ≤ List.count ret1 xs + List.count ret2 xs)
    : xs.length < xs.length / 2 * 2 + 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2
    (xs : List ℕ)
    (hpre : precondition xs)
    (ret1 : ℕ)
    (ret2 : ℕ)
    (hmem1 : ret1 ∈ xs)
    (hmem2 : ret2 ∈ xs)
    (hne : ¬ret1 = ret2)
    (hne' : ¬ret1 = ret2)
    (sum_simplified : xs.length / 2 + 1 + (xs.length / 2 + 1) = xs.length / 2 * 2 + 2)
    (hcount1 : xs.length / 2 < List.count ret1 xs)
    (hcount2 : xs.length / 2 < List.count ret2 xs)
    (count1_bound : xs.length / 2 + 1 ≤ List.count ret1 xs)
    (count2_bound : xs.length / 2 + 1 ≤ List.count ret2 xs)
    (sum_bound : xs.length / 2 + 1 + (xs.length / 2 + 1) ≤ List.count ret1 xs + List.count ret2 xs)
    (div2_property : xs.length < xs.length / 2 * 2 + 2)
    : xs.length < List.count ret1 xs + List.count ret2 xs := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_3
    (xs : List ℕ)
    (hpre : precondition xs)
    (ret1 : ℕ)
    (ret2 : ℕ)
    (hmem1 : ret1 ∈ xs)
    (hmem2 : ret2 ∈ xs)
    (hne : ¬ret1 = ret2)
    (hne' : ¬ret1 = ret2)
    (sum_simplified : xs.length / 2 + 1 + (xs.length / 2 + 1) = xs.length / 2 * 2 + 2)
    (length_partition : xs.length = (List.filter (fun x ↦ x == ret1) xs).length + (List.filter (fun x ↦ x != ret1) xs).length)
    (count_eq_filter : List.count ret1 xs = (List.filter (fun x ↦ x == ret1) xs).length)
    (hcount1 : xs.length / 2 < List.count ret1 xs)
    (hcount2 : xs.length / 2 < List.count ret2 xs)
    (count1_bound : xs.length / 2 + 1 ≤ List.count ret1 xs)
    (count2_bound : xs.length / 2 + 1 ≤ List.count ret2 xs)
    (sum_bound : xs.length / 2 + 1 + (xs.length / 2 + 1) ≤ List.count ret1 xs + List.count ret2 xs)
    (div2_property : xs.length < xs.length / 2 * 2 + 2)
    (sum_exceeds : xs.length < List.count ret1 xs + List.count ret2 xs)
    : List.count ret2 xs ≤ (List.filter (fun x ↦ x != ret1) xs).length := by
    -- Since ret1 ≠ ret2, we have (ret2 != ret1) = true
    have h_ret2_ne_ret1 : (ret2 != ret1) = true := by
      simp only [bne, Bool.not_eq_eq_eq_not, Bool.not_true]
      simp only [beq_eq_false_iff_ne]
      exact fun h => hne h.symm
    -- Use the fact that count ret2 in filtered list equals count ret2 in original list
    have h_count_eq : List.count ret2 (List.filter (fun x ↦ x != ret1) xs) = List.count ret2 xs := by
      exact List.count_filter h_ret2_ne_ret1
    -- count of ret2 in filtered list is at most length of filtered list
    have h_count_le : List.count ret2 (List.filter (fun x ↦ x != ret1) xs) ≤ (List.filter (fun x ↦ x != ret1) xs).length := by
      exact List.count_le_length
    -- Combine: count ret2 xs = count ret2 (filter ...) ≤ length (filter ...)
    rw [← h_count_eq]
    exact h_count_le

theorem uniqueness_4
    (xs : List ℕ)
    (hpre : precondition xs)
    (ret1 : ℕ)
    (ret2 : ℕ)
    (hmem1 : ret1 ∈ xs)
    (hmem2 : ret2 ∈ xs)
    (hne : ¬ret1 = ret2)
    (hne' : ¬ret1 = ret2)
    (sum_simplified : xs.length / 2 + 1 + (xs.length / 2 + 1) = xs.length / 2 * 2 + 2)
    (length_partition : xs.length = (List.filter (fun x ↦ x == ret1) xs).length + (List.filter (fun x ↦ x != ret1) xs).length)
    (count_eq_filter : List.count ret1 xs = (List.filter (fun x ↦ x == ret1) xs).length)
    (count2_in_rest : List.count ret2 xs ≤ (List.filter (fun x ↦ x != ret1) xs).length)
    (hcount1 : xs.length / 2 < List.count ret1 xs)
    (hcount2 : xs.length / 2 < List.count ret2 xs)
    (count1_bound : xs.length / 2 + 1 ≤ List.count ret1 xs)
    (count2_bound : xs.length / 2 + 1 ≤ List.count ret2 xs)
    (sum_bound : xs.length / 2 + 1 + (xs.length / 2 + 1) ≤ List.count ret1 xs + List.count ret2 xs)
    (div2_property : xs.length < xs.length / 2 * 2 + 2)
    (sum_exceeds : xs.length < List.count ret1 xs + List.count ret2 xs)
    : List.count ret1 xs + List.count ret2 xs ≤ xs.length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (xs : List Nat):
  precondition xs →
  (∀ ret1 ret2,
    postcondition xs ret1 →
    postcondition xs ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hmem1, hcount1⟩ := hpost1
  obtain ⟨hmem2, hcount2⟩ := hpost2
  by_contra hne
  have hne' : ret1 ≠ ret2 := hne
  have count1_bound : xs.count ret1 ≥ xs.length / 2 + 1 := by (try simp at *; expose_names); exact (hcount1); done
  have count2_bound : xs.count ret2 ≥ xs.length / 2 + 1 := by (try simp at *; expose_names); exact (hcount2); done
  have sum_bound : xs.count ret1 + xs.count ret2 ≥ xs.length / 2 + 1 + (xs.length / 2 + 1) := by (try simp at *; expose_names); exact (Nat.add_le_add hcount1 hcount2); done
  have sum_simplified : xs.length / 2 + 1 + (xs.length / 2 + 1) = xs.length / 2 * 2 + 2 := by (try simp at *; expose_names); exact (uniqueness_0 xs hpre ret1 ret2 hmem1 hmem2 hne hne' hcount1 hcount2 count1_bound count2_bound sum_bound); done
  have div2_property : xs.length / 2 * 2 + 2 > xs.length := by (try simp at *; expose_names); exact (uniqueness_1 xs hpre ret1 ret2 hmem1 hmem2 hne hne' sum_simplified hcount1 hcount2 count1_bound count2_bound sum_bound); done
  have sum_exceeds : xs.count ret1 + xs.count ret2 > xs.length := by (try simp at *; expose_names); exact (uniqueness_2 xs hpre ret1 ret2 hmem1 hmem2 hne hne' sum_simplified hcount1 hcount2 count1_bound count2_bound sum_bound div2_property); done
  have length_partition : xs.length = (xs.filter (· == ret1)).length + (xs.filter (· != ret1)).length := by (try simp at *; expose_names); exact (List.length_eq_length_filter_add fun x ↦ x == ret1); done
  have count_eq_filter : xs.count ret1 = (xs.filter (· == ret1)).length := by (try simp at *; expose_names); exact (List.count_eq_length_filter); done
  have count2_in_rest : xs.count ret2 ≤ (xs.filter (· != ret1)).length := by (try simp at *; expose_names); exact (uniqueness_3 xs hpre ret1 ret2 hmem1 hmem2 hne hne' sum_simplified length_partition count_eq_filter hcount1 hcount2 count1_bound count2_bound sum_bound div2_property sum_exceeds); done
  have sum_le_length : xs.count ret1 + xs.count ret2 ≤ xs.length := by (try simp at *; expose_names); exact (uniqueness_4 xs hpre ret1 ret2 hmem1 hmem2 hne hne' sum_simplified length_partition count_eq_filter count2_in_rest hcount1 hcount2 count1_bound count2_bound sum_bound div2_property sum_exceeds); done
  exact Nat.lt_irrefl xs.length (Nat.lt_of_lt_of_le sum_exceeds sum_le_length)
end Proof
