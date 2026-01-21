import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def coveredSet (intervals : List (Nat × Nat)) : Set Nat :=
  {x | ∃ interval ∈ intervals, interval.1 ≤ x ∧ x < interval.2}


def removeAt (l : List α) (i : Nat) : List α :=
  l.take i ++ l.drop (i + 1)



def precondition (intervals : List (Nat × Nat)) :=
  intervals.length ≥ 1



def ensures1 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∃ i : Nat, i < intervals.length ∧ result = Nat.card (coveredSet (removeAt intervals i))


def ensures2 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∀ i : Nat, i < intervals.length → Nat.card (coveredSet (removeAt intervals i)) ≤ result

def postcondition (intervals : List (Nat × Nat)) (result : Nat) :=
  ensures1 intervals result ∧ ensures2 intervals result


def test1_intervals : List (Nat × Nat) := [(1, 3), (2, 5), (6, 8)]

def test1_Expected : Nat := 5

def test6_intervals : List (Nat × Nat) := [(1, 5)]

def test6_Expected : Nat := 0

def test9_intervals : List (Nat × Nat) := [(0, 4), (1, 3), (2, 6)]

def test9_Expected : Nat := 6







section Proof
theorem test1_precondition :
  precondition test1_intervals := by
  unfold precondition test1_intervals
  decide

theorem test1_postcondition_0
    (h_unfold : postcondition test1_intervals test1_Expected ↔ ensures1 test1_intervals test1_Expected ∧ ensures2 test1_intervals test1_Expected)
    (h_len : test1_intervals.length = 3)
    : ensures1 test1_intervals test1_Expected := by
    unfold ensures1 test1_intervals test1_Expected
    use 0
    constructor
    · simp
    · -- Need to show 5 = Nat.card (coveredSet (removeAt [(1, 3), (2, 5), (6, 8)] 0))
      unfold removeAt coveredSet
      simp only [List.take_zero, List.nil_append, List.drop_succ_cons, List.drop_zero]
      -- Now we need: 5 = Nat.card {x | ∃ interval ∈ [(2, 5), (6, 8)], interval.1 ≤ x ∧ x < interval.2}
      have h_eq : {x : Nat | ∃ interval ∈ [(2, 5), (6, 8)], interval.1 ≤ x ∧ x < interval.2} = {2, 3, 4, 6, 7} := by
        ext x
        simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton, Set.mem_insert_iff]
        constructor
        · intro ⟨interval, h_mem, h_le, h_lt⟩
          cases h_mem with
          | inl h1 =>
            -- interval = (2, 5)
            simp only [h1] at h_le h_lt
            simp only [Set.mem_singleton_iff]
            omega
          | inr h2 =>
            cases h2 with
            | inl h3 =>
              -- interval = (6, 8)
              simp only [h3] at h_le h_lt
              simp only [Set.mem_singleton_iff]
              omega
            | inr h4 =>
              simp at h4
        · intro h
          simp only [Set.mem_singleton_iff] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact ⟨(2, 5), Or.inl rfl, by omega, by omega⟩
          · exact ⟨(2, 5), Or.inl rfl, by omega, by omega⟩
          · exact ⟨(2, 5), Or.inl rfl, by omega, by omega⟩
          · exact ⟨(6, 8), Or.inr (Or.inl rfl), by omega, by omega⟩
          · exact ⟨(6, 8), Or.inr (Or.inl rfl), by omega, by omega⟩
      rw [h_eq]
      -- Now need to show 5 = Nat.card {2, 3, 4, 6, 7}
      have h_finite : Set.Finite ({2, 3, 4, 6, 7} : Set Nat) := by
        apply Set.Finite.insert
        apply Set.Finite.insert
        apply Set.Finite.insert
        apply Set.Finite.insert
        exact Set.finite_singleton 7
      rw [Nat.card_eq_card_finite_toFinset h_finite]
      have h_finset : h_finite.toFinset = {2, 3, 4, 6, 7} := by
        ext x
        simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      rw [h_finset]
      native_decide

theorem test1_postcondition_1
    (h_unfold : postcondition test1_intervals test1_Expected ↔ ensures1 test1_intervals test1_Expected ∧ ensures2 test1_intervals test1_Expected)
    (h_len : test1_intervals.length = 3)
    (h_ensures1 : ensures1 test1_intervals test1_Expected)
    : (coveredSet (removeAt test1_intervals 0)).ncard ≤ test1_Expected := by
    unfold test1_intervals removeAt test1_Expected coveredSet
    simp only [List.take, List.drop, List.nil_append]
    have h_eq : {x : Nat | ∃ interval ∈ [(2, 5), (6, 8)], interval.1 ≤ x ∧ x < interval.2} =
                ({2, 3, 4, 6, 7} : Set Nat) := by
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton, Set.mem_insert_iff,
                 List.not_mem_nil, or_false, Set.mem_singleton_iff]
      constructor
      · intro ⟨interval, h_mem, h_le, h_lt⟩
        rcases h_mem with rfl | rfl
        · interval_cases x <;> simp_all
        · interval_cases x <;> simp_all
      · intro h
        rcases h with rfl | rfl | rfl | rfl | rfl <;>
        first | exact ⟨(2, 5), by simp, by omega, by omega⟩
              | exact ⟨(6, 8), by simp, by omega, by omega⟩
    rw [h_eq]
    have h7 : (7 : Nat) ∉ (∅ : Set Nat) := Set.not_mem_empty 7
    have h6 : (6 : Nat) ∉ ({7} : Set Nat) := by simp
    have h4 : (4 : Nat) ∉ ({6, 7} : Set Nat) := by simp
    have h3 : (3 : Nat) ∉ ({4, 6, 7} : Set Nat) := by simp
    have h2 : (2 : Nat) ∉ ({3, 4, 6, 7} : Set Nat) := by simp
    have hc1 : ({7} : Set Nat).ncard = 1 := Set.ncard_singleton 7
    have hc2 : ({6, 7} : Set Nat).ncard = 2 := by
      rw [Set.ncard_insert_of_not_mem h6]
      · rw [hc1]
    have hc3 : ({4, 6, 7} : Set Nat).ncard = 3 := by
      rw [Set.ncard_insert_of_not_mem h4]
      · rw [hc2]
    have hc4 : ({3, 4, 6, 7} : Set Nat).ncard = 4 := by
      rw [Set.ncard_insert_of_not_mem h3]
      · rw [hc3]
    have hc5 : ({2, 3, 4, 6, 7} : Set Nat).ncard = 5 := by
      rw [Set.ncard_insert_of_not_mem h2]
      · rw [hc4]
    omega

theorem test1_postcondition_2
    (h_unfold : postcondition test1_intervals test1_Expected ↔ ensures1 test1_intervals test1_Expected ∧ ensures2 test1_intervals test1_Expected)
    (h_len : test1_intervals.length = 3)
    (h_ensures1 : ensures1 test1_intervals test1_Expected)
    (h_case0 : (coveredSet (removeAt test1_intervals 0)).ncard ≤ test1_Expected)
    : (coveredSet (removeAt test1_intervals 1)).ncard ≤ test1_Expected := by
    -- Simplify to get the concrete list
    have h_removed : removeAt test1_intervals 1 = [(1, 3), (6, 8)] := by native_decide
    rw [h_removed]
    -- Show the covered set equals {1, 2, 6, 7}
    have h_set_eq : coveredSet [(1, 3), (6, 8)] = {1, 2, 6, 7} := by
      unfold coveredSet
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 or_false, Set.mem_insert_iff]
      constructor
      · rintro ⟨interval, h_mem, h_le, h_lt⟩
        rcases h_mem with rfl | rfl
        · -- interval = (1, 3)
          simp only [Prod.fst, Prod.snd] at h_le h_lt
          interval_cases x <;> simp_all
        · -- interval = (6, 8)
          simp only [Prod.fst, Prod.snd] at h_le h_lt
          interval_cases x <;> simp_all
      · intro h
        rcases h with rfl | rfl | rfl | rfl
        · exact ⟨(1, 3), Or.inl rfl, by decide, by decide⟩
        · exact ⟨(1, 3), Or.inl rfl, by decide, by decide⟩
        · exact ⟨(6, 8), Or.inr rfl, by decide, by decide⟩
        · exact ⟨(6, 8), Or.inr rfl, by decide, by decide⟩
    rw [h_set_eq]
    -- Now compute ncard {1, 2, 6, 7}
    have h1 : (1 : Nat) ∉ ({2, 6, 7} : Set Nat) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have h2 : (2 : Nat) ∉ ({6, 7} : Set Nat) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have h6 : (6 : Nat) ∉ ({7} : Set Nat) := by
      simp only [Set.mem_singleton_iff]
      omega
    have h_ncard : ({1, 2, 6, 7} : Set Nat).ncard = 4 := by
      have eq1 : ({1, 2, 6, 7} : Set Nat) = insert 1 {2, 6, 7} := rfl
      have eq2 : ({2, 6, 7} : Set Nat) = insert 2 {6, 7} := rfl
      have eq3 : ({6, 7} : Set Nat) = insert 6 {7} := rfl
      rw [eq1, Set.ncard_insert_of_not_mem h1]
      rw [eq2, Set.ncard_insert_of_not_mem h2]
      rw [eq3, Set.ncard_insert_of_not_mem h6]
      rw [Set.ncard_singleton]
    rw [h_ncard]
    unfold test1_Expected
    decide

theorem test1_postcondition_3
    (h_unfold : postcondition test1_intervals test1_Expected ↔ ensures1 test1_intervals test1_Expected ∧ ensures2 test1_intervals test1_Expected)
    (h_len : test1_intervals.length = 3)
    (h_ensures1 : ensures1 test1_intervals test1_Expected)
    (h_case0 : (coveredSet (removeAt test1_intervals 0)).ncard ≤ test1_Expected)
    (h_case1 : (coveredSet (removeAt test1_intervals 1)).ncard ≤ test1_Expected)
    : (coveredSet (removeAt test1_intervals 2)).ncard ≤ test1_Expected := by
    -- First, let's compute removeAt test1_intervals 2
    unfold test1_intervals removeAt
    simp only [List.take, List.drop, List.append_nil]
    -- Now we have coveredSet [(1, 3), (2, 5)]
    -- The covered set is {1, 2, 3, 4}
    have h_set_eq : coveredSet [(1, 3), (2, 5)] = {1, 2, 3, 4} := by
      ext x
      simp only [coveredSet, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
                 Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨interval, h_mem, h_lo, h_hi⟩
        rcases h_mem with rfl | rfl
        · -- interval = (1, 3)
          omega
        · -- interval = (2, 5)
          omega
      · intro h
        rcases h with rfl | rfl | rfl | rfl
        · exact ⟨(1, 3), Or.inl rfl, by omega, by omega⟩
        · exact ⟨(1, 3), Or.inl rfl, by omega, by omega⟩
        · exact ⟨(2, 5), Or.inr rfl, by omega, by omega⟩
        · exact ⟨(2, 5), Or.inr rfl, by omega, by omega⟩
    rw [h_set_eq]
    -- Now we need to show {1, 2, 3, 4}.ncard ≤ 5
    have h_ncard : ({1, 2, 3, 4} : Set Nat).ncard = 4 := by
      have h1 : (1 : Nat) ∉ ({2, 3, 4} : Set Nat) := by decide
      have h2 : (2 : Nat) ∉ ({3, 4} : Set Nat) := by decide
      have h3 : (3 : Nat) ∉ ({4} : Set Nat) := by decide
      rw [Set.ncard_insert_of_not_mem h1]
      rw [Set.ncard_insert_of_not_mem h2]
      rw [Set.ncard_insert_of_not_mem h3]
      rw [Set.ncard_singleton]
    rw [h_ncard]
    unfold test1_Expected
    omega

theorem test1_postcondition_4
    (h_unfold : postcondition test1_intervals test1_Expected ↔ ensures1 test1_intervals test1_Expected ∧ ensures2 test1_intervals test1_Expected)
    (h_len : test1_intervals.length = 3)
    (h_ensures1 : ensures1 test1_intervals test1_Expected)
    (h_case0 : (coveredSet (removeAt test1_intervals 0)).ncard ≤ test1_Expected)
    (h_case1 : (coveredSet (removeAt test1_intervals 1)).ncard ≤ test1_Expected)
    (h_case2 : (coveredSet (removeAt test1_intervals 2)).ncard ≤ test1_Expected)
    : ensures2 test1_intervals test1_Expected := by
    unfold ensures2
    intro i hi
    rw [h_len] at hi
    have h_ncard_eq : ∀ s : Set Nat, Nat.card s = s.ncard := fun s => Nat.card_coe_set_eq s
    interval_cases i
    · rw [h_ncard_eq]; exact h_case0
    · rw [h_ncard_eq]; exact h_case1
    · rw [h_ncard_eq]; exact h_case2

theorem test1_postcondition :
  postcondition test1_intervals test1_Expected := by
  -- Unfold the main postcondition definition
  have h_unfold : postcondition test1_intervals test1_Expected ↔ ensures1 test1_intervals test1_Expected ∧ ensures2 test1_intervals test1_Expected := by
    (try simp at *; expose_names); exact Eq.to_iff rfl; done
  -- The list has length 3
  have h_len : test1_intervals.length = 3 := by
    (try simp at *; expose_names); exact rfl; done
  -- Prove ensures1: witness i = 0 works, since removing (1,3) leaves covered set {2,3,4,6,7} with card 5
  have h_ensures1 : ensures1 test1_intervals test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_0 h_unfold h_len); done
  -- For ensures2, we need to verify all three cases have cardinality ≤ 5
  -- Case i = 0: removing (1,3) gives covered set with card 5
  have h_case0 : Nat.card (coveredSet (removeAt test1_intervals 0)) ≤ test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_1 h_unfold h_len h_ensures1); done
  -- Case i = 1: removing (2,5) gives covered set with card 4
  have h_case1 : Nat.card (coveredSet (removeAt test1_intervals 1)) ≤ test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_2 h_unfold h_len h_ensures1 h_case0); done
  -- Case i = 2: removing (6,8) gives covered set with card 4
  have h_case2 : Nat.card (coveredSet (removeAt test1_intervals 2)) ≤ test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_3 h_unfold h_len h_ensures1 h_case0 h_case1); done
  -- Combine the three cases to prove ensures2
  have h_ensures2 : ensures2 test1_intervals test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_4 h_unfold h_len h_ensures1 h_case0 h_case1 h_case2); done
  -- Final step: combine ensures1 and ensures2 using the equivalence
  rw [h_unfold]
  exact ⟨h_ensures1, h_ensures2⟩

theorem test6_precondition :
  precondition test6_intervals := by
  unfold precondition test6_intervals
  decide

theorem test6_postcondition :
  postcondition test6_intervals test6_Expected := by
  have h_unfold : postcondition test6_intervals test6_Expected ↔ ensures1 test6_intervals test6_Expected ∧ ensures2 test6_intervals test6_Expected := by
    unfold postcondition
    rfl
  have h_len : test6_intervals.length = 1 := by
    unfold test6_intervals
    rfl
  have h_removeAt_0 : removeAt test6_intervals 0 = [] := by
    unfold removeAt test6_intervals
    simp only [List.take_zero, List.nil_append, List.drop_succ_cons, List.drop_zero]
  have h_coveredSet_empty : coveredSet [] = ∅ := by
    unfold coveredSet
    ext x
    simp only [Set.mem_setOf_eq, List.not_mem_nil, false_and, exists_false, Set.mem_empty_iff_false]
  have h_empty_isEmpty : IsEmpty (∅ : Set Nat) := by
    rw [Set.isEmpty_coe_sort]
  have h_card_empty : Nat.card (∅ : Set Nat) = 0 := by
    rw [Nat.card_eq_zero]
    left
    exact h_empty_isEmpty
  have h_card_removeAt_0 : Nat.card (coveredSet (removeAt test6_intervals 0)) = 0 := by
    rw [h_removeAt_0, h_coveredSet_empty]
    exact h_card_empty
  have h_ensures1 : ensures1 test6_intervals test6_Expected := by
    unfold ensures1 test6_Expected
    use 0
    constructor
    · rw [h_len]; exact Nat.zero_lt_one
    · exact h_card_removeAt_0.symm
  have h_ensures2 : ensures2 test6_intervals test6_Expected := by
    unfold ensures2 test6_Expected
    intro i hi
    rw [h_len] at hi
    have h_i_eq_0 : i = 0 := by
      exact Nat.lt_one_iff.mp hi
    rw [h_i_eq_0, h_card_removeAt_0]
  rw [h_unfold]
  exact ⟨h_ensures1, h_ensures2⟩

theorem test9_precondition :
  precondition test9_intervals := by
  unfold precondition test9_intervals
  decide

theorem test9_postcondition_0
    (h_unfold : postcondition test9_intervals test9_Expected ↔ ensures1 test9_intervals test9_Expected ∧ ensures2 test9_intervals test9_Expected)
    (h_len : test9_intervals.length = 3)
    (h_removeAt_0 : removeAt test9_intervals 0 = [(1, 3), (2, 6)])
    (h_removeAt_1 : removeAt test9_intervals 1 = [(0, 4), (2, 6)])
    (h_removeAt_2 : removeAt test9_intervals 2 = [(0, 4), (1, 3)])
    : coveredSet [(1, 3), (2, 6)] = {1, 2, 3, 4, 5} := by
    apply Set.ext
    intro x
    simp only [coveredSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨interval, h_mem, h_bounds⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_mem
      rcases h_mem with rfl | rfl
      · -- interval = (1, 3)
        omega
      · -- interval = (2, 6)
        omega
    · intro h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · -- x = 1
        exact ⟨(1, 3), by simp [List.mem_cons], by omega⟩
      · -- x = 2
        exact ⟨(1, 3), by simp [List.mem_cons], by omega⟩
      · -- x = 3
        exact ⟨(2, 6), by simp [List.mem_cons], by omega⟩
      · -- x = 4
        exact ⟨(2, 6), by simp [List.mem_cons], by omega⟩
      · -- x = 5
        exact ⟨(2, 6), by simp [List.mem_cons], by omega⟩

theorem test9_postcondition_1
    (h_unfold : postcondition test9_intervals test9_Expected ↔ ensures1 test9_intervals test9_Expected ∧ ensures2 test9_intervals test9_Expected)
    (h_len : test9_intervals.length = 3)
    (h_removeAt_0 : removeAt test9_intervals 0 = [(1, 3), (2, 6)])
    (h_removeAt_1 : removeAt test9_intervals 1 = [(0, 4), (2, 6)])
    (h_removeAt_2 : removeAt test9_intervals 2 = [(0, 4), (1, 3)])
    (h_coveredSet_0 : coveredSet [(1, 3), (2, 6)] = {1, 2, 3, 4, 5})
    : coveredSet [(0, 4), (2, 6)] = {0, 1, 2, 3, 4, 5} := by
    apply Set.ext
    intro x
    constructor
    · -- Forward: x ∈ coveredSet → x ∈ {0, 1, 2, 3, 4, 5}
      intro hx
      simp only [coveredSet, Set.mem_setOf_eq] at hx
      obtain ⟨interval, h_mem, h_bounds⟩ := hx
      simp only [List.mem_cons, List.mem_singleton] at h_mem
      cases h_mem with
      | inl h_eq =>
        subst h_eq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      | inr h_eq =>
        cases h_eq with
        | inl h_eq2 =>
          subst h_eq2
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        | inr h_nil =>
          simp at h_nil
    · -- Backward: x ∈ {0, 1, 2, 3, 4, 5} → x ∈ coveredSet
      intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      simp only [coveredSet, Set.mem_setOf_eq]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · -- x = 0
        refine ⟨(0, 4), ?_, ?_⟩
        · simp [List.mem_cons]
        · omega
      · -- x = 1
        refine ⟨(0, 4), ?_, ?_⟩
        · simp [List.mem_cons]
        · omega
      · -- x = 2
        refine ⟨(0, 4), ?_, ?_⟩
        · simp [List.mem_cons]
        · omega
      · -- x = 3
        refine ⟨(0, 4), ?_, ?_⟩
        · simp [List.mem_cons]
        · omega
      · -- x = 4
        refine ⟨(2, 6), ?_, ?_⟩
        · simp [List.mem_cons]
        · omega
      · -- x = 5
        refine ⟨(2, 6), ?_, ?_⟩
        · simp [List.mem_cons]
        · omega

theorem test9_postcondition_2
    (h_unfold : postcondition test9_intervals test9_Expected ↔ ensures1 test9_intervals test9_Expected ∧ ensures2 test9_intervals test9_Expected)
    (h_len : test9_intervals.length = 3)
    (h_removeAt_0 : removeAt test9_intervals 0 = [(1, 3), (2, 6)])
    (h_removeAt_1 : removeAt test9_intervals 1 = [(0, 4), (2, 6)])
    (h_removeAt_2 : removeAt test9_intervals 2 = [(0, 4), (1, 3)])
    (h_coveredSet_0 : coveredSet [(1, 3), (2, 6)] = {1, 2, 3, 4, 5})
    (h_coveredSet_1 : coveredSet [(0, 4), (2, 6)] = {0, 1, 2, 3, 4, 5})
    : coveredSet [(0, 4), (1, 3)] = {0, 1, 2, 3} := by
  apply Set.ext
  intro x
  constructor
  · -- Forward direction: x ∈ coveredSet [(0, 4), (1, 3)] → x ∈ {0, 1, 2, 3}
    intro hx
    simp only [coveredSet, Set.mem_setOf_eq] at hx
    obtain ⟨interval, h_mem, h_bounds⟩ := hx
    simp only [List.mem_cons, List.mem_singleton] at h_mem
    cases h_mem with
    | inl h_eq =>
      subst h_eq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    | inr h_eq =>
      cases h_eq with
      | inl h_eq =>
        subst h_eq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      | inr h_eq =>
        simp only [List.not_mem_nil] at h_eq
  · -- Backward direction: x ∈ {0, 1, 2, 3} → x ∈ coveredSet [(0, 4), (1, 3)]
    intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [coveredSet, Set.mem_setOf_eq]
    use (0, 4)
    constructor
    · simp only [List.mem_cons, List.mem_singleton, true_or]
    · omega
end Proof
