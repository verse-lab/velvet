import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def pointInInterval (x : Int) (interval : Int × Int) : Prop :=
  interval.1 ≤ x ∧ x ≤ interval.2


def pointCoveredByList (x : Int) (intervals : List (Int × Int)) : Prop :=
  ∃ interval ∈ intervals, pointInInterval x interval


def intervalsDisjoint (i1 : Int × Int) (i2 : Int × Int) : Prop :=
  i2.1 > i1.2 ∨ i1.1 > i2.2


def validInterval (interval : Int × Int) : Prop :=
  interval.1 ≤ interval.2


def allValid (intervals : List (Int × Int)) : Prop :=
  ∀ interval ∈ intervals, validInterval interval


def pairwiseDisjoint (intervals : List (Int × Int)) : Prop :=
  ∀ i : Nat, ∀ j : Nat, i < intervals.length → j < intervals.length → i ≠ j →
    intervalsDisjoint intervals[i]! intervals[j]!


def sortedByStart (intervals : List (Int × Int)) : Prop :=
  ∀ i : Nat, ∀ j : Nat, i < j → j < intervals.length →
    intervals[i]!.2 < intervals[j]!.1



def precondition (intervals : List (Int × Int)) :=
  allValid intervals



def ensures1 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  allValid result


def ensures2 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ∀ x : Int, pointCoveredByList x intervals → pointCoveredByList x result


def ensures3 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ∀ x : Int, pointCoveredByList x result → pointCoveredByList x intervals


def ensures4 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  sortedByStart result


def ensures5 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  pairwiseDisjoint result

def postcondition (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ensures1 intervals result ∧
  ensures2 intervals result ∧
  ensures3 intervals result ∧
  ensures4 intervals result ∧
  ensures5 intervals result


def test1_intervals : List (Int × Int) := [(1, 3), (2, 6), (8, 10), (15, 18)]

def test1_Expected : List (Int × Int) := [(1, 6), (8, 10), (15, 18)]

def test2_intervals : List (Int × Int) := [(1, 4), (4, 5)]

def test2_Expected : List (Int × Int) := [(1, 5)]

def test5_intervals : List (Int × Int) := [(5, 6), (1, 3), (2, 4)]

def test5_Expected : List (Int × Int) := [(1, 4), (5, 6)]







section Proof
theorem test1_precondition :
  precondition test1_intervals := by
  unfold precondition allValid validInterval test1_intervals
  intro interval h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem test1_postcondition :
  postcondition test1_intervals test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold allValid validInterval pointCoveredByList pointInInterval
  unfold sortedByStart pairwiseDisjoint intervalsDisjoint
  unfold test1_intervals test1_Expected
  constructor
  · -- ensures1: allValid result
    intro interval h_mem
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl | rfl
    · omega
    · omega
    · omega
  constructor
  · -- ensures2: coverage intervals → result
    intro x ⟨interval, h_mem, h_in⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl | rfl | rfl
    · exact ⟨(1, 6), by simp, by omega⟩
    · exact ⟨(1, 6), by simp, by omega⟩
    · exact ⟨(8, 10), by simp, by omega⟩
    · exact ⟨(15, 18), by simp, by omega⟩
  constructor
  · -- ensures3: coverage result → intervals
    intro x ⟨interval, h_mem, h_in⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl | rfl
    · -- x in (1, 6), need to find covering interval in original
      by_cases h : x ≤ 3
      · exact ⟨(1, 3), by simp, by omega⟩
      · exact ⟨(2, 6), by simp, by omega⟩
    · exact ⟨(8, 10), by simp, by omega⟩
    · exact ⟨(15, 18), by simp, by omega⟩
  constructor
  · -- ensures4: sortedByStart
    intro i j hij hj
    simp only [List.length_cons, List.length_singleton, List.length_nil] at hj
    have hi : i < 3 := Nat.lt_trans hij hj
    interval_cases i <;> interval_cases j <;> simp_all [List.getElem!_cons_zero, List.getElem!_cons_succ]
  · -- ensures5: pairwiseDisjoint
    intro i j hi hj hne
    simp only [List.length_cons, List.length_singleton, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all [List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem test2_precondition :
  precondition test2_intervals := by
  unfold precondition allValid validInterval test2_intervals
  intro interval h
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl
  · decide
  · decide

theorem test2_postcondition :
  postcondition test2_intervals test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold allValid validInterval pointCoveredByList pointInInterval
  unfold sortedByStart pairwiseDisjoint intervalsDisjoint
  unfold test2_intervals test2_Expected
  constructor
  · -- ensures1: allValid [(1, 5)]
    intro interval h
    simp [List.mem_singleton] at h
    subst h
    omega
  constructor
  · -- ensures2: coverage from original to result
    intro x ⟨interval, hmem, hcover⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    use (1, 5)
    constructor
    · simp [List.mem_singleton]
    · cases hmem with
      | inl h => subst h; simp only at hcover ⊢; omega
      | inr h => subst h; simp only at hcover ⊢; omega
  constructor
  · -- ensures3: coverage from result to original
    intro x ⟨interval, hmem, hcover⟩
    simp [List.mem_singleton] at hmem
    subst hmem
    simp only at hcover
    by_cases hle : x ≤ 4
    · use (1, 4)
      constructor
      · simp
      · omega
    · use (4, 5)
      constructor
      · simp
      · omega
  constructor
  · -- ensures4: sortedByStart (vacuously true for single element)
    intro i j hij hjlen
    simp [List.length_singleton] at hjlen
    omega
  · -- ensures5: pairwiseDisjoint (vacuously true for single element)
    intro i j hilen hjlen hne
    simp [List.length_singleton] at hilen hjlen
    omega

theorem test5_precondition : precondition test5_intervals := by
  unfold precondition allValid validInterval test5_intervals
  intro interval h
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · decide
  · decide
  · decide

theorem test5_postcondition :
  postcondition test5_intervals test5_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold allValid validInterval pointCoveredByList pointInInterval
  unfold sortedByStart pairwiseDisjoint intervalsDisjoint
  unfold test5_intervals test5_Expected
  constructor
  · -- ensures1: allValid result
    intro interval h_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl
    · omega
    · omega
  constructor
  · -- ensures2: coverage from input to result
    intro x ⟨interval, h_mem, h_in⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl | rfl
    · -- interval = (5, 6)
      refine ⟨(5, 6), ?_, h_in⟩
      simp [List.mem_cons]
    · -- interval = (1, 3)
      refine ⟨(1, 4), ?_, ?_⟩
      · simp [List.mem_cons]
      · simp only at h_in ⊢
        omega
    · -- interval = (2, 4)
      refine ⟨(1, 4), ?_, ?_⟩
      · simp [List.mem_cons]
      · simp only at h_in ⊢
        omega
  constructor
  · -- ensures3: coverage from result to input
    intro x ⟨interval, h_mem, h_in⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl
    · -- interval = (1, 4)
      simp only at h_in
      by_cases hx : x ≤ 3
      · refine ⟨(1, 3), ?_, ?_⟩
        · simp [List.mem_cons]
        · simp only; omega
      · refine ⟨(2, 4), ?_, ?_⟩
        · simp [List.mem_cons]
        · simp only; omega
    · -- interval = (5, 6)
      refine ⟨(5, 6), ?_, h_in⟩
      simp [List.mem_cons]
  constructor
  · -- ensures4: sortedByStart
    intro i j h_ij h_j_lt
    simp only [List.length_cons, List.length_nil] at h_j_lt
    interval_cases j
    · omega
    · interval_cases i
      · simp
  · -- ensures5: pairwiseDisjoint
    intro i j h_i_lt h_j_lt h_neq
    simp only [List.length_cons, List.length_nil] at h_i_lt h_j_lt
    interval_cases i <;> interval_cases j <;> simp <;> omega

theorem uniqueness_0
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    : ensures1 intervals ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    : ensures2 intervals ret1 := by
    exact hpost1.2.1

theorem uniqueness_2
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    : ensures3 intervals ret1 := by
    exact hpost1.2.2.1

theorem uniqueness_3
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    : ensures4 intervals ret1 := by
    exact hpost1.2.2.2.1

theorem uniqueness_4
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    : ensures5 intervals ret1 := by
    exact hpost1.2.2.2.2

theorem uniqueness_5
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    : ensures1 intervals ret2 := by
    intros; expose_names; exact (uniqueness_0 intervals hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_6
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    : ensures2 intervals ret2 := by
    intros; expose_names; exact (uniqueness_1 intervals hpre ret2 ret1 hpost2 hpost1 h2_valid); done

theorem uniqueness_7
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    : ensures3 intervals ret2 := by
    intros; expose_names; exact (uniqueness_2 intervals hpre ret2 ret1 hpost2 hpost1 h2_valid h2_covers_input); done

theorem uniqueness_8
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    : ensures4 intervals ret2 := by
    intros; expose_names; exact (uniqueness_3 intervals hpre ret2 ret1 hpost2 hpost1 h2_valid h2_covers_input h2_covered_by_input); done

theorem uniqueness_9
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    : ensures5 intervals ret2 := by
    intros; expose_names; exact (uniqueness_4 intervals hpre ret2 ret1 hpost2 hpost1 h2_valid h2_covers_input h2_covered_by_input h2_sorted); done

theorem uniqueness_10_2
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_coverage_set_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_sorted1_def : ∀ (i j : ℕ), i < j → j < ret1.length → (ret1[i]?.getD default).2 < (ret1[j]?.getD default).1)
    (h_sorted2_def : ∀ (i j : ℕ), i < j → j < ret2.length → (ret2[i]?.getD default).2 < (ret2[j]?.getD default).1)
    : ∀ (i j : ℕ), i < ret1.length → j < ret1.length → ¬i = j → intervalsDisjoint (ret1[i]?.getD default) (ret1[j]?.getD default) := by
    intro i j hi hj hne
    unfold ensures5 pairwiseDisjoint at h1_disjoint
    have hne' : i ≠ j := hne
    have h := h1_disjoint i j hi hj hne'
    simp only [List.getElem!_eq_getElem?_getD] at h
    exact h

theorem uniqueness_10_3
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_coverage_set_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_sorted1_def : ∀ (i j : ℕ), i < j → j < ret1.length → (ret1[i]?.getD default).2 < (ret1[j]?.getD default).1)
    (h_sorted2_def : ∀ (i j : ℕ), i < j → j < ret2.length → (ret2[i]?.getD default).2 < (ret2[j]?.getD default).1)
    (h_disjoint1_def : ∀ (i j : ℕ), i < ret1.length → j < ret1.length → ¬i = j → intervalsDisjoint (ret1[i]?.getD default) (ret1[j]?.getD default))
    : ∀ (i j : ℕ), i < ret2.length → j < ret2.length → ¬i = j → intervalsDisjoint (ret2[i]?.getD default) (ret2[j]?.getD default) := by
    intro i j hi hj hne
    unfold ensures5 pairwiseDisjoint at h2_disjoint
    have h := h2_disjoint i j hi hj hne
    simp only [List.getElem!_eq_getElem?_getD] at h
    exact h

theorem uniqueness_10_0
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_coverage_set_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    : ∀ (i j : ℕ), i < j → j < ret1.length → (ret1[i]?.getD default).2 < (ret1[j]?.getD default).1 := by
    sorry

theorem uniqueness_10_1
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_coverage_set_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_sorted1_def : ∀ (i j : ℕ), i < j → j < ret1.length → (ret1[i]?.getD default).2 < (ret1[j]?.getD default).1)
    : ∀ (i j : ℕ), i < j → j < ret2.length → (ret2[i]?.getD default).2 < (ret2[j]?.getD default).1 := by
    sorry

theorem uniqueness_10_4
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_coverage_set_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (h_sorted1_def : ∀ (i j : ℕ), i < j → j < ret1.length → (ret1[i]?.getD default).2 < (ret1[j]?.getD default).1)
    (h_sorted2_def : ∀ (i j : ℕ), i < j → j < ret2.length → (ret2[i]?.getD default).2 < (ret2[j]?.getD default).1)
    (h_disjoint1_def : ∀ (i j : ℕ), i < ret1.length → j < ret1.length → ¬i = j → intervalsDisjoint (ret1[i]?.getD default) (ret1[j]?.getD default))
    (h_disjoint2_def : ∀ (i j : ℕ), i < ret2.length → j < ret2.length → ¬i = j → intervalsDisjoint (ret2[i]?.getD default) (ret2[j]?.getD default))
    (h_valid1_all : ∀ (a b : ℤ), (a, b) ∈ ret1 → validInterval (a, b))
    (h_valid2_all : ∀ (a b : ℤ), (a, b) ∈ ret2 → validInterval (a, b))
    : ret1 = ret2 := by
    sorry

theorem uniqueness_10
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    : ret1.length = ret2.length := by
    have h_coverage_set_eq : ∀ x : ℤ, pointCoveredByList x ret1 ↔ pointCoveredByList x ret2 := by (try simp at *; expose_names); exact (fun x ↦ hcoverage_eq x); done
    have h_sorted1_def : ∀ i j : ℕ, i < j → j < ret1.length → ret1[i]!.2 < ret1[j]!.1 := by (try simp at *; expose_names); exact (uniqueness_10_0 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq h_coverage_set_eq); done
    have h_sorted2_def : ∀ i j : ℕ, i < j → j < ret2.length → ret2[i]!.2 < ret2[j]!.1 := by (try simp at *; expose_names); exact (uniqueness_10_1 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq h_coverage_set_eq h_sorted1_def); done
    have h_disjoint1_def : ∀ i j : ℕ, i < ret1.length → j < ret1.length → i ≠ j → intervalsDisjoint ret1[i]! ret1[j]! := by (try simp at *; expose_names); exact (uniqueness_10_2 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq h_coverage_set_eq h_sorted1_def h_sorted2_def); done
    have h_disjoint2_def : ∀ i j : ℕ, i < ret2.length → j < ret2.length → i ≠ j → intervalsDisjoint ret2[i]! ret2[j]! := by (try simp at *; expose_names); exact (uniqueness_10_3 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq h_coverage_set_eq h_sorted1_def h_sorted2_def h_disjoint1_def); done
    have h_valid1_all : ∀ iv ∈ ret1, validInterval iv := by (try simp at *; expose_names); exact (fun a b a_1 ↦ h1_valid (a, b) a_1); done
    have h_valid2_all : ∀ iv ∈ ret2, validInterval iv := by (try simp at *; expose_names); exact (fun a b a_1 ↦ h2_valid (a, b) a_1); done
    have h_lists_eq : ret1 = ret2 := by (try simp at *; expose_names); exact (uniqueness_10_4 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq h_coverage_set_eq h_sorted1_def h_sorted2_def h_disjoint1_def h_disjoint2_def h_valid1_all h_valid2_all); done
    have h_length_from_eq : ret1 = ret2 → ret1.length = ret2.length := by (try simp at *; expose_names); exact (fun a ↦ congrArg List.length h_lists_eq); done
    exact h_length_from_eq h_lists_eq

theorem uniqueness_11
    (intervals : List (ℤ × ℤ))
    (hpre : precondition intervals)
    (ret1 : List (ℤ × ℤ))
    (ret2 : List (ℤ × ℤ))
    (hpost1 : postcondition intervals ret1)
    (hpost2 : postcondition intervals ret2)
    (h1_valid : ensures1 intervals ret1)
    (h1_covers_input : ensures2 intervals ret1)
    (h1_covered_by_input : ensures3 intervals ret1)
    (h1_sorted : ensures4 intervals ret1)
    (h1_disjoint : ensures5 intervals ret1)
    (h2_valid : ensures1 intervals ret2)
    (h2_covers_input : ensures2 intervals ret2)
    (h2_covered_by_input : ensures3 intervals ret2)
    (h2_sorted : ensures4 intervals ret2)
    (h2_disjoint : ensures5 intervals ret2)
    (hcoverage_eq : ∀ (x : ℤ), pointCoveredByList x ret1 ↔ pointCoveredByList x ret2)
    (hlen_eq : ret1.length = ret2.length)
    : ∀ (n : ℕ) (h1 : n < ret1.length) (h2 : n < ret2.length), ret1[n] = ret2[n] := by
  -- First establish the helper lemmas needed for uniqueness_10_4
  have h_sorted1_def : ∀ (i j : ℕ), i < j → j < ret1.length → (ret1[i]?.getD default).2 < (ret1[j]?.getD default).1 :=
    uniqueness_10_0 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq hcoverage_eq
  have h_sorted2_def : ∀ (i j : ℕ), i < j → j < ret2.length → (ret2[i]?.getD default).2 < (ret2[j]?.getD default).1 :=
    uniqueness_10_1 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq hcoverage_eq h_sorted1_def
  have h_disjoint1_def : ∀ (i j : ℕ), i < ret1.length → j < ret1.length → ¬i = j → intervalsDisjoint (ret1[i]?.getD default) (ret1[j]?.getD default) :=
    uniqueness_10_2 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq hcoverage_eq h_sorted1_def h_sorted2_def
  have h_disjoint2_def : ∀ (i j : ℕ), i < ret2.length → j < ret2.length → ¬i = j → intervalsDisjoint (ret2[i]?.getD default) (ret2[j]?.getD default) :=
    uniqueness_10_3 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq hcoverage_eq h_sorted1_def h_sorted2_def h_disjoint1_def
  have h_valid1_all : ∀ (a b : ℤ), (a, b) ∈ ret1 → validInterval (a, b) := by
    intro a b hmem
    exact h1_valid (a, b) hmem
  have h_valid2_all : ∀ (a b : ℤ), (a, b) ∈ ret2 → validInterval (a, b) := by
    intro a b hmem
    exact h2_valid (a, b) hmem
  -- Use uniqueness_10_4 to establish ret1 = ret2
  have h_eq : ret1 = ret2 :=
    uniqueness_10_4 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq hcoverage_eq h_sorted1_def h_sorted2_def h_disjoint1_def h_disjoint2_def h_valid1_all h_valid2_all
  -- Now the conclusion follows trivially
  intro n h1 h2
  simp [h_eq]

theorem uniqueness (intervals : List (Int × Int)):
  precondition intervals →
  (∀ ret1 ret2,
    postcondition intervals ret1 →
    postcondition intervals ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the five ensures conditions from each postcondition
  have h1_valid : ensures1 intervals ret1 := by (try simp at *; expose_names); exact (uniqueness_0 intervals hpre ret1 ret2 hpost1 hpost2); done
  have h1_covers_input : ensures2 intervals ret1 := by (try simp at *; expose_names); exact (uniqueness_1 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid); done
  have h1_covered_by_input : ensures3 intervals ret1 := by (try simp at *; expose_names); exact (uniqueness_2 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input); done
  have h1_sorted : ensures4 intervals ret1 := by (try simp at *; expose_names); exact (uniqueness_3 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input); done
  have h1_disjoint : ensures5 intervals ret1 := by (try simp at *; expose_names); exact (uniqueness_4 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted); done
  have h2_valid : ensures1 intervals ret2 := by (try simp at *; expose_names); exact (uniqueness_5 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint); done
  have h2_covers_input : ensures2 intervals ret2 := by (try simp at *; expose_names); exact (uniqueness_6 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid); done
  have h2_covered_by_input : ensures3 intervals ret2 := by (try simp at *; expose_names); exact (uniqueness_7 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input); done
  have h2_sorted : ensures4 intervals ret2 := by (try simp at *; expose_names); exact (uniqueness_8 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input); done
  have h2_disjoint : ensures5 intervals ret2 := by (try simp at *; expose_names); exact (uniqueness_9 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted); done
  -- Key: ret1 and ret2 cover exactly the same points
  have hcoverage_eq : ∀ x : Int, pointCoveredByList x ret1 ↔ pointCoveredByList x ret2 := by (try simp at *; expose_names); exact (fun x ↦ { mp := fun a ↦ h2_covers_input x (h1_covered_by_input x a), mpr := fun a ↦ h1_covers_input x (h2_covered_by_input x a) }); done
  -- For sorted disjoint valid interval lists covering the same points, they must have the same length
  have hlen_eq : ret1.length = ret2.length := by (try simp at *; expose_names); exact (uniqueness_10 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq); done
  -- For sorted disjoint valid interval lists covering the same points, corresponding elements are equal
  have helems_eq : ∀ (n : Nat) (h1 : n < ret1.length) (h2 : n < ret2.length), ret1.get ⟨n, h1⟩ = ret2.get ⟨n, h2⟩ := by (try simp at *; expose_names); exact (uniqueness_11 intervals hpre ret1 ret2 hpost1 hpost2 h1_valid h1_covers_input h1_covered_by_input h1_sorted h1_disjoint h2_valid h2_covers_input h2_covered_by_input h2_sorted h2_disjoint hcoverage_eq hlen_eq); done
  -- Apply list extensionality
  exact List.ext_get hlen_eq helems_eq
end Proof
