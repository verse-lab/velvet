import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def validDigits (l : List Nat) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! < 10


def noLeadingZeros (l : List Nat) : Prop :=
  l = [0] ∨ (l ≠ [] ∧ l.getLast! ≠ 0)



def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧
  l2.length > 0 ∧
  validDigits l1 ∧
  validDigits l2 ∧
  noLeadingZeros l1 ∧
  noLeadingZeros l2





def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=

  Nat.ofDigits 10 result = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 ∧

  validDigits result ∧

  noLeadingZeros result


def test1_l1 : List Nat := [2, 4, 3]

def test1_l2 : List Nat := [5, 6, 4]

def test1_Expected : List Nat := [7, 0, 8]

def test3_l1 : List Nat := [9, 9, 9, 9, 9, 9, 9]

def test3_l2 : List Nat := [9, 9, 9, 9]

def test3_Expected : List Nat := [8, 9, 9, 9, 0, 0, 0, 1]

def test5_l1 : List Nat := [5]

def test5_l2 : List Nat := [5]

def test5_Expected : List Nat := [0, 1]







section Proof
theorem test1_precondition :
  precondition test1_l1 test1_l2 := by
  unfold precondition test1_l1 test1_l2 validDigits noLeadingZeros
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | n + 3 => simp only [List.length_cons, List.length_nil] at hi; omega
  · intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | n + 3 => simp only [List.length_cons, List.length_nil] at hi; omega
  · right; constructor <;> native_decide
  · right; constructor <;> native_decide

theorem test1_postcondition :
  postcondition test1_l1 test1_l2 test1_Expected := by
  unfold postcondition test1_l1 test1_l2 test1_Expected
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · unfold validDigits
    intro i hi
    simp only [List.length] at hi
    interval_cases i <;> native_decide
  · unfold noLeadingZeros
    right
    constructor
    · decide
    · native_decide

theorem test3_precondition :
  precondition test3_l1 test3_l2 := by
  unfold precondition test3_l1 test3_l2 validDigits noLeadingZeros
  refine ⟨by native_decide, by native_decide, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : i < 7 := hi
    interval_cases i <;> native_decide
  · intro i hi
    have : i < 4 := hi
    interval_cases i <;> native_decide
  · right; constructor <;> native_decide
  · right; constructor <;> native_decide

theorem test3_postcondition :
  postcondition test3_l1 test3_l2 test3_Expected := by
  unfold postcondition test3_l1 test3_l2 test3_Expected
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · unfold validDigits
    intro i hi
    simp only [List.length] at hi
    interval_cases i <;> native_decide
  · unfold noLeadingZeros
    right
    constructor
    · simp
    · native_decide

theorem test5_precondition :
  precondition test5_l1 test5_l2 := by
  unfold precondition test5_l1 test5_l2 validDigits noLeadingZeros
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- l1.length > 0
    native_decide
  · -- l2.length > 0
    native_decide
  · -- validDigits l1
    intro i hi
    simp only [List.length_singleton] at hi
    interval_cases i
    native_decide
  · -- validDigits l2
    intro i hi
    simp only [List.length_singleton] at hi
    interval_cases i
    native_decide
  · -- noLeadingZeros l1
    right
    constructor
    · native_decide
    · native_decide
  · -- noLeadingZeros l2
    right
    constructor
    · native_decide
    · native_decide

theorem test5_postcondition :
  postcondition test5_l1 test5_l2 test5_Expected := by
  unfold postcondition test5_l1 test5_l2 test5_Expected
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · unfold validDigits
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> native_decide
  · unfold noLeadingZeros
    right
    constructor
    · simp
    · native_decide

theorem uniqueness_0
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 := by
    exact hpost1.1

theorem uniqueness_1
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 := by
    intros; expose_names; exact (uniqueness_0 l1 l2 hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    : validDigits ret1 := by
    exact hpost1.2.1

theorem uniqueness_3
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    : validDigits ret2 := by
    intros; expose_names; exact (uniqueness_2 l1 l2 hpre ret2 ret1 hpost2 hpost1 h_val2 h_val1); done

theorem uniqueness_4
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    : noLeadingZeros ret1 := by
    exact hpost1.2.2

theorem uniqueness_5
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    : noLeadingZeros ret2 := by
    exact hpost2.2.2

theorem uniqueness_6
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7_0
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    : ∀ i < ret1.length, ret1[i]?.getD 0 < 10 := by
    intro i hi
    have h_digit := h_valid1 i hi
    -- h_digit : ret1[i]! < 10
    -- We need to show ret1[i]?.getD 0 < 10
    -- Since i < ret1.length, ret1[i]? = some ret1[i]
    rw [List.getElem?_eq_getElem hi, Option.getD_some]
    -- Now goal is ret1[i] < 10
    -- h_digit is ret1[i]! < 10
    -- For Nat lists with valid index, ret1[i]! = ret1[i]
    unfold validDigits at h_valid1
    simp only [List.getElem!_eq_getElem?_getD] at h_digit
    rw [List.getElem?_eq_getElem hi, Option.getD_some] at h_digit
    exact h_digit

theorem uniqueness_7_1
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_index_to_mem : (∀ (i : ℕ) (h : i < ret1.length), ret1[i] < 10) ↔ ∀ a ∈ ret1, a < 10)
    (h_unfold_valid1 : ∀ i < ret1.length, ret1[i]?.getD 0 < 10)
    : ∀ (i : ℕ) (h : i < ret1.length), ret1[i] = ret1[i]?.getD 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7_2
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_index_to_mem : (∀ (i : ℕ) (h : i < ret1.length), ret1[i] < 10) ↔ ∀ a ∈ ret1, a < 10)
    (h_index_based : ∀ (i : ℕ) (h : i < ret1.length), ret1[i] < 10)
    (h_unfold_valid1 : ∀ i < ret1.length, ret1[i]?.getD 0 < 10)
    (h_getElem_eq_getElem! : ∀ (i : ℕ) (h : i < ret1.length), ret1[i] = ret1[i]?.getD 0)
    : ∀ a ∈ ret1, a < 10 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    : ∀ l ∈ ret1, l < 10 := by
    have h_unfold_valid1 : ∀ i : Nat, i < ret1.length → ret1[i]! < 10 := by (try simp at *; expose_names); exact (uniqueness_7_0 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val); done
    have h_index_to_mem : (∀ (i : Nat) (h : i < ret1.length), ret1[i]'h < 10) ↔ (∀ a, a ∈ ret1 → a < 10) := by (try simp at *; expose_names); exact (Iff.symm List.forall_mem_iff_getElem); done
    have h_getElem_eq_getElem! : ∀ (i : Nat) (h : i < ret1.length), ret1[i]'h = ret1[i]! := by (try simp at *; expose_names); exact (uniqueness_7_1 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_index_to_mem h_unfold_valid1); done
    have h_index_based : ∀ (i : Nat) (h : i < ret1.length), ret1[i]'h < 10 := by (try simp at *; expose_names); exact (fun i h ↦ lt_of_eq_of_lt (h_getElem_eq_getElem! i h) (h_unfold_valid1 i h)); done
    have h_mem_based : ∀ a, a ∈ ret1 → a < 10 := by (try simp at *; expose_names); exact (uniqueness_7_2 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_index_to_mem h_index_based h_unfold_valid1 h_getElem_eq_getElem!); done
    exact h_mem_based

theorem uniqueness_8
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    : ∀ l ∈ ret2, l < 10 := by
  intro a ha
  -- Get the index where a appears in ret2
  rw [List.mem_iff_getElem] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  -- From h_valid2, we know ret2[i]! < 10 for valid indices
  unfold validDigits at h_valid2
  have h_bound := h_valid2 i hi
  -- We need to show ret2[i]! = ret2[i] for valid index
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h_bound
  exact h_bound

theorem uniqueness_9
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_base : True)
    : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0 := by
    unfold noLeadingZeros at h_nlz1
    cases h_nlz1 with
    | inl h_zero =>
      left
      exact h_zero
    | inr h_nonempty =>
      right
      obtain ⟨h_ne, h_last⟩ := h_nonempty
      constructor
      · exact h_ne
      · -- Need to show ¬ret1.getLast?.getD 0 = 0
        -- We know ret1.getLast! ≠ 0 and ret1 ≠ []
        -- For non-empty list: getLast! l = (getLast? l).getD default
        have h_eq : ret1.getLast! = ret1.getLast?.getD 0 := by
          rw [List.getLast!_eq_getLast?_getD]
          rfl
        rw [← h_eq]
        exact h_last

theorem uniqueness_10
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0 := by
    unfold noLeadingZeros at h_nlz2
    cases h_nlz2 with
    | inl h_zero =>
      left
      exact h_zero
    | inr h_nonempty =>
      right
      obtain ⟨h_ne, h_last⟩ := h_nonempty
      constructor
      · exact h_ne
      · intro h_contra
        apply h_last
        have h_eq : ret2.getLast! = ret2.getLast?.getD 0 := by
          rw [List.getLast!_eq_getLast?_getD]
          rfl
        rw [h_eq]
        exact h_contra

theorem uniqueness_11
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0] := by
    cases h_cases1 with
    | inl h_zero =>
      right
      exact h_zero
    | inr h_nonzero =>
      left
      obtain ⟨h_ne, h_last_ne⟩ := h_nonzero
      apply Nat.digits_ofDigits
      · omega
      · exact h_lt1
      · intro hne
        have h_getLast_eq : ret1.getLast?.getD 0 = ret1.getLast hne := by
          rw [List.getLast?_eq_getLast hne]
          simp
        rw [h_getLast_eq] at h_last_ne
        exact h_last_ne

theorem uniqueness_12
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0] := by
    cases h_cases2 with
    | inl h_zero =>
      right
      exact h_zero
    | inr h_nonzero =>
      left
      obtain ⟨h_ne, h_last_ne⟩ := h_nonzero
      apply Nat.digits_ofDigits
      · omega
      · exact h_lt2
      · intro hne
        have h_getLast_eq : ret2.getLast? = some (ret2.getLast hne) := List.getLast?_eq_getLast hne
        simp only [h_getLast_eq, Option.getD_some] at h_last_ne
        exact h_last_ne

theorem uniqueness_13
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    : Nat.ofDigits 10 ret1 = 0 → ret1 = [0] := by
    intro h_zero
    cases h_cases1 with
    | inl h_eq => exact h_eq
    | inr h_neq =>
      obtain ⟨h_ne_nil, h_last_ne_zero⟩ := h_neq
      -- If ret1 is nonempty and has nonzero last element, ofDigits > 0
      -- This contradicts h_zero
      exfalso
      -- ret1 is nonempty, so we can get its last element
      have h_exists_last : ret1.getLast?.isSome := by
        cases ret1 with
        | nil => exact absurd rfl h_ne_nil
        | cons hd tl => simp [List.getLast?]
      have h_last_some : ∃ x, ret1.getLast? = some x := Option.isSome_iff_exists.mp h_exists_last
      obtain ⟨last_val, h_last_eq⟩ := h_last_some
      have h_last_ne : last_val ≠ 0 := by
        simp [h_last_eq] at h_last_ne_zero
        exact h_last_ne_zero
      -- Use the canonical form: if ofDigits is 0, digits should be []
      have h_digits_zero : Nat.digits 10 0 = [] := by native_decide
      rw [h_zero] at h_canonical1
      cases h_canonical1 with
      | inl h_dig =>
        rw [h_digits_zero] at h_dig
        exact h_ne_nil h_dig.symm
      | inr h_ret1_zero =>
        -- ret1 = [0] contradicts h_last_ne_zero
        simp [h_ret1_zero] at h_last_ne_zero

theorem uniqueness_14
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    : Nat.ofDigits 10 ret2 = 0 → ret2 = [0] := by
  intro h_zero
  cases h_cases2 with
  | inl h_eq => exact h_eq
  | inr h_ne =>
    obtain ⟨h_ne_nil, h_last_ne_zero⟩ := h_ne
    cases h_canonical2 with
    | inl h_dig =>
      rw [h_zero] at h_dig
      simp only [Nat.digits_zero] at h_dig
      exact absurd h_dig.symm h_ne_nil
    | inr h_eq =>
      rw [h_eq] at h_last_ne_zero
      simp only [List.getLast?_singleton, Option.getD_some, ne_eq, not_true_eq_false] at h_last_ne_zero

theorem uniqueness_15
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_is_zero : Nat.ofDigits 10 ret1 = 0)
    (hret1_zero : ret1 = [0])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    : ret2 = [0] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_16
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    (h_pos : 0 < Nat.ofDigits 10 ret1)
    : ¬ret1 = [] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_17
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_ne1 : ¬ret1 = [])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    (h_pos : 0 < Nat.ofDigits 10 ret1)
    : ¬ret2 = [] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_18
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_ne1 : ¬ret1 = [])
    (h_ne2 : ¬ret2 = [])
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    (h_pos : 0 < Nat.ofDigits 10 ret1)
    : ∀ (h : ¬ret1 = []), ¬ret1.getLast h = 0 := by
  intro h
  -- First, eliminate the case ret1 = [0] using h_pos
  cases h_cases1 with
  | inl h_zero =>
    -- If ret1 = [0], then Nat.ofDigits 10 ret1 = 0, contradicting h_pos
    simp only [h_zero] at h_pos
    simp at h_pos
  | inr h_nonzero =>
    -- We have ret1 ≠ [] and ret1.getLast?.getD 0 ≠ 0
    obtain ⟨_, h_last_ne⟩ := h_nonzero
    -- For non-empty list, getLast? = some (getLast h)
    have h_getLast_eq : ret1.getLast? = some (ret1.getLast h) := List.getLast?_eq_getLast h
    -- So getLast?.getD 0 = getLast h
    rw [h_getLast_eq] at h_last_ne
    simp only [Option.getD_some] at h_last_ne
    exact h_last_ne

theorem uniqueness_19
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_ne1 : ¬ret1 = [])
    (h_ne2 : ¬ret2 = [])
    (h_last1 : ∀ (h : ¬ret1 = []), ¬ret1.getLast h = 0)
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    (h_pos : 0 < Nat.ofDigits 10 ret1)
    : ∀ (h : ¬ret2 = []), ¬ret2.getLast h = 0 := by
  intro h
  cases h_cases2 with
  | inl h_zero =>
    -- ret2 = [0] case leads to contradiction
    rw [h_zero] at h_eq_val
    simp only [Nat.ofDigits] at h_eq_val
    omega
  | inr h_nonzero =>
    -- ret2 ≠ [] and ret2.getLast?.getD 0 ≠ 0
    obtain ⟨_, h_last_ne⟩ := h_nonzero
    -- For non-empty list, getLast? = some (getLast h)
    have h_getLast_eq : ret2.getLast? = some (ret2.getLast h) := List.getLast?_eq_getLast h
    rw [h_getLast_eq] at h_last_ne
    simp only [Option.getD_some] at h_last_ne
    exact h_last_ne

theorem uniqueness_20
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_ne1 : ¬ret1 = [])
    (h_ne2 : ¬ret2 = [])
    (h_last1 : ∀ (h : ¬ret1 = []), ¬ret1.getLast h = 0)
    (h_last2 : ∀ (h : ¬ret2 = []), ¬ret2.getLast h = 0)
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    (h_pos : 0 < Nat.ofDigits 10 ret1)
    : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_21
    (l1 : List ℕ)
    (l2 : List ℕ)
    (hpre : precondition l1 l2)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition l1 l2 ret1)
    (hpost2 : postcondition l1 l2 ret2)
    (h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2)
    (h_valid1 : validDigits ret1)
    (h_valid2 : validDigits ret2)
    (h_nlz1 : noLeadingZeros ret1)
    (h_nlz2 : noLeadingZeros ret2)
    (h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2)
    (h_lt1 : ∀ l ∈ ret1, l < 10)
    (h_lt2 : ∀ l ∈ ret2, l < 10)
    (h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0])
    (h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0])
    (h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0])
    (h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0])
    (h_ne1 : ¬ret1 = [])
    (h_ne2 : ¬ret2 = [])
    (h_last1 : ∀ (h : ¬ret1 = []), ¬ret1.getLast h = 0)
    (h_last2 : ∀ (h : ¬ret2 = []), ¬ret2.getLast h = 0)
    (h_dig1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1)
    (h_base : True)
    (h_cases1 : ret1 = [0] ∨ ¬ret1 = [] ∧ ¬ret1.getLast?.getD 0 = 0)
    (h_cases2 : ret2 = [0] ∨ ¬ret2 = [] ∧ ¬ret2.getLast?.getD 0 = 0)
    (h_pos : 0 < Nat.ofDigits 10 ret1)
    : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (l1 : List Nat) (l2 : List Nat):
  precondition l1 l2 →
  (∀ ret1 ret2,
    postcondition l1 l2 ret1 →
    postcondition l1 l2 ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the key facts from postconditions
  have h_val1 : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 := by
    (try simp at *; expose_names); exact (uniqueness_0 l1 l2 hpre ret1 ret2 hpost1 hpost2); done
  have h_val2 : Nat.ofDigits 10 ret2 = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 := by
    (try simp at *; expose_names); exact (uniqueness_1 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1); done
  have h_valid1 : validDigits ret1 := by
    (try simp at *; expose_names); exact (uniqueness_2 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2); done
  have h_valid2 : validDigits ret2 := by
    (try simp at *; expose_names); exact (uniqueness_3 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1); done
  have h_nlz1 : noLeadingZeros ret1 := by
    (try simp at *; expose_names); exact (uniqueness_4 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2); done
  have h_nlz2 : noLeadingZeros ret2 := by
    (try simp at *; expose_names); exact (uniqueness_5 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1); done
  -- Both have the same ofDigits value
  have h_eq_val : Nat.ofDigits 10 ret1 = Nat.ofDigits 10 ret2 := by
    (try simp at *; expose_names); exact (uniqueness_6 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2); done
  -- Convert validDigits to the form needed for Nat.digits_ofDigits
  have h_lt1 : ∀ l ∈ ret1, l < 10 := by
    (try simp at *; expose_names); exact (uniqueness_7 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val); done
  have h_lt2 : ∀ l ∈ ret2, l < 10 := by
    (try simp at *; expose_names); exact (uniqueness_8 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1); done
  -- Base 10 > 1
  have h_base : 1 < 10 := by
    (try simp at *; expose_names); exact Nat.one_lt_succ_succ 8; done
  -- Handle the case when result is [0] vs non-empty with nonzero last
  have h_cases1 : ret1 = [0] ∨ (ret1 ≠ [] ∧ ret1.getLast! ≠ 0) := by
    (try simp at *; expose_names); exact (uniqueness_9 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_base); done
  have h_cases2 : ret2 = [0] ∨ (ret2 ≠ [] ∧ ret2.getLast! ≠ 0) := by
    (try simp at *; expose_names); exact (uniqueness_10 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_base h_cases1); done
  -- Use Nat.digits_ofDigits to show both equal the canonical representation
  have h_canonical1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 ∨ ret1 = [0] := by
    (try simp at *; expose_names); exact (uniqueness_11 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_base h_cases1 h_cases2); done
  have h_canonical2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 ∨ ret2 = [0] := by
    (try simp at *; expose_names); exact (uniqueness_12 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_base h_cases1 h_cases2); done
  -- If ofDigits 10 ret = 0 and noLeadingZeros, then ret = [0]
  have h_zero_case : Nat.ofDigits 10 ret1 = 0 → ret1 = [0] := by
    (try simp at *; expose_names); exact (uniqueness_13 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_base h_cases1 h_cases2); done
  have h_zero_case2 : Nat.ofDigits 10 ret2 = 0 → ret2 = [0] := by
    (try simp at *; expose_names); exact (uniqueness_14 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_base h_cases1 h_cases2); done
  -- For the main proof, we case split on whether the sum is zero
  cases Nat.eq_zero_or_pos (Nat.ofDigits 10 ret1) with
  | inl h_is_zero =>
    have hret1_zero : ret1 = [0] := by
      (try simp at *; expose_names); exact h_zero_case h_is_zero; done
    have hret2_zero : ret2 = [0] := by
      (try simp at *; expose_names); exact (uniqueness_15 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_is_zero hret1_zero h_base h_cases1 h_cases2); done
    calc ret1 = [0] := hret1_zero
      _ = ret2 := hret2_zero.symm
  | inr h_pos =>
    -- When positive, both must have nonzero last element and equal canonical digits
    have h_ne1 : ret1 ≠ [] := by
      (try simp at *; expose_names); exact (uniqueness_16 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_base h_cases1 h_cases2 h_pos); done
    have h_ne2 : ret2 ≠ [] := by
      (try simp at *; expose_names); exact (uniqueness_17 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_ne1 h_base h_cases1 h_cases2 h_pos); done
    have h_last1 : ∀ (h : ret1 ≠ []), ret1.getLast h ≠ 0 := by
      (try simp at *; expose_names); exact (uniqueness_18 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_ne1 h_ne2 h_base h_cases1 h_cases2 h_pos); done
    have h_last2 : ∀ (h : ret2 ≠ []), ret2.getLast h ≠ 0 := by
      (try simp at *; expose_names); exact (uniqueness_19 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_ne1 h_ne2 h_last1 h_base h_cases1 h_cases2 h_pos); done
    have h_dig1 : Nat.digits 10 (Nat.ofDigits 10 ret1) = ret1 := by
      (try simp at *; expose_names); exact (uniqueness_20 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_ne1 h_ne2 h_last1 h_last2 h_base h_cases1 h_cases2 h_pos); done
    have h_dig2 : Nat.digits 10 (Nat.ofDigits 10 ret2) = ret2 := by
      (try simp at *; expose_names); exact (uniqueness_21 l1 l2 hpre ret1 ret2 hpost1 hpost2 h_val1 h_val2 h_valid1 h_valid2 h_nlz1 h_nlz2 h_eq_val h_lt1 h_lt2 h_canonical1 h_canonical2 h_zero_case h_zero_case2 h_ne1 h_ne2 h_last1 h_last2 h_dig1 h_base h_cases1 h_cases2 h_pos); done
    calc ret1 = Nat.digits 10 (Nat.ofDigits 10 ret1) := h_dig1.symm
      _ = Nat.digits 10 (Nat.ofDigits 10 ret2) := by rw [h_eq_val]
      _ = ret2 := h_dig2
end Proof
