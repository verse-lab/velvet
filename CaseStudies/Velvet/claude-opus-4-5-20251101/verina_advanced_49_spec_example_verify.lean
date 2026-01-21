import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedAsc (lst : List Int) : Prop :=
  List.Sorted (· ≤ ·) lst

def countOccurrences (x : Int) (lst : List Int) : Nat :=
  lst.filter (· == x) |>.length



def precondition (arr1 : List Int) (arr2 : List Int) : Prop :=
  isSortedAsc arr1 ∧ isSortedAsc arr2



def ensures1 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  isSortedAsc result


def ensures2 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  result.length = arr1.length + arr2.length


def ensures3 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ result → x ∈ arr1 ∨ x ∈ arr2


def ensures4 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ∀ x, countOccurrences x result = countOccurrences x arr1 + countOccurrences x arr2

def postcondition (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ensures1 arr1 arr2 result ∧
  ensures2 arr1 arr2 result ∧
  ensures3 arr1 arr2 result ∧
  ensures4 arr1 arr2 result


def test1_arr1 : List Int := [1, 3, 5]

def test1_arr2 : List Int := [2, 4, 6]

def test1_Expected : List Int := [1, 2, 3, 4, 5, 6]

def test3_arr1 : List Int := [-2, 0, 1]

def test3_arr2 : List Int := [-3, -1]

def test3_Expected : List Int := [-3, -2, -1, 0, 1]

def test5_arr1 : List Int := [1, 2, 2]

def test5_arr2 : List Int := [2, 3, 3]

def test5_Expected : List Int := [1, 2, 2, 2, 3, 3]







section Proof
theorem test1_precondition :
  precondition test1_arr1 test1_arr2 := by
  unfold precondition isSortedAsc test1_arr1 test1_arr2
  constructor
  · -- Prove List.Sorted (· ≤ ·) [1, 3, 5]
    simp only [List.Sorted]
    apply List.Pairwise.cons
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · decide
      · decide
    · apply List.Pairwise.cons
      · intro a ha
        simp at ha
        subst ha
        decide
      · apply List.Pairwise.cons
        · intro a ha
          simp at ha
        · exact List.Pairwise.nil
  · -- Prove List.Sorted (· ≤ ·) [2, 4, 6]
    simp only [List.Sorted]
    apply List.Pairwise.cons
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · decide
      · decide
    · apply List.Pairwise.cons
      · intro a ha
        simp at ha
        subst ha
        decide
      · apply List.Pairwise.cons
        · intro a ha
          simp at ha
        · exact List.Pairwise.nil

theorem test1_postcondition_0
    (h_unfold : postcondition test1_arr1 test1_arr2 test1_Expected ↔ ensures1 test1_arr1 test1_arr2 test1_Expected ∧ ensures2 test1_arr1 test1_arr2 test1_Expected ∧ ensures3 test1_arr1 test1_arr2 test1_Expected ∧ ensures4 test1_arr1 test1_arr2 test1_Expected)
    : ensures1 test1_arr1 test1_arr2 test1_Expected := by
    unfold ensures1 isSortedAsc test1_Expected
    native_decide

theorem test1_postcondition_1
    (h_ensures1 : ensures1 test1_arr1 test1_arr2 test1_Expected)
    (h_ensures2 : ensures2 test1_arr1 test1_arr2 test1_Expected)
    (h_unfold : postcondition test1_arr1 test1_arr2 test1_Expected ↔ ensures1 test1_arr1 test1_arr2 test1_Expected ∧ ensures2 test1_arr1 test1_arr2 test1_Expected ∧ ensures3 test1_arr1 test1_arr2 test1_Expected ∧ ensures4 test1_arr1 test1_arr2 test1_Expected)
    : ensures3 test1_arr1 test1_arr2 test1_Expected := by
    unfold ensures3 test1_arr1 test1_arr2 test1_Expected
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · left; left; rfl
    · right; left; rfl
    · left; right; left; rfl
    · right; right; left; rfl
    · left; right; right; rfl
    · right; right; right; rfl

theorem test1_postcondition_2
    (h_ensures1 : ensures1 test1_arr1 test1_arr2 test1_Expected)
    (h_ensures2 : ensures2 test1_arr1 test1_arr2 test1_Expected)
    (h_ensures3 : ensures3 test1_arr1 test1_arr2 test1_Expected)
    (h_unfold : postcondition test1_arr1 test1_arr2 test1_Expected ↔ ensures1 test1_arr1 test1_arr2 test1_Expected ∧ ensures2 test1_arr1 test1_arr2 test1_Expected ∧ ensures3 test1_arr1 test1_arr2 test1_Expected ∧ ensures4 test1_arr1 test1_arr2 test1_Expected)
    : ensures4 test1_arr1 test1_arr2 test1_Expected := by
    unfold ensures4 countOccurrences test1_arr1 test1_arr2 test1_Expected
    intro x
    simp only [List.filter, decide_eq_true_eq]
    cases h1 : (1 : Int) == x <;> cases h2 : (2 : Int) == x <;> cases h3 : (3 : Int) == x <;> 
    cases h4 : (4 : Int) == x <;> cases h5 : (5 : Int) == x <;> cases h6 : (6 : Int) == x <;>
    simp_all [beq_iff_eq, ne_eq]

theorem test1_postcondition :
  postcondition test1_arr1 test1_arr2 test1_Expected := by
  -- First unfold all definitions to expose the concrete structure
  have h_unfold : postcondition test1_arr1 test1_arr2 test1_Expected = 
    (ensures1 test1_arr1 test1_arr2 test1_Expected ∧
     ensures2 test1_arr1 test1_arr2 test1_Expected ∧
     ensures3 test1_arr1 test1_arr2 test1_Expected ∧
     ensures4 test1_arr1 test1_arr2 test1_Expected) := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Prove ensures1: the result [1, 2, 3, 4, 5, 6] is sorted ascending
  have h_ensures1 : ensures1 test1_arr1 test1_arr2 test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_0 h_unfold); done
  -- Prove ensures2: length of result equals sum of input lengths (6 = 3 + 3)
  have h_ensures2 : ensures2 test1_arr1 test1_arr2 test1_Expected := by (try simp at *; expose_names); exact (rfl); done
  -- Prove ensures3: every element in result is from arr1 or arr2
  have h_ensures3 : ensures3 test1_arr1 test1_arr2 test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_1 h_ensures1 h_ensures2 h_unfold); done
  -- Prove ensures4: count of each element in result equals sum of counts in inputs
  have h_ensures4 : ensures4 test1_arr1 test1_arr2 test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_2 h_ensures1 h_ensures2 h_ensures3 h_unfold); done
  -- Combine all four ensures conditions into the postcondition
  unfold postcondition
  exact ⟨h_ensures1, h_ensures2, h_ensures3, h_ensures4⟩

theorem test3_precondition :
  precondition test3_arr1 test3_arr2 := by
  unfold precondition isSortedAsc test3_arr1 test3_arr2
  constructor
  · -- Show [-2, 0, 1] is sorted
    apply List.Pairwise.cons
    · intro a' ha'
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · native_decide
      · native_decide
    · apply List.Pairwise.cons
      · intro a' ha'
        simp only [List.mem_singleton, List.not_mem_nil, or_false] at ha'
        subst ha'
        native_decide
      · apply List.Pairwise.cons
        · intro a' ha'
          simp only [List.not_mem_nil] at ha'
        · exact List.Pairwise.nil
  · -- Show [-3, -1] is sorted
    apply List.Pairwise.cons
    · intro a' ha'
      simp only [List.mem_singleton, List.not_mem_nil, or_false] at ha'
      subst ha'
      native_decide
    · apply List.Pairwise.cons
      · intro a' ha'
        simp only [List.not_mem_nil] at ha'
      · exact List.Pairwise.nil

theorem test3_postcondition_0
    (h_unfold : postcondition test3_arr1 test3_arr2 test3_Expected ↔ ensures1 test3_arr1 test3_arr2 test3_Expected ∧ ensures2 test3_arr1 test3_arr2 test3_Expected ∧ ensures3 test3_arr1 test3_arr2 test3_Expected ∧ ensures4 test3_arr1 test3_arr2 test3_Expected)
    : ensures1 test3_arr1 test3_arr2 test3_Expected := by
    unfold ensures1 isSortedAsc test3_Expected
    native_decide

theorem test3_postcondition_1
    (h_ensures1 : ensures1 test3_arr1 test3_arr2 test3_Expected)
    (h_ensures2 : ensures2 test3_arr1 test3_arr2 test3_Expected)
    (h_unfold : postcondition test3_arr1 test3_arr2 test3_Expected ↔ ensures1 test3_arr1 test3_arr2 test3_Expected ∧ ensures2 test3_arr1 test3_arr2 test3_Expected ∧ ensures3 test3_arr1 test3_arr2 test3_Expected ∧ ensures4 test3_arr1 test3_arr2 test3_Expected)
    : ensures3 test3_arr1 test3_arr2 test3_Expected := by
    unfold ensures3 test3_arr1 test3_arr2 test3_Expected
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · right; left; rfl
    · left; left; rfl
    · right; right; rfl
    · left; right; left; rfl
    · left; right; right; rfl

theorem test3_postcondition_2
    (h_ensures1 : ensures1 test3_arr1 test3_arr2 test3_Expected)
    (h_ensures2 : ensures2 test3_arr1 test3_arr2 test3_Expected)
    (h_ensures3 : ensures3 test3_arr1 test3_arr2 test3_Expected)
    (h_unfold : postcondition test3_arr1 test3_arr2 test3_Expected ↔ ensures1 test3_arr1 test3_arr2 test3_Expected ∧ ensures2 test3_arr1 test3_arr2 test3_Expected ∧ ensures3 test3_arr1 test3_arr2 test3_Expected ∧ ensures4 test3_arr1 test3_arr2 test3_Expected)
    : ensures4 test3_arr1 test3_arr2 test3_Expected := by
    unfold ensures4 countOccurrences test3_arr1 test3_arr2 test3_Expected
    intro x
    simp only [List.filter_cons, List.filter_nil, List.length_cons, List.length_nil]
    cases h3 : ((-3 : Int) == x) <;> cases h2 : ((-2 : Int) == x) <;> cases h1 : ((-1 : Int) == x) <;> cases h0 : ((0 : Int) == x) <;> cases h1' : ((1 : Int) == x) <;> simp_all [beq_iff_eq]

theorem test3_postcondition :
  postcondition test3_arr1 test3_arr2 test3_Expected := by
  -- Unfold the postcondition definition to expose its structure
  have h_unfold : postcondition test3_arr1 test3_arr2 test3_Expected = 
    (ensures1 test3_arr1 test3_arr2 test3_Expected ∧
     ensures2 test3_arr1 test3_arr2 test3_Expected ∧
     ensures3 test3_arr1 test3_arr2 test3_Expected ∧
     ensures4 test3_arr1 test3_arr2 test3_Expected) := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Prove ensures1: test3_Expected = [-3, -2, -1, 0, 1] is sorted ascending
  -- Check: -3 ≤ -2 ≤ -1 ≤ 0 ≤ 1
  have h_ensures1 : ensures1 test3_arr1 test3_arr2 test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_0 h_unfold); done
  -- Prove ensures2: length of result equals sum of input lengths
  -- length [-3, -2, -1, 0, 1] = 5 = 3 + 2 = length [-2, 0, 1] + length [-3, -1]
  have h_ensures2 : ensures2 test3_arr1 test3_arr2 test3_Expected := by (try simp at *; expose_names); exact (rfl); done
  -- Prove ensures3: every element in result is from arr1 or arr2
  -- -3 ∈ arr2, -2 ∈ arr1, -1 ∈ arr2, 0 ∈ arr1, 1 ∈ arr1
  have h_ensures3 : ensures3 test3_arr1 test3_arr2 test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_1 h_ensures1 h_ensures2 h_unfold); done
  -- Prove ensures4: count of each element in result equals sum of counts in inputs
  have h_ensures4 : ensures4 test3_arr1 test3_arr2 test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_2 h_ensures1 h_ensures2 h_ensures3 h_unfold); done
  -- Combine all four ensures conditions into the postcondition
  unfold postcondition
  exact ⟨h_ensures1, h_ensures2, h_ensures3, h_ensures4⟩

theorem test5_precondition : precondition test5_arr1 test5_arr2 := by
  unfold precondition isSortedAsc test5_arr1 test5_arr2
  constructor <;> native_decide

theorem test5_postcondition_0
    (h_unfold : postcondition test5_arr1 test5_arr2 test5_Expected ↔ ensures1 test5_arr1 test5_arr2 test5_Expected ∧ ensures2 test5_arr1 test5_arr2 test5_Expected ∧ ensures3 test5_arr1 test5_arr2 test5_Expected ∧ ensures4 test5_arr1 test5_arr2 test5_Expected)
    : ensures1 test5_arr1 test5_arr2 test5_Expected := by
    unfold ensures1 isSortedAsc test5_Expected
    native_decide

theorem test5_postcondition_1
    (h_ensures1 : ensures1 test5_arr1 test5_arr2 test5_Expected)
    (h_ensures2 : ensures2 test5_arr1 test5_arr2 test5_Expected)
    (h_unfold : postcondition test5_arr1 test5_arr2 test5_Expected ↔ ensures1 test5_arr1 test5_arr2 test5_Expected ∧ ensures2 test5_arr1 test5_arr2 test5_Expected ∧ ensures3 test5_arr1 test5_arr2 test5_Expected ∧ ensures4 test5_arr1 test5_arr2 test5_Expected)
    : ensures3 test5_arr1 test5_arr2 test5_Expected := by
    unfold ensures3 test5_arr1 test5_arr2 test5_Expected
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · left; left; rfl
    · left; right; left; rfl
    · left; right; left; rfl
    · left; right; left; rfl
    · right; right; left; rfl
    · right; right; left; rfl

theorem test5_postcondition_2
    (h_ensures1 : ensures1 test5_arr1 test5_arr2 test5_Expected)
    (h_ensures2 : ensures2 test5_arr1 test5_arr2 test5_Expected)
    (h_ensures3 : ensures3 test5_arr1 test5_arr2 test5_Expected)
    (h_unfold : postcondition test5_arr1 test5_arr2 test5_Expected ↔ ensures1 test5_arr1 test5_arr2 test5_Expected ∧ ensures2 test5_arr1 test5_arr2 test5_Expected ∧ ensures3 test5_arr1 test5_arr2 test5_Expected ∧ ensures4 test5_arr1 test5_arr2 test5_Expected)
    : ensures4 test5_arr1 test5_arr2 test5_Expected := by
    unfold ensures4 countOccurrences test5_arr1 test5_arr2 test5_Expected
    intro x
    simp only [List.filter_cons, List.filter_nil, List.length_cons, List.length_nil]
    cases h1 : ((1 : Int) == x) <;> cases h2 : ((2 : Int) == x) <;> cases h3 : ((3 : Int) == x) <;> simp_all [beq_iff_eq]

theorem test5_postcondition :
  postcondition test5_arr1 test5_arr2 test5_Expected := by
  -- First unfold the postcondition definition to expose its structure
  have h_unfold : postcondition test5_arr1 test5_arr2 test5_Expected = 
    (ensures1 test5_arr1 test5_arr2 test5_Expected ∧
     ensures2 test5_arr1 test5_arr2 test5_Expected ∧
     ensures3 test5_arr1 test5_arr2 test5_Expected ∧
     ensures4 test5_arr1 test5_arr2 test5_Expected) := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Prove ensures1: test5_Expected = [1, 2, 2, 2, 3, 3] is sorted ascending
  -- Check: 1 ≤ 2 ≤ 2 ≤ 2 ≤ 3 ≤ 3
  have h_ensures1 : ensures1 test5_arr1 test5_arr2 test5_Expected := by (try simp at *; expose_names); exact (test5_postcondition_0 h_unfold); done
  -- Prove ensures2: length of result equals sum of input lengths
  -- length [1, 2, 2, 2, 3, 3] = 6 = 3 + 3 = length [1, 2, 2] + length [2, 3, 3]
  have h_ensures2 : ensures2 test5_arr1 test5_arr2 test5_Expected := by (try simp at *; expose_names); exact (rfl); done
  -- Prove ensures3: every element in result is from arr1 or arr2
  -- 1 ∈ arr1, 2 ∈ arr1, 2 ∈ arr1, 2 ∈ arr2, 3 ∈ arr2, 3 ∈ arr2
  have h_ensures3 : ensures3 test5_arr1 test5_arr2 test5_Expected := by (try simp at *; expose_names); exact (test5_postcondition_1 h_ensures1 h_ensures2 h_unfold); done
  -- Prove ensures4: count of each element in result equals sum of counts from inputs
  -- For 1: 1 = 1 + 0, For 2: 3 = 2 + 1, For 3: 2 = 0 + 2, For others: 0 = 0 + 0
  have h_ensures4 : ensures4 test5_arr1 test5_arr2 test5_Expected := by (try simp at *; expose_names); exact (test5_postcondition_2 h_ensures1 h_ensures2 h_ensures3 h_unfold); done
  -- Combine all four ensures conditions into the postcondition
  unfold postcondition
  exact ⟨h_ensures1, h_ensures2, h_ensures3, h_ensures4⟩

theorem uniqueness_0
    (arr1 : List ℤ)
    (arr2 : List ℤ)
    (hpre : precondition arr1 arr2)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr1 arr2 ret1)
    (hpost2 : postcondition arr1 arr2 ret2)
    : isSortedAsc ret1 := by
    unfold postcondition at hpost1
    unfold ensures1 at hpost1
    exact hpost1.1

theorem uniqueness_1
    (arr1 : List ℤ)
    (arr2 : List ℤ)
    (hpre : precondition arr1 arr2)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr1 arr2 ret1)
    (hpost2 : postcondition arr1 arr2 ret2)
    (h_sorted1 : isSortedAsc ret1)
    : isSortedAsc ret2 := by
    intros; expose_names; exact (uniqueness_0 arr1 arr2 hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (arr1 : List ℤ)
    (arr2 : List ℤ)
    (hpre : precondition arr1 arr2)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr1 arr2 ret1)
    (hpost2 : postcondition arr1 arr2 ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    : ensures4 arr1 arr2 ret1 := by
    unfold postcondition at hpost1
    exact hpost1.2.2.2

theorem uniqueness_3
    (arr1 : List ℤ)
    (arr2 : List ℤ)
    (hpre : precondition arr1 arr2)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr1 arr2 ret1)
    (hpost2 : postcondition arr1 arr2 ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_ensures4_1 : ensures4 arr1 arr2 ret1)
    : ensures4 arr1 arr2 ret2 := by
    intros; expose_names; exact (uniqueness_2 arr1 arr2 hpre ret2 ret1 hpost2 hpost1 h_sorted2 h_sorted1); done

theorem uniqueness_4
    (arr1 : List ℤ)
    (arr2 : List ℤ)
    (hpre : precondition arr1 arr2)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr1 arr2 ret1)
    (hpost2 : postcondition arr1 arr2 ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_ensures4_1 : ensures4 arr1 arr2 ret1)
    (h_ensures4_2 : ensures4 arr1 arr2 ret2)
    : ∀ (x : ℤ), countOccurrences x ret1 = countOccurrences x ret2 := by
    intro x
    unfold ensures4 at h_ensures4_1 h_ensures4_2
    have h1 : countOccurrences x ret1 = countOccurrences x arr1 + countOccurrences x arr2 := h_ensures4_1 x
    have h2 : countOccurrences x ret2 = countOccurrences x arr1 + countOccurrences x arr2 := h_ensures4_2 x
    rw [h1, h2]

theorem uniqueness_5
    (arr1 : List ℤ)
    (arr2 : List ℤ)
    (hpre : precondition arr1 arr2)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr1 arr2 ret1)
    (hpost2 : postcondition arr1 arr2 ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_ensures4_1 : ensures4 arr1 arr2 ret1)
    (h_ensures4_2 : ensures4 arr1 arr2 ret2)
    (h_same_count : ∀ (x : ℤ), countOccurrences x ret1 = countOccurrences x ret2)
    : ∀ (x : ℤ), List.count x ret1 = List.count x ret2 := by
    intro x
    -- countOccurrences x lst = (lst.filter (· == x)).length by definition
    -- List.count x lst = List.countP (· == x) lst = (lst.filter (· == x)).length
    have count_eq_filter_len : ∀ (lst : List ℤ), List.count x lst = (lst.filter (· == x)).length := by
      intro lst
      rw [List.count_eq_countP]
      rw [List.countP_eq_length_filter]
    rw [count_eq_filter_len ret1, count_eq_filter_len ret2]
    -- Now we have (ret1.filter (· == x)).length = (ret2.filter (· == x)).length
    -- which follows from h_same_count since countOccurrences uses the same definition
    have := h_same_count x
    simp only [countOccurrences] at this
    exact this

theorem uniqueness (arr1 : List Int) (arr2 : List Int):
  precondition arr1 arr2 →
  (∀ ret1 ret2,
    postcondition arr1 arr2 ret1 →
    postcondition arr1 arr2 ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the ensures conditions from both postconditions
  have h_sorted1 : isSortedAsc ret1 := by (try simp at *; expose_names); exact (uniqueness_0 arr1 arr2 hpre ret1 ret2 hpost1 hpost2); done
  have h_sorted2 : isSortedAsc ret2 := by (try simp at *; expose_names); exact (uniqueness_1 arr1 arr2 hpre ret1 ret2 hpost1 hpost2 h_sorted1); done
  have h_ensures4_1 : ensures4 arr1 arr2 ret1 := by (try simp at *; expose_names); exact (uniqueness_2 arr1 arr2 hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2); done
  have h_ensures4_2 : ensures4 arr1 arr2 ret2 := by (try simp at *; expose_names); exact (uniqueness_3 arr1 arr2 hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_ensures4_1); done
  -- Show that ret1 and ret2 have the same count of every element
  have h_same_count : ∀ x, countOccurrences x ret1 = countOccurrences x ret2 := by (try simp at *; expose_names); exact (uniqueness_4 arr1 arr2 hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_ensures4_1 h_ensures4_2); done
  -- Convert countOccurrences to List.count for using library lemmas
  have h_count_eq : ∀ x, List.count x ret1 = List.count x ret2 := by (try simp at *; expose_names); exact (uniqueness_5 arr1 arr2 hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_ensures4_1 h_ensures4_2 h_same_count); done
  -- From equal counts, we get that ret1 and ret2 are permutations of each other
  have h_perm : ret1.Perm ret2 := by (try simp at *; expose_names); exact (List.perm_iff_count.mpr h_count_eq); done
  -- isSortedAsc means List.Sorted (· ≤ ·), which is List.Pairwise (· ≤ ·)
  have h_pairwise1 : List.Pairwise (· ≤ ·) ret1 := by (try simp at *; expose_names); exact (h_sorted1); done
  have h_pairwise2 : List.Pairwise (· ≤ ·) ret2 := by (try simp at *; expose_names); exact (h_sorted2); done
  -- For integers, antisymmetry: if a ≤ b and b ≤ a, then a = b
  have h_antisymm : ∀ (a b : Int), a ∈ ret1 → b ∈ ret2 → a ≤ b → b ≤ a → a = b := by (try simp at *; expose_names); exact (fun a b a_1 a_2 a_3 a_4 ↦ Int.le_antisymm a_3 a_4); done
  -- Apply the theorem that sorted permutations are equal using Perm.eq_of_sorted
  exact h_perm.eq_of_sorted h_antisymm h_pairwise1 h_pairwise2
end Proof
