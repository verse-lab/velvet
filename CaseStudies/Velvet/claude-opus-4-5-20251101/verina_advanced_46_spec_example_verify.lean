import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def subarraySum (numbers : List Int) (i : Nat) (j : Nat) : Int :=
  ((numbers.drop i).take (j - i)).foldl (· + ·) 0



def isAchievableSubarraySum (numbers : List Int) (val : Int) : Prop :=
  ∃ i j, i ≤ j ∧ j ≤ numbers.length ∧ subarraySum numbers i j = val


def isMaximalSubarraySum (numbers : List Int) (val : Int) : Prop :=
  ∀ i j, i ≤ j → j ≤ numbers.length → subarraySum numbers i j ≤ val



def precondition (numbers : List Int) : Prop :=
  True



def postcondition (numbers : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  isAchievableSubarraySum numbers result ∧
  isMaximalSubarraySum numbers result


def test1_numbers : List Int := [1, 2, 3, -2, 5]

def test1_Expected : Int := 9

def test2_numbers : List Int := [-2, -3, 4, -1, -2, 1, 5, -3]

def test2_Expected : Int := 7

def test3_numbers : List Int := [-1, -2, -3, -4]

def test3_Expected : Int := 0







section Proof
theorem test1_precondition :
  precondition test1_numbers := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_numbers test1_Expected := by
  unfold postcondition test1_numbers test1_Expected isAchievableSubarraySum isMaximalSubarraySum subarraySum
  refine ⟨by omega, ⟨0, 5, by omega, by native_decide, by native_decide⟩, ?_⟩
  intro i j hij hjlen
  have hi5 : i ≤ 5 := Nat.le_trans hij hjlen
  have hj5 : j ≤ 5 := hjlen
  interval_cases i <;> interval_cases j <;> 
    first | omega | native_decide

theorem test2_precondition :
  precondition test2_numbers := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_numbers test2_Expected := by
  unfold postcondition isAchievableSubarraySum isMaximalSubarraySum subarraySum 
         test2_numbers test2_Expected
  constructor
  · omega
  constructor
  · exact ⟨2, 7, by omega, by native_decide, by native_decide⟩
  · intro i j hij hjn
    simp only [List.length] at hjn
    have hi : i ≤ 8 := Nat.le_trans hij hjn
    interval_cases i <;> interval_cases j <;> first | omega | native_decide

theorem test3_precondition :
  precondition test3_numbers := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition_0
    (h_expected : test3_Expected = 0)
    (h_numbers : test3_numbers = [-1, -2, -3, -4])
    (h_len : test3_numbers.length = 4)
    (h_empty_sum : subarraySum test3_numbers 0 0 = 0)
    (h_unfold : postcondition test3_numbers test3_Expected ↔ 0 ≤ test3_Expected ∧ isAchievableSubarraySum test3_numbers test3_Expected ∧ isMaximalSubarraySum test3_numbers test3_Expected)
    (h_nonneg : 0 ≤ test3_Expected)
    : isAchievableSubarraySum test3_numbers test3_Expected := by
    unfold isAchievableSubarraySum
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · exact Nat.le_refl 0
    · rw [h_len]
      exact Nat.zero_le 4
    · rw [h_expected]
      exact h_empty_sum

theorem test3_postcondition_1
    (h_expected : test3_Expected = 0)
    (h_numbers : test3_numbers = [-1, -2, -3, -4])
    (h_len : test3_numbers.length = 4)
    (h_empty_sum : subarraySum test3_numbers 0 0 = 0)
    (h_achievable : isAchievableSubarraySum test3_numbers test3_Expected)
    (h_unfold : postcondition test3_numbers test3_Expected ↔ 0 ≤ test3_Expected ∧ isAchievableSubarraySum test3_numbers test3_Expected ∧ isMaximalSubarraySum test3_numbers test3_Expected)
    (h_nonneg : 0 ≤ test3_Expected)
    : isMaximalSubarraySum test3_numbers test3_Expected := by
    unfold isMaximalSubarraySum
    intro i j hij hjlen
    rw [h_expected]
    rw [h_len] at hjlen
    have hi4 : i ≤ 4 := Nat.le_trans hij hjlen
    -- Now we case split on the bounded values
    interval_cases i <;> interval_cases j <;> 
      first
        | omega  -- handles cases where i > j (contradicts hij)
        | native_decide  -- handles valid cases by computation

theorem test3_postcondition :
  postcondition test3_numbers test3_Expected := by
  -- First unfold all the definitions
  have h_unfold : postcondition test3_numbers test3_Expected ↔ 
    test3_Expected ≥ 0 ∧ 
    isAchievableSubarraySum test3_numbers test3_Expected ∧ 
    isMaximalSubarraySum test3_numbers test3_Expected := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Establish the concrete values
  have h_expected : test3_Expected = 0 := by (try simp at *; expose_names); exact rfl; done
  have h_numbers : test3_numbers = [-1, -2, -3, -4] := by (try simp at *; expose_names); exact (rfl); done
  have h_len : test3_numbers.length = 4 := by (try simp at *; expose_names); exact rfl; done
  -- Part 1: result ≥ 0
  have h_nonneg : test3_Expected ≥ 0 := by (try simp at *; expose_names); exact (Int.zero_le_ofNat 0); done
  -- Part 2: achievability - empty subarray at i=0, j=0 gives sum 0
  have h_empty_sum : subarraySum test3_numbers 0 0 = 0 := by (try simp at *; expose_names); exact (h_expected); done
  have h_achievable : isAchievableSubarraySum test3_numbers test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_0 h_expected h_numbers h_len h_empty_sum h_unfold h_nonneg); done
  -- Part 3: maximality - all subarray sums are ≤ 0
  -- Since all elements are negative, any non-empty subarray has negative sum
  -- Empty subarrays have sum 0
  have h_maximal : isMaximalSubarraySum test3_numbers test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_1 h_expected h_numbers h_len h_empty_sum h_achievable h_unfold h_nonneg); done
  -- Combine all three parts
  unfold postcondition test3_numbers test3_Expected isAchievableSubarraySum isMaximalSubarraySum subarraySum
  refine ⟨by omega, ⟨0, 0, by omega, by native_decide, by native_decide⟩, ?_⟩
  intro i j hij hjlen
  simp only [List.length] at hjlen
  have hi4 : i ≤ 4 := Nat.le_trans hij hjlen
  interval_cases i <;> interval_cases j <;> first | omega | native_decide

theorem uniqueness (numbers : List Int):
  precondition numbers →
  (∀ ret1 ret2,
    postcondition numbers ret1 →
    postcondition numbers ret2 →
    ret1 = ret2) := by
  intro _h_pre
  intro ret1 ret2 h1 h2
  -- Destruct the postconditions
  obtain ⟨h1_nonneg, h1_achievable, h1_maximal⟩ := h1
  obtain ⟨h2_nonneg, h2_achievable, h2_maximal⟩ := h2
  -- Get witnesses from achievability
  obtain ⟨i1, j1, h1_i_le_j, h1_j_le_len, h1_sum⟩ := h1_achievable
  obtain ⟨i2, j2, h2_i_le_j, h2_j_le_len, h2_sum⟩ := h2_achievable
  -- Show ret1 ≤ ret2 using h2_maximal applied to i1, j1
  have h_ret1_le_ret2 : ret1 ≤ ret2 := by
    have := h2_maximal i1 j1 h1_i_le_j h1_j_le_len
    rw [h1_sum] at this
    exact this
  -- Show ret2 ≤ ret1 using h1_maximal applied to i2, j2
  have h_ret2_le_ret1 : ret2 ≤ ret1 := by
    have := h1_maximal i2 j2 h2_i_le_j h2_j_le_len
    rw [h2_sum] at this
    exact this
  -- By antisymmetry
  exact Int.le_antisymm h_ret1_le_ret2 h_ret2_le_ret1
end Proof
