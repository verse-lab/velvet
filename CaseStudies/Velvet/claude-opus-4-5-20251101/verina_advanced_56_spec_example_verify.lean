import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def nonZeroElements (xs : List Int) : List Int :=
  xs.filter (· ≠ 0)




def ensures1 (xs : List Int) (result : List Int) :=
  ∀ x : Int, result.count x = xs.count x



def ensures2 (xs : List Int) (result : List Int) :=
  ∀ i j : Nat, i < j → j < result.length → result[i]! = 0 → result[j]! = 0



def ensures3 (xs : List Int) (result : List Int) :=
  nonZeroElements result = nonZeroElements xs

def precondition (xs : List Int) :=
  True

def postcondition (xs : List Int) (result : List Int) :=
  ensures1 xs result ∧ ensures2 xs result ∧ ensures3 xs result


def test1_xs : List Int := [0, 1, 0, 3, 12]

def test1_Expected : List Int := [1, 3, 12, 0, 0]

def test3_xs : List Int := [1, 2, 3]

def test3_Expected : List Int := [1, 2, 3]

def test6_xs : List Int := [4, 0, 5, 0, 6]

def test6_Expected : List Int := [4, 5, 6, 0, 0]







section Proof
theorem test1_precondition :
  precondition test1_xs := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_xs test1_Expected := by
  simp only [postcondition, ensures1, ensures2, ensures3, nonZeroElements, test1_xs, test1_Expected]
  refine ⟨?_, ?_, rfl⟩
  · intro x
    simp only [List.count_cons, List.count_nil]
    omega
  · intro i j hij hjlen hi0
    simp only [List.length] at hjlen
    interval_cases j <;> interval_cases i <;> simp_all

theorem test3_precondition :
  precondition test3_xs := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_xs test3_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test3_xs test3_Expected nonZeroElements
  refine ⟨?_, ?_, ?_⟩
  · -- ensures1: counts are equal
    intro x
    rfl
  · -- ensures2: zeros at the end (vacuously true - no zeros)
    intro i j hij hjlen hi0
    simp only [List.length_cons, List.length_nil] at hjlen
    -- j < 3, so j ∈ {0, 1, 2}
    -- We need to show result[j]! = 0, but first check that result[i]! = 0 is false
    interval_cases j
    · -- j = 0: impossible since i < j = 0
      omega
    · -- j = 1: i = 0, check [1,2,3][0]! = 1 ≠ 0
      interval_cases i
      · simp at hi0
    · -- j = 2: i ∈ {0, 1}
      interval_cases i
      · simp at hi0
      · simp at hi0
  · -- ensures3: nonZeroElements are equal
    rfl

theorem test6_precondition :
  precondition test6_xs := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition_0
    (h_unfold : postcondition test6_xs test6_Expected ↔ ensures1 test6_xs test6_Expected ∧ ensures2 test6_xs test6_Expected ∧ ensures3 test6_xs test6_Expected)
    (h_xs : test6_xs = [4, 0, 5, 0, 6])
    (h_expected : test6_Expected = [4, 5, 6, 0, 0])
    (h_expected_len : test6_Expected.length = 5)
    : ensures1 test6_xs test6_Expected := by
    unfold ensures1
    intro x
    simp only [h_xs, h_expected]
    simp only [List.count_cons, List.count_nil]
    omega

theorem test6_postcondition_1
    (h_unfold : postcondition test6_xs test6_Expected ↔ ensures1 test6_xs test6_Expected ∧ ensures2 test6_xs test6_Expected ∧ ensures3 test6_xs test6_Expected)
    (h_xs : test6_xs = [4, 0, 5, 0, 6])
    (h_expected : test6_Expected = [4, 5, 6, 0, 0])
    (h_expected_len : test6_Expected.length = 5)
    (h_ensures1 : ensures1 test6_xs test6_Expected)
    : ensures2 test6_xs test6_Expected := by
    unfold ensures2
    intros i j hij hjlen hi0
    simp only [h_expected] at hjlen hi0 ⊢
    simp only [List.length_cons, List.length_nil] at hjlen
    -- hjlen : j < 5
    -- We need to check all cases where i < j < 5 and [4, 5, 6, 0, 0][i]! = 0
    -- The list is [4, 5, 6, 0, 0], so only indices 3 and 4 have value 0
    -- If i = 3, then j = 4, and [4, 5, 6, 0, 0][4]! = 0 ✓
    -- If i < 3, then [4, 5, 6, 0, 0][i]! ≠ 0, contradiction
    interval_cases j
    · omega  -- j = 0, but i < j means i < 0, impossible
    · interval_cases i
      · simp only [List.getElem!_cons_zero] at hi0
        omega  -- 4 ≠ 0
    · interval_cases i
      · simp only [List.getElem!_cons_zero] at hi0
        omega
      · simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hi0
        omega
    · interval_cases i
      · simp only [List.getElem!_cons_zero] at hi0
        omega
      · simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hi0
        omega
      · simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hi0
        omega
    · interval_cases i
      · simp only [List.getElem!_cons_zero] at hi0
        omega
      · simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hi0
        omega
      · simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hi0
        omega
      · native_decide

theorem test6_postcondition :
  postcondition test6_xs test6_Expected := by
  -- First unfold all definitions to expose the concrete lists
  have h_unfold : postcondition test6_xs test6_Expected ↔ 
    (ensures1 test6_xs test6_Expected ∧ ensures2 test6_xs test6_Expected ∧ ensures3 test6_xs test6_Expected) := by
    (try simp at *; expose_names); exact Eq.to_iff rfl; done
  -- The concrete values
  have h_xs : test6_xs = [4, 0, 5, 0, 6] := by (try simp at *; expose_names); exact rfl; done
  have h_expected : test6_Expected = [4, 5, 6, 0, 0] := by (try simp at *; expose_names); exact (rfl); done
  have h_expected_len : test6_Expected.length = 5 := by (try simp at *; expose_names); exact rfl; done
  -- ensures1: For all x, count x in result = count x in xs
  have h_ensures1 : ensures1 test6_xs test6_Expected := by
    (try simp at *; expose_names); exact (test6_postcondition_0 h_unfold h_xs h_expected h_expected_len); done
  -- ensures2: zeros are at the end - if result[i]! = 0 and i < j < length, then result[j]! = 0
  -- For test6_Expected = [4, 5, 6, 0, 0], zeros are at indices 3 and 4
  have h_ensures2 : ensures2 test6_xs test6_Expected := by
    (try simp at *; expose_names); exact (test6_postcondition_1 h_unfold h_xs h_expected h_expected_len h_ensures1); done
  -- ensures3: nonZeroElements are equal
  -- nonZeroElements [4, 0, 5, 0, 6] = [4, 5, 6]
  -- nonZeroElements [4, 5, 6, 0, 0] = [4, 5, 6]
  have h_nonzero_xs : nonZeroElements test6_xs = [4, 5, 6] := by (try simp at *; expose_names); exact (rfl); done
  have h_nonzero_expected : nonZeroElements test6_Expected = [4, 5, 6] := by (try simp at *; expose_names); exact (h_nonzero_xs); done
  have h_ensures3 : ensures3 test6_xs test6_Expected := by
    (try simp at *; expose_names); exact h_nonzero_xs; done
  -- Combine all three ensures properties
  exact ⟨h_ensures1, h_ensures2, h_ensures3⟩

theorem uniqueness (xs : List Int):
  precondition xs →
  (∀ ret1 ret2,
    postcondition xs ret1 →
    postcondition xs ret2 →
    ret1 = ret2) := by
  intro _ ret1 ret2 ⟨hc1, hz1, hn1⟩ ⟨hc2, hz2, hn2⟩
  unfold ensures1 ensures2 ensures3 nonZeroElements at *
  have hfilter : ret1.filter (· ≠ 0) = ret2.filter (· ≠ 0) := hn1.trans hn2.symm
  have hcount : ∀ x, ret1.count x = ret2.count x := fun x => (hc1 x).trans (hc2 x).symm
  sorry
end Proof
