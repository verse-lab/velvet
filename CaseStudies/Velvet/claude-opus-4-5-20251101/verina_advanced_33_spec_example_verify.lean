import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! < l[j]!


def isLongestIncreasingSubsequenceLength (nums : List Int) (len : Nat) : Prop :=

  (∃ subseq : List Int, subseq.Sublist nums ∧ isStrictlyIncreasing subseq ∧ subseq.length = len) ∧

  (∀ subseq : List Int, subseq.Sublist nums → isStrictlyIncreasing subseq → subseq.length ≤ len)

def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Nat) : Prop :=

  (nums = [] → result = 0) ∧

  (nums ≠ [] → isLongestIncreasingSubsequenceLength nums result)


def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]

def test1_Expected : Nat := 4

def test3_nums : List Int := [7, 7, 7, 7, 7]

def test3_Expected : Nat := 1

def test4_nums : List Int := []

def test4_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (h_nums : test1_nums = [10, 9, 2, 5, 3, 7, 101, 18])
    (h_expected : test1_Expected = 4)
    (h_nonempty : ¬test1_nums = [])
    (h_unfold : postcondition test1_nums test1_Expected ↔ (test1_nums = [] → test1_Expected = 0) ∧ (¬test1_nums = [] → isLongestIncreasingSubsequenceLength test1_nums test1_Expected))
    (h_empty_case : test1_nums = [] → test1_Expected = 0)
    (h_sublist : [2, 3, 7, 18].Sublist test1_nums)
    : isStrictlyIncreasing [2, 3, 7, 18] := by
    unfold isStrictlyIncreasing
    intro i j hij hjlen
    simp only [List.length] at hjlen
    interval_cases j
    · -- j = 0: impossible since i < j means i < 0
      omega
    · -- j = 1: i = 0
      interval_cases i
      · native_decide
    · -- j = 2: i ∈ {0, 1}
      interval_cases i
      · native_decide
      · native_decide
    · -- j = 3: i ∈ {0, 1, 2}
      interval_cases i
      · native_decide
      · native_decide
      · native_decide

theorem test1_postcondition_1
    (h_nums : test1_nums = [10, 9, 2, 5, 3, 7, 101, 18])
    (h_expected : test1_Expected = 4)
    (h_nonempty : ¬test1_nums = [])
    (h_unfold : postcondition test1_nums test1_Expected ↔ (test1_nums = [] → test1_Expected = 0) ∧ (¬test1_nums = [] → isLongestIncreasingSubsequenceLength test1_nums test1_Expected))
    (h_empty_case : test1_nums = [] → test1_Expected = 0)
    (h_sublist : [2, 3, 7, 18].Sublist test1_nums)
    (h_increasing : isStrictlyIncreasing [2, 3, 7, 18])
    (h_len_4 : True)
    : ∃ subseq, subseq.Sublist test1_nums ∧ isStrictlyIncreasing subseq ∧ subseq.length = 4 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_3
    (h_nums : test1_nums = [10, 9, 2, 5, 3, 7, 101, 18])
    (h_expected : test1_Expected = 4)
    (h_nonempty : ¬test1_nums = [])
    (h_unfold : postcondition test1_nums test1_Expected ↔ (test1_nums = [] → test1_Expected = 0) ∧ (¬test1_nums = [] → isLongestIncreasingSubsequenceLength test1_nums test1_Expected))
    (h_empty_case : test1_nums = [] → test1_Expected = 0)
    (h_sublist : [2, 3, 7, 18].Sublist test1_nums)
    (h_increasing : isStrictlyIncreasing [2, 3, 7, 18])
    (h_exists : ∃ subseq, subseq.Sublist test1_nums ∧ isStrictlyIncreasing subseq ∧ subseq.length = 4)
    (h_bound : ∀ (subseq : List ℤ), subseq.Sublist test1_nums → isStrictlyIncreasing subseq → subseq.length ≤ 4)
    (h_len_4 : True)
    : isLongestIncreasingSubsequenceLength test1_nums 4 := by
    unfold isLongestIncreasingSubsequenceLength
    exact ⟨h_exists, h_bound⟩

theorem test1_postcondition_2
    (h_nums : test1_nums = [10, 9, 2, 5, 3, 7, 101, 18])
    (h_expected : test1_Expected = 4)
    (h_nonempty : ¬test1_nums = [])
    (h_unfold : postcondition test1_nums test1_Expected ↔ (test1_nums = [] → test1_Expected = 0) ∧ (¬test1_nums = [] → isLongestIncreasingSubsequenceLength test1_nums test1_Expected))
    (h_empty_case : test1_nums = [] → test1_Expected = 0)
    (h_sublist : [2, 3, 7, 18].Sublist test1_nums)
    (h_increasing : isStrictlyIncreasing [2, 3, 7, 18])
    (h_exists : ∃ subseq, subseq.Sublist test1_nums ∧ isStrictlyIncreasing subseq ∧ subseq.length = 4)
    (h_len_4 : True)
    : ∀ (subseq : List ℤ), subseq.Sublist test1_nums → isStrictlyIncreasing subseq → subseq.length ≤ 4 := by
    sorry

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  -- First, establish the concrete values
  have h_nums : test1_nums = [10, 9, 2, 5, 3, 7, 101, 18] := by (try simp at *; expose_names); exact (rfl); done
  have h_expected : test1_Expected = 4 := by (try simp at *; expose_names); exact rfl; done
  -- The list is non-empty
  have h_nonempty : test1_nums ≠ [] := by (try simp at *; expose_names); exact (List.getLast?_isSome.mp rfl); done
  -- Unfold postcondition: we need both parts of the conjunction
  have h_unfold : postcondition test1_nums test1_Expected ↔ 
    (test1_nums = [] → test1_Expected = 0) ∧ 
    (test1_nums ≠ [] → isLongestIncreasingSubsequenceLength test1_nums test1_Expected) := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Part 1: Empty case is vacuously true (since list is non-empty)
  have h_empty_case : test1_nums = [] → test1_Expected = 0 := by (try simp at *; expose_names); exact (fun a ↦ False.elim (h_nonempty a)); done
  -- For part 2, we need isLongestIncreasingSubsequenceLength
  -- First, show [2, 3, 7, 18] is a sublist of test1_nums
  have h_sublist : [2, 3, 7, 18].Sublist test1_nums := by (try simp at *; expose_names); exact (List.isSublist_iff_sublist.mp rfl); done
  -- Show [2, 3, 7, 18] is strictly increasing
  have h_increasing : isStrictlyIncreasing [2, 3, 7, 18] := by (try simp at *; expose_names); exact (test1_postcondition_0 h_nums h_expected h_nonempty h_unfold h_empty_case h_sublist); done
  -- Show [2, 3, 7, 18] has length 4
  have h_len_4 : [2, 3, 7, 18].length = 4 := by (try simp at *; expose_names); exact h_expected; done
  -- Therefore exists a strictly increasing subsequence of length 4
  have h_exists : ∃ subseq : List Int, subseq.Sublist test1_nums ∧ isStrictlyIncreasing subseq ∧ subseq.length = 4 := by (try simp at *; expose_names); exact (test1_postcondition_1 h_nums h_expected h_nonempty h_unfold h_empty_case h_sublist h_increasing h_len_4); done
  -- For maximality: all strictly increasing sublists have length ≤ 4
  -- This is the key claim that requires checking all possibilities
  have h_bound : ∀ subseq : List Int, subseq.Sublist test1_nums → isStrictlyIncreasing subseq → subseq.length ≤ 4 := by (try simp at *; expose_names); exact (test1_postcondition_2 h_nums h_expected h_nonempty h_unfold h_empty_case h_sublist h_increasing h_exists h_len_4); done
  -- Combine existence and bound to get isLongestIncreasingSubsequenceLength
  have h_is_lis : isLongestIncreasingSubsequenceLength test1_nums 4 := by (try simp at *; expose_names); exact (test1_postcondition_3 h_nums h_expected h_nonempty h_unfold h_empty_case h_sublist h_increasing h_exists h_bound h_len_4); done
  -- Rewrite expected value
  have h_is_lis_expected : isLongestIncreasingSubsequenceLength test1_nums test1_Expected := by (try simp at *; expose_names); exact (h_is_lis); done
  -- Part 2: non-empty implies LIS length
  have h_nonempty_case : test1_nums ≠ [] → isLongestIncreasingSubsequenceLength test1_nums test1_Expected := by (try simp at *; expose_names); exact (fun a ↦ h_is_lis); done
  -- Combine both parts using the equivalence
  rw [h_unfold]
  exact ⟨h_empty_case, h_nonempty_case⟩
end Proof
