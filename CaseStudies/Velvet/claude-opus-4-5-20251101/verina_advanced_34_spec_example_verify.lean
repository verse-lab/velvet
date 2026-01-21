import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (· < ·)

def isIncreasingSubseq (subseq : List Int) (nums : List Int) : Prop :=
  subseq.Sublist nums ∧ isStrictlyIncreasing subseq



def precondition (nums : List Int) : Prop :=
  True



def ensures1 (nums : List Int) (result : Int) : Prop :=
  result ≤ nums.length


def ensures2 (nums : List Int) (result : Int) : Prop :=
  ∃ subseq : List Int, isIncreasingSubseq subseq nums ∧ subseq.length = result.toNat


def ensures3 (nums : List Int) (result : Int) : Prop :=
  ∀ subseq : List Int, isIncreasingSubseq subseq nums → subseq.length ≤ result.toNat

def postcondition (nums : List Int) (result : Int) : Prop :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result


def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]

def test1_Expected : Int := 4

def test3_nums : List Int := [7, 7, 7, 7, 7, 7, 7]

def test3_Expected : Int := 1

def test5_nums : List Int := [10]

def test5_Expected : Int := 1







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (h_postcond_def : postcondition test1_nums test1_Expected ↔ ensures1 test1_nums test1_Expected ∧ ensures2 test1_nums test1_Expected ∧ ensures3 test1_nums test1_Expected)
    (h_list_length : test1_nums.length = 8)
    (h_result_val : test1_Expected = 4)
    : ensures1 test1_nums test1_Expected := by
    unfold ensures1
    simp only [test1_nums, test1_Expected]
    native_decide

theorem test1_postcondition_1
    (h_postcond_def : postcondition test1_nums test1_Expected ↔ ensures1 test1_nums test1_Expected ∧ ensures2 test1_nums test1_Expected ∧ ensures3 test1_nums test1_Expected)
    (h_list_length : test1_nums.length = 8)
    (h_result_val : test1_Expected = 4)
    (h_ensures1 : ensures1 test1_nums test1_Expected)
    (h_witness_sublist : [2, 5, 7, 101].Sublist test1_nums)
    : isStrictlyIncreasing [2, 5, 7, 101] := by
    unfold isStrictlyIncreasing
    native_decide

theorem test1_postcondition_2
    (h_postcond_def : postcondition test1_nums test1_Expected ↔ ensures1 test1_nums test1_Expected ∧ ensures2 test1_nums test1_Expected ∧ ensures3 test1_nums test1_Expected)
    (h_list_length : test1_nums.length = 8)
    (h_result_val : test1_Expected = 4)
    (h_ensures1 : ensures1 test1_nums test1_Expected)
    (h_witness_sublist : [2, 5, 7, 101].Sublist test1_nums)
    (h_witness_increasing : isStrictlyIncreasing [2, 5, 7, 101])
    : isIncreasingSubseq [2, 5, 7, 101] test1_nums := by
    unfold isIncreasingSubseq
    exact ⟨h_witness_sublist, h_witness_increasing⟩

theorem test1_postcondition_3
    (h_postcond_def : postcondition test1_nums test1_Expected ↔ ensures1 test1_nums test1_Expected ∧ ensures2 test1_nums test1_Expected ∧ ensures3 test1_nums test1_Expected)
    (h_list_length : test1_nums.length = 8)
    (h_result_val : test1_Expected = 4)
    (h_ensures1 : ensures1 test1_nums test1_Expected)
    (h_witness_sublist : [2, 5, 7, 101].Sublist test1_nums)
    (h_witness_increasing : isStrictlyIncreasing [2, 5, 7, 101])
    (h_witness_is_inc_subseq : isIncreasingSubseq [2, 5, 7, 101] test1_nums)
    (h_toNat_result : test1_Expected.toNat = 4)
    (h_witness_length : 4 = test1_Expected.toNat)
    : ensures2 test1_nums test1_Expected := by
    unfold ensures2
    use [2, 5, 7, 101]
    constructor
    · exact h_witness_is_inc_subseq
    · simp only [List.length_cons, List.length_nil]
      omega

theorem test1_postcondition_4
    (h_postcond_def : postcondition test1_nums test1_Expected ↔ ensures1 test1_nums test1_Expected ∧ ensures2 test1_nums test1_Expected ∧ ensures3 test1_nums test1_Expected)
    (h_list_length : test1_nums.length = 8)
    (h_result_val : test1_Expected = 4)
    (h_ensures1 : ensures1 test1_nums test1_Expected)
    (h_witness_sublist : [2, 5, 7, 101].Sublist test1_nums)
    (h_witness_increasing : isStrictlyIncreasing [2, 5, 7, 101])
    (h_witness_is_inc_subseq : isIncreasingSubseq [2, 5, 7, 101] test1_nums)
    (h_toNat_result : test1_Expected.toNat = 4)
    (h_ensures2 : ensures2 test1_nums test1_Expected)
    (h_witness_length : 4 = test1_Expected.toNat)
    : ensures3 test1_nums test1_Expected := by
    sorry

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  -- Unfold the postcondition definition
  have h_postcond_def : postcondition test1_nums test1_Expected ↔ ensures1 test1_nums test1_Expected ∧ ensures2 test1_nums test1_Expected ∧ ensures3 test1_nums test1_Expected := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Compute the list length
  have h_list_length : test1_nums.length = 8 := by (try simp at *; expose_names); exact rfl; done
  -- The expected result value
  have h_result_val : test1_Expected = 4 := by (try simp at *; expose_names); exact rfl; done
  -- Prove ensures1: result ≤ nums.length, i.e., 4 ≤ 8
  have h_ensures1 : ensures1 test1_nums test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_0 h_postcond_def h_list_length h_result_val); done
  -- Show that [2, 5, 7, 101] is a sublist of test1_nums
  have h_witness_sublist : [2, 5, 7, 101].Sublist test1_nums := by (try simp at *; expose_names); exact (List.isSublist_iff_sublist.mp rfl); done
  -- Show that [2, 5, 7, 101] is strictly increasing
  have h_witness_increasing : isStrictlyIncreasing [2, 5, 7, 101] := by (try simp at *; expose_names); exact (test1_postcondition_1 h_postcond_def h_list_length h_result_val h_ensures1 h_witness_sublist); done
  -- Combine to show [2, 5, 7, 101] is an increasing subsequence
  have h_witness_is_inc_subseq : isIncreasingSubseq [2, 5, 7, 101] test1_nums := by (try simp at *; expose_names); exact (test1_postcondition_2 h_postcond_def h_list_length h_result_val h_ensures1 h_witness_sublist h_witness_increasing); done
  -- Compute toNat of the result
  have h_toNat_result : test1_Expected.toNat = 4 := by (try simp at *; expose_names); exact rfl; done
  -- The witness has length equal to toNat of result
  have h_witness_length : ([2, 5, 7, 101] : List Int).length = test1_Expected.toNat := by (try simp at *; expose_names); exact (h_toNat_result); done
  -- Prove ensures2: existence of increasing subsequence of length 4
  have h_ensures2 : ensures2 test1_nums test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_3 h_postcond_def h_list_length h_result_val h_ensures1 h_witness_sublist h_witness_increasing h_witness_is_inc_subseq h_toNat_result h_witness_length); done
  -- For ensures3, we need to show all increasing subsequences have length ≤ 4
  -- This is decidable for concrete lists - use native_decide or direct proof
  have h_ensures3 : ensures3 test1_nums test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_4 h_postcond_def h_list_length h_result_val h_ensures1 h_witness_sublist h_witness_increasing h_witness_is_inc_subseq h_toNat_result h_ensures2 h_witness_length); done
  -- Combine all three ensures to prove postcondition
  rw [h_postcond_def]
  exact ⟨h_ensures1, h_ensures2, h_ensures3⟩
end Proof
