import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isValidPermutation (nums : List Int) : Prop :=
  let n := nums.length
  n > 0 ∧
  (∀ x, x ∈ nums → 1 ≤ x ∧ x ≤ n) ∧
  nums.Nodup ∧
  (∀ k : Nat, 1 ≤ k ∧ k ≤ n → (k : Int) ∈ nums)

def findIndex (nums : List Int) (val : Int) : Nat :=
  nums.findIdx (· == val)

def isSemiOrdered (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums[0]! = 1 ∧ nums[nums.length - 1]! = (nums.length : Int)

def swapAt (nums : List Int) (i : Nat) : List Int :=
  if i + 1 < nums.length then
    nums.set i (nums[i + 1]!) |>.set (i + 1) (nums[i]!)
  else
    nums



def precondition (nums : List Int) : Prop :=
  isValidPermutation nums











def postcondition (nums : List Int) (result : Int) : Prop :=
  let n := nums.length
  let idx1 := findIndex nums 1
  let idxN := findIndex nums (n : Int)

  result ≥ 0 ∧

  (result = 0 ↔ isSemiOrdered nums) ∧


  (idx1 ≤ idxN → result = (idx1 : Int) + ((n - 1 : Int) - (idxN : Int))) ∧
  (idx1 > idxN → result = (idx1 : Int) + ((n - 1 : Int) - (idxN : Int)) - 1)


def test1_nums : List Int := [2, 1, 4, 3]

def test1_Expected : Int := 2

def test2_nums : List Int := [2, 4, 1, 3]

def test2_Expected : Int := 3

def test4_nums : List Int := [3, 1, 2]

def test4_Expected : Int := 2







section Proof
theorem test1_precondition_0
    (h_test1_def : test1_nums = [2, 1, 4, 3])
    (h_length : test1_nums.length = 4)
    (h_pos : 0 < test1_nums.length)
    : ∀ x ∈ test1_nums, 1 ≤ x ∧ x ≤ ↑test1_nums.length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_precondition_1
    (h_test1_def : test1_nums = [2, 1, 4, 3])
    (h_length : test1_nums.length = 4)
    (h_range : ∀ x ∈ test1_nums, 1 ≤ x ∧ x ≤ ↑test1_nums.length)
    (h_pos : 0 < test1_nums.length)
    : test1_nums.Nodup := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_precondition_2
    (h_test1_def : test1_nums = [2, 1, 4, 3])
    (h_length : test1_nums.length = 4)
    (h_range : ∀ x ∈ test1_nums, 1 ≤ x ∧ x ≤ ↑test1_nums.length)
    (h_nodup : test1_nums.Nodup)
    (h_pos : 0 < test1_nums.length)
    : ∀ (k : ℕ), 1 ≤ k → k ≤ test1_nums.length → ↑k ∈ test1_nums := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_precondition :
  precondition test1_nums := by
  -- precondition is isValidPermutation, which has 4 conditions
  -- test1_nums = [2, 1, 4, 3], n = 4
  
  have h_test1_def : test1_nums = [2, 1, 4, 3] := by (try simp at *; expose_names); exact rfl; done
  
  have h_length : test1_nums.length = 4 := by (try simp at *; expose_names); exact rfl; done
  
  have h_pos : test1_nums.length > 0 := by (try simp at *; expose_names); exact (Nat.zero_lt_succ [1, 4, 3].length); done
  
  have h_range : ∀ x, x ∈ test1_nums → 1 ≤ x ∧ x ≤ test1_nums.length := by (try simp at *; expose_names); exact (test1_precondition_0 h_test1_def h_length h_pos); done
  
  have h_nodup : test1_nums.Nodup := by (try simp at *; expose_names); exact (test1_precondition_1 h_test1_def h_length h_range h_pos); done
  
  have h_complete : ∀ k : Nat, 1 ≤ k ∧ k ≤ test1_nums.length → (k : Int) ∈ test1_nums := by (try simp at *; expose_names); exact (test1_precondition_2 h_test1_def h_length h_range h_nodup h_pos); done
  
  unfold precondition isValidPermutation
  exact ⟨h_pos, h_range, h_nodup, h_complete⟩

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition test1_nums test1_Expected findIndex isSemiOrdered
  simp only [List.length_cons, List.length_nil]
  native_decide

theorem test2_precondition : precondition test2_nums := by
  unfold precondition isValidPermutation test2_nums
  simp only [List.length_cons, List.length_nil]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · -- All elements in range [1, 4]
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · -- Nodup
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, 
               not_false_eq_true, and_true, List.nodup_nil, or_false]
    decide
  · -- All k in [1, 4] appear in list
    intro k ⟨hk1, hk2⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    omega

theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  unfold postcondition test2_nums test2_Expected findIndex isSemiOrdered
  native_decide

theorem test4_precondition : precondition test4_nums := by
  unfold precondition isValidPermutation test4_nums
  simp only [List.length_cons, List.length_nil]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · omega
    · omega
  · native_decide
  · intro k ⟨hk1, hk2⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    omega

theorem test4_postcondition :
  postcondition test4_nums test4_Expected := by
  unfold postcondition test4_nums test4_Expected findIndex isSemiOrdered
  native_decide

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  simp only at hpost1 hpost2
  obtain ⟨hge1, hiff1, hle1, hgt1⟩ := hpost1
  obtain ⟨hge2, hiff2, hle2, hgt2⟩ := hpost2
  let idx1 := findIndex nums 1
  let idxN := findIndex nums (nums.length : Int)
  cases le_or_lt idx1 idxN with
  | inl hle =>
    have h1 : ret1 = (idx1 : Int) + ((nums.length - 1 : Int) - (idxN : Int)) := hle1 hle
    have h2 : ret2 = (idx1 : Int) + ((nums.length - 1 : Int) - (idxN : Int)) := hle2 hle
    omega
  | inr hgt =>
    have hgt' : idx1 > idxN := hgt
    have h1 : ret1 = (idx1 : Int) + ((nums.length - 1 : Int) - (idxN : Int)) - 1 := hgt1 hgt'
    have h2 : ret2 = (idx1 : Int) + ((nums.length - 1 : Int) - (idxN : Int)) - 1 := hgt2 hgt'
    omega
end Proof
