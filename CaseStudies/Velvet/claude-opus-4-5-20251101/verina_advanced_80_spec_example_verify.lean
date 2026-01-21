import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isValidPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

def hasUniqueSolution (nums : Array Int) (target : Int) : Prop :=
  ∃ i j, isValidPair nums target i j ∧
    (∀ i' j', isValidPair nums target i' j' → i' = i ∧ j' = j)



def precondition (nums : Array Int) (target : Int) :=
  nums.size ≥ 2 ∧ hasUniqueSolution nums target



def postcondition (nums : Array Int) (target : Int) (result : Array Nat) :=
  result.size = 2 ∧
  result[0]! < result[1]! ∧
  result[1]! < nums.size ∧
  nums[result[0]!]! + nums[result[1]!]! = target


def test1_nums : Array Int := #[2, 7, 11, 15]

def test1_target : Int := 9

def test1_Expected : Array Nat := #[0, 1]

def test2_nums : Array Int := #[3, 2, 4]

def test2_target : Int := 6

def test2_Expected : Array Nat := #[1, 2]

def test3_nums : Array Int := #[3, 3]

def test3_target : Int := 6

def test3_Expected : Array Nat := #[0, 1]







section Proof
theorem test1_precondition_0
    (h_j_lt_size : 1 < test1_nums.size)
    (h_sum : test1_nums[0]! + test1_nums[1]! = test1_target)
    (h_unfold : precondition test1_nums test1_target ↔ 2 ≤ test1_nums.size ∧ hasUniqueSolution test1_nums test1_target)
    (h_size : 2 ≤ test1_nums.size)
    (h_i_lt_j : True)
    : isValidPair test1_nums test1_target 0 1 := by
    unfold isValidPair
    exact ⟨Nat.zero_lt_one, h_j_lt_size, h_sum⟩

theorem test1_precondition_1
    (h_j_lt_size : 1 < test1_nums.size)
    (h_sum : test1_nums[0]! + test1_nums[1]! = test1_target)
    (h_valid_pair : isValidPair test1_nums test1_target 0 1)
    (h_unfold : precondition test1_nums test1_target ↔ 2 ≤ test1_nums.size ∧ hasUniqueSolution test1_nums test1_target)
    (h_size : 2 ≤ test1_nums.size)
    (h_i_lt_j : True)
    : ∀ (i' j' : ℕ), isValidPair test1_nums test1_target i' j' → i' = 0 ∧ j' = 1 := by
    intro i' j' h
    unfold isValidPair at h
    obtain ⟨h_lt, h_bound, h_eq⟩ := h
    have hsize : test1_nums.size = 4 := by native_decide
    rw [hsize] at h_bound
    have hi_bound : i' < 4 := Nat.lt_trans h_lt h_bound
    -- Check all cases by examining the sum condition
    have key : (i' = 0 ∧ j' = 1) := by
      match i', j' with
      | 0, 0 => omega
      | 0, 1 => exact ⟨rfl, rfl⟩
      | 0, 2 => simp only [test1_nums, test1_target] at h_eq; contradiction
      | 0, 3 => simp only [test1_nums, test1_target] at h_eq; contradiction
      | 0, j'+4 => omega
      | 1, 0 => omega
      | 1, 1 => omega
      | 1, 2 => simp only [test1_nums, test1_target] at h_eq; contradiction
      | 1, 3 => simp only [test1_nums, test1_target] at h_eq; contradiction
      | 1, j'+4 => omega
      | 2, 0 => omega
      | 2, 1 => omega
      | 2, 2 => omega
      | 2, 3 => simp only [test1_nums, test1_target] at h_eq; contradiction
      | 2, j'+4 => omega
      | 3, 0 => omega
      | 3, 1 => omega
      | 3, 2 => omega
      | 3, 3 => omega
      | 3, j'+4 => omega
      | i'+4, _ => omega
    exact key

theorem test1_precondition_2
    (h_j_lt_size : 1 < test1_nums.size)
    (h_sum : test1_nums[0]! + test1_nums[1]! = test1_target)
    (h_valid_pair : isValidPair test1_nums test1_target 0 1)
    (h_unique : ∀ (i' j' : ℕ), isValidPair test1_nums test1_target i' j' → i' = 0 ∧ j' = 1)
    (h_unfold : precondition test1_nums test1_target ↔ 2 ≤ test1_nums.size ∧ hasUniqueSolution test1_nums test1_target)
    (h_size : 2 ≤ test1_nums.size)
    (h_i_lt_j : True)
    : hasUniqueSolution test1_nums test1_target := by
    exact ⟨0, 1, h_valid_pair, h_unique⟩

theorem test1_precondition :
  precondition test1_nums test1_target := by
  -- First, unfold the definition of precondition
  have h_unfold : precondition test1_nums test1_target ↔ 
    (test1_nums.size ≥ 2 ∧ hasUniqueSolution test1_nums test1_target) := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Prove the size condition: test1_nums.size = 4 ≥ 2
  have h_size : test1_nums.size ≥ 2 := by (try simp at *; expose_names); exact (Nat.le_of_ble_eq_true rfl); done
  -- Now prove hasUniqueSolution: there exist unique indices i, j with the required properties
  -- The valid pair is (0, 1) since nums[0] + nums[1] = 2 + 7 = 9
  have h_i_lt_j : 0 < 1 := by (try simp at *; expose_names); exact Nat.one_pos; done
  have h_j_lt_size : 1 < test1_nums.size := by (try simp at *; expose_names); exact h_size; done
  have h_sum : test1_nums[0]! + test1_nums[1]! = test1_target := by (try simp at *; expose_names); exact (rfl); done
  -- Establish that (0, 1) is a valid pair
  have h_valid_pair : isValidPair test1_nums test1_target 0 1 := by (try simp at *; expose_names); exact (test1_precondition_0 h_j_lt_size h_sum h_unfold h_size h_i_lt_j); done
  -- Prove uniqueness: any valid pair must equal (0, 1)
  -- This requires checking all other pairs don't sum to 9
  have h_unique : ∀ i' j', isValidPair test1_nums test1_target i' j' → i' = 0 ∧ j' = 1 := by (try simp at *; expose_names); exact (test1_precondition_1 h_j_lt_size h_sum h_valid_pair h_unfold h_size h_i_lt_j); done
  -- Combine to get hasUniqueSolution
  have h_has_unique : hasUniqueSolution test1_nums test1_target := by (try simp at *; expose_names); exact (test1_precondition_2 h_j_lt_size h_sum h_valid_pair h_unique h_unfold h_size h_i_lt_j); done
  -- Finally combine size and uniqueness to get precondition
  exact ⟨h_size, h_has_unique⟩

theorem test1_postcondition :
  postcondition test1_nums test1_target test1_Expected := by
  unfold postcondition test1_nums test1_target test1_Expected
  native_decide

theorem test2_precondition :
  precondition test2_nums test2_target := by
  unfold precondition
  constructor
  · -- Prove nums.size ≥ 2
    native_decide
  · -- Prove hasUniqueSolution
    unfold hasUniqueSolution
    use 1, 2
    constructor
    · -- Prove isValidPair test2_nums test2_target 1 2
      unfold isValidPair
      native_decide
    · -- Prove uniqueness
      intro i' j' h_valid
      unfold isValidPair at h_valid
      obtain ⟨h_i_lt_j, h_j_lt_size, h_sum⟩ := h_valid
      have h_j_bound : j' < 3 := h_j_lt_size
      have h_i_bound : i' < 3 := Nat.lt_trans h_i_lt_j h_j_lt_size
      match i', j' with
      | 0, 0 => omega
      | 0, 1 => simp only [test2_nums, test2_target] at h_sum; norm_num at h_sum
      | 0, 2 => simp only [test2_nums, test2_target] at h_sum; norm_num at h_sum
      | 1, 0 => omega
      | 1, 1 => omega
      | 1, 2 => exact ⟨rfl, rfl⟩
      | 2, 0 => omega
      | 2, 1 => omega
      | 2, 2 => omega
      | 0, _ + 3 => omega
      | 1, _ + 3 => omega
      | 2, _ + 3 => omega
      | _ + 3, _ => omega

theorem test2_postcondition :
  postcondition test2_nums test2_target test2_Expected := by
  unfold postcondition test2_nums test2_target test2_Expected
  native_decide

theorem test3_precondition :
  precondition test3_nums test3_target := by
  unfold precondition hasUniqueSolution isValidPair test3_nums test3_target
  refine ⟨by decide, 0, 1, ⟨by omega, by decide, by decide⟩, ?_⟩
  intro i' j' ⟨h_lt, h_bound, h_sum⟩
  simp only [Array.size_toArray, List.length_cons, List.length_nil] at h_bound
  omega

theorem test3_postcondition :
  postcondition test3_nums test3_target test3_Expected := by
  unfold postcondition test3_nums test3_target test3_Expected
  native_decide

theorem uniqueness_0
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    : hasUniqueSolution nums target := by
    exact hpre.2

theorem uniqueness_1
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_exists_unique : ∃ i j, isValidPair nums target i j ∧ ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    : isValidPair nums target ret1[0]! ret1[1]! := by
    unfold postcondition at hpost1
    obtain ⟨_, h_lt, h_bound, h_sum⟩ := hpost1
    unfold isValidPair
    exact ⟨h_lt, h_bound, h_sum⟩

theorem uniqueness_2
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_exists_unique : ∃ i j, isValidPair nums target i j ∧ ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    : isValidPair nums target ret2[0]! ret2[1]! := by
    intros; expose_names; exact (uniqueness_1 nums target hpre ret2 ret1 hpost2 hpost1 h_unique_sol h_unique_sol); done

theorem uniqueness_3
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    : ret1[0]! = ret2[0]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_4
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    (h_elem0_eq : ret1[0]! = ret2[0]!)
    : ret1[1]! = ret2[1]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_5
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    (h_elem0_eq : ret1[0]! = ret2[0]!)
    (h_elem1_eq : ret1[1]! = ret2[1]!)
    : ret1.size = 2 := by
    exact hpost1.1

theorem uniqueness_6
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    (h_elem0_eq : ret1[0]! = ret2[0]!)
    (h_elem1_eq : ret1[1]! = ret2[1]!)
    (h_size1 : ret1.size = 2)
    : ret2.size = 2 := by
    exact hpost2.1

theorem uniqueness_7
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    (h_elem0_eq : ret1[0]! = ret2[0]!)
    (h_elem1_eq : ret1[1]! = ret2[1]!)
    (h_size1 : ret1.size = 2)
    (h_size2 : ret2.size = 2)
    : ret1.size = ret2.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_8
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    (h_elem0_eq : ret1[0]! = ret2[0]!)
    (h_elem1_eq : ret1[1]! = ret2[1]!)
    (h_size1 : ret1.size = 2)
    (h_size2 : ret2.size = 2)
    (h_size_eq : ret1.size = ret2.size)
    (idx : ℕ)
    (h_idx1 : 0 < ret1.size)
    (h_idx2 : 0 < ret2.size)
    (h_get0 : ret1[0] = ret1[0]!)
    (h_get0' : ret2[0] = ret2[0]!)
    (h_idx_bound : True)
    : ret1[0] = ret2[0] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_9
    (nums : Array ℤ)
    (target : ℤ)
    (hpre : precondition nums target)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition nums target ret1)
    (hpost2 : postcondition nums target ret2)
    (h_unique_sol : hasUniqueSolution nums target)
    (h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]!)
    (h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]!)
    (i : ℕ)
    (j : ℕ)
    (h_ij_valid : isValidPair nums target i j)
    (h_ij_unique : ∀ (i' j' : ℕ), isValidPair nums target i' j' → i' = i ∧ j' = j)
    (h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j)
    (h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j)
    (h_elem0_eq : ret1[0]! = ret2[0]!)
    (h_elem1_eq : ret1[1]! = ret2[1]!)
    (h_size1 : ret1.size = 2)
    (h_size2 : ret2.size = 2)
    (h_size_eq : ret1.size = ret2.size)
    (idx : ℕ)
    (h_idx1 : 1 < ret1.size)
    (h_idx2 : 1 < ret2.size)
    (h_get1 : ret1[1] = ret1[1]!)
    (h_get1' : ret2[1] = ret2[1]!)
    (h_idx_bound : True)
    : ret1[1] = ret2[1] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (nums : Array Int) (target : Int):
  precondition nums target →
  (∀ ret1 ret2,
    postcondition nums target ret1 →
    postcondition nums target ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract hasUniqueSolution from precondition
  have h_unique_sol : hasUniqueSolution nums target := by
    (try simp at *; expose_names); exact (uniqueness_0 nums target hpre ret1 ret2 hpost1 hpost2); done
  -- Get the unique pair (i, j) and its properties
  have h_exists_unique : ∃ i j, isValidPair nums target i j ∧ (∀ i' j', isValidPair nums target i' j' → i' = i ∧ j' = j) := by
    (try simp at *; expose_names); exact h_unique_sol; done
  -- ret1 defines a valid pair
  have h_ret1_valid : isValidPair nums target ret1[0]! ret1[1]! := by
    (try simp at *; expose_names); exact (uniqueness_1 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_exists_unique); done
  -- ret2 defines a valid pair
  have h_ret2_valid : isValidPair nums target ret2[0]! ret2[1]! := by
    (try simp at *; expose_names); exact (uniqueness_2 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_exists_unique h_ret1_valid); done
  -- Get the unique indices from hasUniqueSolution
  obtain ⟨i, j, h_ij_valid, h_ij_unique⟩ := h_exists_unique
  -- ret1 indices equal the unique pair
  have h_ret1_eq : ret1[0]! = i ∧ ret1[1]! = j := by
    (try simp at *; expose_names); exact h_ij_unique ret1[0]! ret1[1]! h_ret1_valid; done
  -- ret2 indices equal the unique pair
  have h_ret2_eq : ret2[0]! = i ∧ ret2[1]! = j := by
    (try simp at *; expose_names); exact h_ij_unique ret2[0]! ret2[1]! h_ret2_valid; done
  -- Therefore ret1 and ret2 have the same elements at index 0
  have h_elem0_eq : ret1[0]! = ret2[0]! := by
    (try simp at *; expose_names); exact (uniqueness_3 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq); done
  -- And the same elements at index 1
  have h_elem1_eq : ret1[1]! = ret2[1]! := by
    (try simp at *; expose_names); exact (uniqueness_4 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq h_elem0_eq); done
  -- Both arrays have size 2
  have h_size1 : ret1.size = 2 := by
    (try simp at *; expose_names); exact (uniqueness_5 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq h_elem0_eq h_elem1_eq); done
  have h_size2 : ret2.size = 2 := by
    (try simp at *; expose_names); exact (uniqueness_6 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq h_elem0_eq h_elem1_eq h_size1); done
  -- Sizes are equal
  have h_size_eq : ret1.size = ret2.size := by
    (try simp at *; expose_names); exact (uniqueness_7 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq h_elem0_eq h_elem1_eq h_size1 h_size2); done
  -- Use array extensionality to conclude equality
  apply Array.ext h_size_eq
  intro idx h_idx1 h_idx2
  have h_idx_bound : idx < 2 := by
    (try simp at *; expose_names); exact Nat.lt_of_lt_of_eq h_idx1 h_size1; done
  -- Case split on idx being 0 or 1
  interval_cases idx
  · -- idx = 0
    have h_get0 : ret1[0] = ret1[0]! := by (try simp at *; expose_names); exact (Eq.symm (getElem!_pos ret1 0 h_idx1)); done
    have h_get0' : ret2[0] = ret2[0]! := by (try simp at *; expose_names); exact (Eq.symm (getElem!_pos ret2 0 h_idx2)); done
    (try simp at *; expose_names); exact (uniqueness_8 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq h_elem0_eq h_elem1_eq h_size1 h_size2 h_size_eq idx h_idx1 h_idx2 h_get0 h_get0' h_idx_bound); done
  · -- idx = 1
    have h_get1 : ret1[1] = ret1[1]! := by (try simp at *; expose_names); exact (Eq.symm (getElem!_pos ret1 1 h_idx1)); done
    have h_get1' : ret2[1] = ret2[1]! := by (try simp at *; expose_names); exact (Eq.symm (getElem!_pos ret2 1 h_idx2)); done
    (try simp at *; expose_names); exact (uniqueness_9 nums target hpre ret1 ret2 hpost1 hpost2 h_unique_sol h_ret1_valid h_ret2_valid i j h_ij_valid h_ij_unique h_ret1_eq h_ret2_eq h_elem0_eq h_elem1_eq h_size1 h_size2 h_size_eq idx h_idx1 h_idx2 h_get1 h_get1' h_idx_bound); done
end Proof
