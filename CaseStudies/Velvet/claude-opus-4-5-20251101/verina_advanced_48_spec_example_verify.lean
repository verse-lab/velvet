import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedAsc (l : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! ≤ l[j]!


def isPermutation (l1 l2 : List Int) : Prop :=
  List.Perm l1 l2



def precondition (list : List Int) : Prop :=
  True



def postcondition (list : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermutation list result


def test1_list : List Int := [5, 2, 9, 1, 5, 6]

def test1_Expected : List Int := [1, 2, 5, 5, 6, 9]

def test3_list : List Int := []

def test3_Expected : List Int := []

def test8_list : List Int := [-3, -1, -5, -2]

def test8_Expected : List Int := [-5, -3, -2, -1]







section Proof
theorem test1_precondition :
  precondition test1_list := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_list test1_Expected := by
  unfold postcondition
  constructor
  · -- isSortedAsc test1_Expected
    unfold isSortedAsc test1_Expected
    intro i j hij hjlen
    simp only [List.length_cons, List.length_nil] at hjlen
    -- j < 6, so j ∈ {0,1,2,3,4,5}, and i < j
    interval_cases j
    all_goals interval_cases i
    all_goals simp [List.getElem!_cons_zero, List.getElem!_cons_succ]
    all_goals native_decide
  · -- isPermutation test1_list test1_Expected
    unfold isPermutation test1_list test1_Expected
    native_decide

theorem test3_precondition :
  precondition test3_list := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_list test3_Expected := by
  unfold postcondition
  constructor
  · -- isSortedAsc []
    unfold isSortedAsc test3_Expected
    intro i j hij hjlen
    -- hjlen : j < [].length = j < 0, which is false for Nat
    simp [List.length_nil] at hjlen
  · -- isPermutation [] []
    unfold isPermutation test3_list test3_Expected
    exact List.Perm.nil

theorem test8_precondition :
  precondition test8_list := by
  intros; expose_names; exact (trivial); done

theorem test8_postcondition :
  postcondition test8_list test8_Expected := by
  unfold postcondition test8_list test8_Expected
  constructor
  · -- isSortedAsc [-5, -3, -2, -1]
    unfold isSortedAsc
    intro i j hij hjlen
    simp only [List.length] at hjlen
    match j with
    | 0 => omega
    | 1 => 
      match i with
      | 0 => native_decide
      | _ + 1 => omega
    | 2 =>
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | _ + 2 => omega
    | 3 =>
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | _ + 3 => omega
    | n + 4 => omega
  · -- isPermutation [-3, -1, -5, -2] [-5, -3, -2, -1]
    unfold isPermutation
    native_decide

theorem uniqueness_0
    (list : List ℤ)
    (hpre : precondition list)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition list ret1)
    (hpost2 : postcondition list ret2)
    : isSortedAsc ret1 := by
    unfold postcondition at hpost1
    exact hpost1.left

theorem uniqueness_1
    (list : List ℤ)
    (hpre : precondition list)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition list ret1)
    (hpost2 : postcondition list ret2)
    (h_sorted1 : isSortedAsc ret1)
    : isSortedAsc ret2 := by
    intros; expose_names; exact (uniqueness_0 list hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (list : List ℤ)
    (hpre : precondition list)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition list ret1)
    (hpost2 : postcondition list ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    : isPermutation list ret1 := by
    exact hpost1.right

theorem uniqueness_3
    (list : List ℤ)
    (hpre : precondition list)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition list ret1)
    (hpost2 : postcondition list ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_perm1 : isPermutation list ret1)
    : isPermutation list ret2 := by
    intros; expose_names; exact (uniqueness_2 list hpre ret2 ret1 hpost2 hpost1 h_sorted2 h_sorted1); done

theorem uniqueness_4
    (list : List ℤ)
    (hpre : precondition list)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition list ret1)
    (hpost2 : postcondition list ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_perm1 : isPermutation list ret1)
    (h_perm2 : isPermutation list ret2)
    (h_perm1' : list.Perm ret1)
    (h_perm2' : list.Perm ret2)
    (h_perm1_sym : ret1.Perm list)
    (h_perm_ret1_ret2 : ret1.Perm ret2)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1 := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have h := h_sorted1 i j hij hj
    simp only [List.getElem!_eq_getElem?_getD] at h
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
    simp at h
    exact h

theorem uniqueness_5
    (list : List ℤ)
    (hpre : precondition list)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition list ret1)
    (hpost2 : postcondition list ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_perm1 : isPermutation list ret1)
    (h_perm2 : isPermutation list ret2)
    (h_perm1' : list.Perm ret1)
    (h_perm2' : list.Perm ret2)
    (h_perm1_sym : ret1.Perm list)
    (h_perm_ret1_ret2 : ret1.Perm ret2)
    (h_pairwise1 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2 := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have h := h_sorted2 i j hij hj
    have hi' : i < ret2.length := Nat.lt_trans hij hj
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj, Option.getD_some] at h
    exact h

theorem uniqueness (list : List Int):
  precondition list →
  (∀ ret1 ret2,
    postcondition list ret1 →
    postcondition list ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the components from postconditions
  have h_sorted1 : isSortedAsc ret1 := by (try simp at *; expose_names); exact (uniqueness_0 list hpre ret1 ret2 hpost1 hpost2); done
  have h_sorted2 : isSortedAsc ret2 := by (try simp at *; expose_names); exact (uniqueness_1 list hpre ret1 ret2 hpost1 hpost2 h_sorted1); done
  have h_perm1 : isPermutation list ret1 := by (try simp at *; expose_names); exact (uniqueness_2 list hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2); done
  have h_perm2 : isPermutation list ret2 := by (try simp at *; expose_names); exact (uniqueness_3 list hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_perm1); done
  -- Convert isPermutation to List.Perm
  have h_perm1' : List.Perm list ret1 := by (try simp at *; expose_names); exact h_perm1; done
  have h_perm2' : List.Perm list ret2 := by (try simp at *; expose_names); exact h_perm2; done
  -- Get permutation between ret1 and ret2 using transitivity and symmetry
  have h_perm1_sym : List.Perm ret1 list := by (try simp at *; expose_names); exact (id (List.Perm.symm h_perm1')); done
  have h_perm_ret1_ret2 : List.Perm ret1 ret2 := by (try simp at *; expose_names); exact (List.Perm.trans h_perm1_sym h_perm2); done
  -- Convert isSortedAsc to List.Pairwise (· ≤ ·)
  have h_pairwise1 : List.Pairwise (· ≤ ·) ret1 := by (try simp at *; expose_names); exact (uniqueness_4 list hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_perm1 h_perm2 h_perm1' h_perm2' h_perm1_sym h_perm_ret1_ret2); done
  have h_pairwise2 : List.Pairwise (· ≤ ·) ret2 := by (try simp at *; expose_names); exact (uniqueness_5 list hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_perm1 h_perm2 h_perm1' h_perm2' h_perm1_sym h_perm_ret1_ret2 h_pairwise1); done
  -- Prove the antisymmetry condition needed for eq_of_sorted
  have h_antisym : ∀ (a b : Int), a ∈ ret1 → b ∈ ret2 → a ≤ b → b ≤ a → a = b := by (try simp at *; expose_names); exact (fun a b a_1 a_2 a_3 a_4 ↦ Int.le_antisymm a_3 a_4); done
  -- Apply the uniqueness theorem for sorted permutations
  exact List.Perm.eq_of_sorted h_antisym h_pairwise1 h_pairwise2 h_perm_ret1_ret2
end Proof
