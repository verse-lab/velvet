import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x



def precondition (lst : List Int) : Prop :=
  True



def postcondition (lst : List Int) (result : Int) : Prop :=
  (hasMajorityElement lst → (result ∈ lst ∧ isMajorityElement lst result)) ∧
  (¬hasMajorityElement lst → result = -1)


def test1_lst : List Int := [1, 2, 1, 1]

def test1_Expected : Int := 1

def test3_lst : List Int := [2, 2, 2, 2, 3, 3]

def test3_Expected : Int := 2

def test7_lst : List Int := [-3, -3, -3, -3, 1]

def test7_Expected : Int := -3







section Proof
theorem test1_precondition :
  precondition test1_lst := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_lst test1_Expected := by
  unfold postcondition test1_lst test1_Expected
  unfold hasMajorityElement isMajorityElement
  constructor
  · -- First part: hasMajorityElement → result ∈ lst ∧ isMajorityElement
    intro _
    constructor
    · -- 1 ∈ [1, 2, 1, 1]
      native_decide
    · -- isMajorityElement [1, 2, 1, 1] 1
      native_decide
  · -- Second part: ¬hasMajorityElement → result = -1
    intro h
    exfalso
    apply h
    use 1
    constructor
    · native_decide
    · native_decide

theorem test3_precondition :
  precondition test3_lst := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_lst test3_Expected := by
  unfold postcondition test3_lst test3_Expected
  constructor
  · -- First part: hasMajorityElement → result ∈ lst ∧ isMajorityElement lst result
    intro _
    constructor
    · -- 2 ∈ [2, 2, 2, 2, 3, 3]
      native_decide
    · -- isMajorityElement [2, 2, 2, 2, 3, 3] 2
      unfold isMajorityElement
      native_decide
  · -- Second part: ¬hasMajorityElement → result = -1
    intro h
    exfalso
    apply h
    unfold hasMajorityElement
    use 2
    constructor
    · native_decide
    · unfold isMajorityElement
      native_decide

theorem test7_precondition :
  precondition test7_lst := by
  intros; expose_names; exact (trivial); done

theorem test7_postcondition :
  postcondition test7_lst test7_Expected := by
  unfold postcondition test7_lst test7_Expected
  constructor
  · -- hasMajorityElement → result ∈ lst ∧ isMajorityElement lst result
    intro _
    constructor
    · native_decide
    · unfold isMajorityElement
      native_decide
  · -- ¬hasMajorityElement → result = -1
    intro h
    exfalso
    apply h
    unfold hasMajorityElement
    use -3
    constructor
    · native_decide
    · unfold isMajorityElement
      native_decide

theorem uniqueness_0
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    : ret1 ∈ lst ∧ isMajorityElement lst ret1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_1
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    : ret2 ∈ lst ∧ isMajorityElement lst ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    (hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2)
    : isMajorityElement lst ret1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_3
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    (hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2)
    (hret1_is_maj : isMajorityElement lst ret1)
    : isMajorityElement lst ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_4_0
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    (hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2)
    (hne : ¬ret1 = ret2)
    (hcount1_le : List.count ret1 lst ≤ lst.length)
    (hcount2_le : List.count ret2 lst ≤ lst.length)
    (hret1_is_maj : lst.length / 2 < List.count ret1 lst)
    (hret2_is_maj : lst.length / 2 < List.count ret2 lst)
    (hcount1 : lst.length / 2 < List.count ret1 lst)
    (hcount2 : lst.length / 2 < List.count ret2 lst)
    (hne_symm : ¬ret1 = ret2)
    (hcount1_eq : List.count ret1 lst = List.countP (fun x ↦ x == ret1) lst)
    (hcount2_eq : List.count ret2 lst = List.countP (fun x ↦ x == ret2) lst)
    : lst.length = List.countP (fun x ↦ x == ret1) lst + List.countP (fun x ↦ !decide (x = ret1)) lst := by
    have h := List.length_eq_countP_add_countP (fun x => x == ret1) (l := lst)
    simp only [beq_iff_eq, decide_eq_true_eq] at h
    convert h using 2
    apply List.countP_congr
    intro x _
    simp only [beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]

theorem uniqueness_4_1
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    (hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2)
    (hne : ¬ret1 = ret2)
    (hcount1_le : List.count ret1 lst ≤ lst.length)
    (hcount2_le : List.count ret2 lst ≤ lst.length)
    (hret1_is_maj : lst.length / 2 < List.count ret1 lst)
    (hret2_is_maj : lst.length / 2 < List.count ret2 lst)
    (hcount1 : lst.length / 2 < List.count ret1 lst)
    (hcount2 : lst.length / 2 < List.count ret2 lst)
    (hne_symm : ¬ret1 = ret2)
    (hcount1_eq : List.count ret1 lst = List.countP (fun x ↦ x == ret1) lst)
    (hcount2_eq : List.count ret2 lst = List.countP (fun x ↦ x == ret2) lst)
    (hlen_split : lst.length = List.countP (fun x ↦ x == ret1) lst + List.countP (fun x ↦ !decide (x = ret1)) lst)
    : List.countP (fun x ↦ x == ret2) lst ≤ List.countP (fun x ↦ !decide (x = ret1)) lst := by
    apply List.countP_mono_left
    intro x _ hx_eq_ret2
    -- hx_eq_ret2 : (x == ret2) = true
    -- Need to show: !decide (x = ret1) = true
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    -- Need to show: x ≠ ret1
    have hx_is_ret2 : x = ret2 := by
      simp only [beq_iff_eq] at hx_eq_ret2
      exact hx_eq_ret2
    rw [hx_is_ret2]
    exact Ne.symm hne

theorem uniqueness_4
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    (hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2)
    (hne : ¬ret1 = ret2)
    (hcount1_le : List.count ret1 lst ≤ lst.length)
    (hcount2_le : List.count ret2 lst ≤ lst.length)
    (hret1_is_maj : lst.length / 2 < List.count ret1 lst)
    (hret2_is_maj : lst.length / 2 < List.count ret2 lst)
    (hcount1 : lst.length / 2 < List.count ret1 lst)
    (hcount2 : lst.length / 2 < List.count ret2 lst)
    : List.count ret1 lst + List.count ret2 lst ≤ lst.length := by
    have hne_symm : ret1 ≠ ret2 := by (try simp at *; expose_names); exact hne; done
    have hcount1_eq : List.count ret1 lst = List.countP (· == ret1) lst := by (try simp at *; expose_names); exact (rfl); done
    have hcount2_eq : List.count ret2 lst = List.countP (· == ret2) lst := by (try simp at *; expose_names); exact (rfl); done
    have hlen_split : lst.length = List.countP (· == ret1) lst + List.countP (fun x => ¬(x == ret1)) lst := by (try simp at *; expose_names); exact (uniqueness_4_0 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj hret2_maj hne hcount1_le hcount2_le hret1_is_maj hret2_is_maj hcount1 hcount2 hne_symm hcount1_eq hcount2_eq); done
    have hcount2_le_not_ret1 : List.countP (· == ret2) lst ≤ List.countP (fun x => ¬(x == ret1)) lst := by (try simp at *; expose_names); exact (uniqueness_4_1 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj hret2_maj hne hcount1_le hcount2_le hret1_is_maj hret2_is_maj hcount1 hcount2 hne_symm hcount1_eq hcount2_eq hlen_split); done
    have hcount1_rewrite : List.count ret1 lst = List.countP (· == ret1) lst := by (try simp at *; expose_names); exact (hcount1_eq); done
    have hcount2_rewrite : List.count ret2 lst = List.countP (· == ret2) lst := by (try simp at *; expose_names); exact (hcount2_eq); done
    have hsum_le : List.countP (· == ret1) lst + List.countP (· == ret2) lst ≤ List.countP (· == ret1) lst + List.countP (fun x => ¬(x == ret1)) lst := by (try simp at *; expose_names); exact (hcount2_le_not_ret1); done
    omega

theorem uniqueness_5
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : hasMajorityElement lst)
    (hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1)
    (hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2)
    (hne : ¬ret1 = ret2)
    (hcount1_le : List.count ret1 lst ≤ lst.length)
    (hcount2_le : List.count ret2 lst ≤ lst.length)
    (hsum_le : List.count ret1 lst + List.count ret2 lst ≤ lst.length)
    (hret1_is_maj : lst.length / 2 < List.count ret1 lst)
    (hret2_is_maj : lst.length / 2 < List.count ret2 lst)
    (hcount1 : lst.length / 2 < List.count ret1 lst)
    (hcount2 : lst.length / 2 < List.count ret2 lst)
    : lst.length < List.count ret1 lst + List.count ret2 lst := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_6
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : ¬hasMajorityElement lst)
    : ret1 = -1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7
    (lst : List ℤ)
    (_hpre : precondition lst)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : (hasMajorityElement lst → ret1 ∈ lst ∧ isMajorityElement lst ret1) ∧ (¬hasMajorityElement lst → ret1 = -1))
    (hpost2 : (hasMajorityElement lst → ret2 ∈ lst ∧ isMajorityElement lst ret2) ∧ (¬hasMajorityElement lst → ret2 = -1))
    (hmaj : ¬hasMajorityElement lst)
    (hret1_neg1 : ret1 = -1)
    : ret2 = -1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (lst : List Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  -- Case analysis on whether lst has a majority element
  by_cases hmaj : hasMajorityElement lst
  · -- Case 1: lst has a majority element
    have hret1_maj : ret1 ∈ lst ∧ isMajorityElement lst ret1 := by
      (try simp at *; expose_names); exact (uniqueness_0 lst _hpre ret1 ret2 hpost1 hpost2 hmaj); done
    have hret2_maj : ret2 ∈ lst ∧ isMajorityElement lst ret2 := by
      (try simp at *; expose_names); exact (uniqueness_1 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj); done
    have hret1_is_maj : isMajorityElement lst ret1 := by
      (try simp at *; expose_names); exact (uniqueness_2 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj hret2_maj); done
    have hret2_is_maj : isMajorityElement lst ret2 := by
      (try simp at *; expose_names); exact (uniqueness_3 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj hret2_maj hret1_is_maj); done
    -- Key: two majority elements must be equal
    unfold isMajorityElement at hret1_is_maj hret2_is_maj
    by_contra hne
    have hcount1 : lst.count ret1 > lst.length / 2 := by
      (try simp at *; expose_names); exact hret1_is_maj; done
    have hcount2 : lst.count ret2 > lst.length / 2 := by
      (try simp at *; expose_names); exact hret2_is_maj; done
    have hcount1_le : lst.count ret1 ≤ lst.length := by
      (try simp at *; expose_names); exact List.count_le_length; done
    have hcount2_le : lst.count ret2 ≤ lst.length := by
      (try simp at *; expose_names); exact List.count_le_length; done
    -- If ret1 ≠ ret2, the sum of their counts is at most lst.length
    have hsum_le : lst.count ret1 + lst.count ret2 ≤ lst.length := by
      (try simp at *; expose_names); exact (uniqueness_4 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj hret2_maj hne hcount1_le hcount2_le hret1_is_maj hret2_is_maj hcount1 hcount2); done
    -- But both counts > length/2 implies sum > length
    have hsum_gt : lst.count ret1 + lst.count ret2 > lst.length := by
      (try simp at *; expose_names); exact (uniqueness_5 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_maj hret2_maj hne hcount1_le hcount2_le hsum_le hret1_is_maj hret2_is_maj hcount1 hcount2); done
    omega
  · -- Case 2: lst does not have a majority element
    have hret1_neg1 : ret1 = -1 := by
      (try simp at *; expose_names); exact (uniqueness_6 lst _hpre ret1 ret2 hpost1 hpost2 hmaj); done
    have hret2_neg1 : ret2 = -1 := by
      (try simp at *; expose_names); exact (uniqueness_7 lst _hpre ret1 ret2 hpost1 hpost2 hmaj hret1_neg1); done
    calc ret1 = -1 := hret1_neg1
      _ = ret2 := hret2_neg1.symm
end Proof
