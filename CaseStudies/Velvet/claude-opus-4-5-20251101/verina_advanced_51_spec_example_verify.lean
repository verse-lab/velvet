import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedInt (lst : List Int) : Prop :=
  ∀ i : Nat, i + 1 < lst.length → lst[i]! ≤ lst[i + 1]!



def precondition (a : List Int) (b : List Int) : Prop :=
  isSortedInt a ∧ isSortedInt b


def ensures1 (a : List Int) (b : List Int) (result : List Int) : Prop :=
  isSortedInt result



def ensures2 (a : List Int) (b : List Int) (result : List Int) : Prop :=
  result.Perm (a ++ b)



def postcondition (a : List Int) (b : List Int) (result : List Int) : Prop :=
  ensures1 a b result ∧ ensures2 a b result


def test1_a : List Int := [1, 3, 5]

def test1_b : List Int := [2, 4, 6]

def test1_Expected : List Int := [1, 2, 3, 4, 5, 6]

def test2_a : List Int := [1, 2]

def test2_b : List Int := [1, 2, 3]

def test2_Expected : List Int := [1, 1, 2, 2, 3]

def test5_a : List Int := [1, 4, 6]

def test5_b : List Int := [2, 3, 5]

def test5_Expected : List Int := [1, 2, 3, 4, 5, 6]







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  unfold precondition isSortedInt test1_a test1_b
  constructor
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    -- i + 1 < 3 means i < 2, so i ∈ {0, 1}
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    -- i + 1 < 3 means i < 2, so i ∈ {0, 1}
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_a test1_b test1_Expected
  constructor
  · -- Prove isSortedInt [1, 2, 3, 4, 5, 6]
    unfold isSortedInt
    intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | 4 => native_decide
    | n + 5 => simp at hi; omega
  · -- Prove permutation
    native_decide

theorem test2_precondition :
  precondition test2_a test2_b := by
  unfold precondition isSortedInt test2_a test2_b
  constructor
  · -- isSortedInt [1, 2]
    intro i hi
    match i with
    | 0 => native_decide
    | n + 1 => 
      -- hi : (n + 1) + 1 < 2, i.e., n + 2 < 2, which means n < 0, impossible
      simp only [List.length] at hi
      omega
  · -- isSortedInt [1, 2, 3]
    intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => 
      -- hi : (n + 2) + 1 < 3, i.e., n + 3 < 3, which means n < 0, impossible
      simp only [List.length] at hi
      omega

theorem test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  unfold postcondition ensures1 ensures2 test2_a test2_b test2_Expected
  constructor
  · -- Prove isSortedInt [1, 1, 2, 2, 3]
    unfold isSortedInt
    intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | n + 4 => simp only [List.length] at hi; omega
  · -- Prove [1, 1, 2, 2, 3].Perm ([1, 2] ++ [1, 2, 3])
    native_decide

theorem test5_precondition :
  precondition test5_a test5_b := by
  unfold precondition isSortedInt test5_a test5_b
  constructor
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega

theorem test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  unfold postcondition ensures1 ensures2
  constructor
  · unfold isSortedInt test5_Expected
    intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | 4 => native_decide
    | n + 5 => simp only [List.length] at hi; omega
  · unfold test5_Expected test5_a test5_b
    native_decide

theorem uniqueness_0
    (a : List ℤ)
    (b : List ℤ)
    (hpre : precondition a b)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition a b ret1)
    (hpost2 : postcondition a b ret2)
    : ensures1 a b ret1 := by
    exact hpost1.left

theorem uniqueness_1
    (a : List ℤ)
    (b : List ℤ)
    (hpre : precondition a b)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition a b ret1)
    (hpost2 : postcondition a b ret2)
    (h1_sorted : ensures1 a b ret1)
    : ensures1 a b ret2 := by
    intros; expose_names; exact (uniqueness_0 a b hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (a : List ℤ)
    (b : List ℤ)
    (hpre : precondition a b)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition a b ret1)
    (hpost2 : postcondition a b ret2)
    (h1_sorted : ensures1 a b ret1)
    (h2_sorted : ensures1 a b ret2)
    : ensures2 a b ret1 := by
    exact hpost1.right

theorem uniqueness_3
    (a : List ℤ)
    (b : List ℤ)
    (hpre : precondition a b)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition a b ret1)
    (hpost2 : postcondition a b ret2)
    (h1_sorted : ensures1 a b ret1)
    (h2_sorted : ensures1 a b ret2)
    (h1_perm : ensures2 a b ret1)
    : ensures2 a b ret2 := by
    intros; expose_names; exact (uniqueness_2 a b hpre ret2 ret1 hpost2 hpost1 h2_sorted h1_sorted); done

theorem uniqueness_4
    (a : List ℤ)
    (b : List ℤ)
    (hpre : precondition a b)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition a b ret1)
    (hpost2 : postcondition a b ret2)
    (h1_sorted : ensures1 a b ret1)
    (h2_sorted : ensures1 a b ret2)
    (h1_perm : ensures2 a b ret1)
    (h2_perm : ensures2 a b ret2)
    (h1_isSorted : isSortedInt ret1)
    (h2_isSorted : isSortedInt ret2)
    (h1_perm_ab : ret1.Perm (a ++ b))
    (h2_perm_ab : ret2.Perm (a ++ b))
    (h_perm_sym : (a ++ b).Perm ret2)
    (h_ret1_perm_ret2 : ret1.Perm ret2)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1 := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    -- We need to show ret1[i] ≤ ret1[j] for i < j
    -- h1_isSorted gives us: ∀ k, k + 1 < ret1.length → ret1[k]! ≤ ret1[k + 1]!
    have h_sorted_consec : ∀ k : Nat, (hk : k + 1 < ret1.length) → ret1[k]'(Nat.lt_of_succ_lt hk) ≤ ret1[k + 1]'hk := by
      intro k hk
      have := h1_isSorted k hk
      simp only [List.getElem!_eq_getElem?_getD] at this
      have hk1 : k < ret1.length := Nat.lt_of_succ_lt hk
      have hk2 : k + 1 < ret1.length := hk
      simp only [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2] at this
      simp at this
      exact this
    -- Prove by induction on the difference (j - i)
    have hmain : ∀ (d : Nat) (i j : Nat) (hi : i < ret1.length) (hj : j < ret1.length) (hij : i < j) (hdiff : j = i + d + 1), ret1[i] ≤ ret1[j] := by
      intro d
      induction d with
      | zero =>
        intro i j hi hj hij hdiff
        have : j = i + 1 := by omega
        subst this
        exact h_sorted_consec i hj
      | succ d' ih =>
        intro i j hi hj hij hdiff
        have hi1 : i + 1 < ret1.length := by omega
        have h1 : ret1[i] ≤ ret1[i + 1] := h_sorted_consec i hi1
        have h2 : ret1[i + 1] ≤ ret1[j] := ih (i + 1) j hi1 hj (by omega) (by omega)
        exact Int.le_trans h1 h2
    -- Apply hmain with d = j - i - 1
    have hdiff : j = i + (j - i - 1) + 1 := by omega
    exact hmain (j - i - 1) i j hi hj hij hdiff

theorem uniqueness_5
    (a : List ℤ)
    (b : List ℤ)
    (hpre : precondition a b)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition a b ret1)
    (hpost2 : postcondition a b ret2)
    (h1_sorted : ensures1 a b ret1)
    (h2_sorted : ensures1 a b ret2)
    (h1_perm : ensures2 a b ret1)
    (h2_perm : ensures2 a b ret2)
    (h1_isSorted : isSortedInt ret1)
    (h2_isSorted : isSortedInt ret2)
    (h1_perm_ab : ret1.Perm (a ++ b))
    (h2_perm_ab : ret2.Perm (a ++ b))
    (h_perm_sym : (a ++ b).Perm ret2)
    (h_ret1_perm_ret2 : ret1.Perm ret2)
    (h1_pairwise : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2 := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have h_consec : ∀ k : Nat, (hk : k + 1 < ret2.length) → ret2[k]'(Nat.lt_of_succ_lt hk) ≤ ret2[k + 1]'hk := by
      intro k hk
      have := h2_isSorted k hk
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.lt_of_succ_lt hk), List.getElem?_eq_getElem hk] at this
      simp only [Option.getD_some] at this
      exact this
    have h_trans : ∀ (d : Nat), ∀ (i' : Nat), (hid : i' + d < ret2.length) → ret2[i']'(Nat.lt_of_add_right_lt hid) ≤ ret2[i' + d]'hid := by
      intro d
      induction d with
      | zero =>
        intro i' hid
        simp
      | succ d' ih =>
        intro i' hid
        have hid' : i' + d' < ret2.length := by omega
        have h1 := ih i' hid'
        have hk : i' + d' + 1 < ret2.length := by omega
        have h2 := h_consec (i' + d') hk
        have hi'_lt : i' < ret2.length := Nat.lt_of_add_right_lt hid'
        have hi'd'_lt : i' + d' < ret2.length := hid'
        have hi'd'1_lt : i' + d' + 1 < ret2.length := hk
        have heq1 : ret2[i']'hi'_lt = ret2[i']'(Nat.lt_of_add_right_lt hid') := rfl
        have heq2 : i' + (d' + 1) = i' + d' + 1 := by omega
        calc ret2[i']'(Nat.lt_of_add_right_lt hid) ≤ ret2[i' + d']'hid' := by
               have : ret2[i']'(Nat.lt_of_add_right_lt hid) = ret2[i']'(Nat.lt_of_add_right_lt hid') := rfl
               rw [this]; exact h1
             _ ≤ ret2[i' + d' + 1]'hk := h2
             _ = ret2[i' + (d' + 1)]'hid := by simp only [Nat.add_assoc]
    have hji : i + (j - i) < ret2.length := by omega
    have key := h_trans (j - i) i hji
    have heq : i + (j - i) = j := by omega
    have hi_lt : i < ret2.length := hi
    have hj_lt : j < ret2.length := hj
    have : ret2[i]'(Nat.lt_of_add_right_lt hji) = ret2[i]'hi := rfl
    have : ret2[i + (j - i)]'hji = ret2[j]'hj := by simp only [heq]
    simp only [heq] at key
    exact key

theorem uniqueness (a : List Int) (b : List Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract the components of postcondition
  have h1_sorted : ensures1 a b ret1 := by (try simp at *; expose_names); exact (uniqueness_0 a b hpre ret1 ret2 hpost1 hpost2); done
  have h2_sorted : ensures1 a b ret2 := by (try simp at *; expose_names); exact (uniqueness_1 a b hpre ret1 ret2 hpost1 hpost2 h1_sorted); done
  have h1_perm : ensures2 a b ret1 := by (try simp at *; expose_names); exact (uniqueness_2 a b hpre ret1 ret2 hpost1 hpost2 h1_sorted h2_sorted); done
  have h2_perm : ensures2 a b ret2 := by (try simp at *; expose_names); exact (uniqueness_3 a b hpre ret1 ret2 hpost1 hpost2 h1_sorted h2_sorted h1_perm); done
  -- Unfold ensures1 to get isSortedInt
  have h1_isSorted : isSortedInt ret1 := by (try simp at *; expose_names); exact h1_sorted; done
  have h2_isSorted : isSortedInt ret2 := by (try simp at *; expose_names); exact h2_sorted; done
  -- Unfold ensures2 to get permutations
  have h1_perm_ab : ret1.Perm (a ++ b) := by (try simp at *; expose_names); exact h1_perm; done
  have h2_perm_ab : ret2.Perm (a ++ b) := by (try simp at *; expose_names); exact h2_perm; done
  -- By transitivity and symmetry, ret1 is a permutation of ret2
  have h_perm_sym : (a ++ b).Perm ret2 := by (try simp at *; expose_names); exact (id (List.Perm.symm h2_perm_ab)); done
  have h_ret1_perm_ret2 : ret1.Perm ret2 := by (try simp at *; expose_names); exact (List.Perm.trans h1_perm h_perm_sym); done
  -- Convert isSortedInt to List.Pairwise for ret1
  have h1_pairwise : ret1.Pairwise (· ≤ ·) := by (try simp at *; expose_names); exact (uniqueness_4 a b hpre ret1 ret2 hpost1 hpost2 h1_sorted h2_sorted h1_perm h2_perm h1_isSorted h2_isSorted h1_perm_ab h2_perm_ab h_perm_sym h_ret1_perm_ret2); done
  -- Convert isSortedInt to List.Pairwise for ret2
  have h2_pairwise : ret2.Pairwise (· ≤ ·) := by (try simp at *; expose_names); exact (uniqueness_5 a b hpre ret1 ret2 hpost1 hpost2 h1_sorted h2_sorted h1_perm h2_perm h1_isSorted h2_isSorted h1_perm_ab h2_perm_ab h_perm_sym h_ret1_perm_ret2 h1_pairwise); done
  -- Antisymmetry condition: for integers, a ≤ b and b ≤ a implies a = b
  have h_antisymm : ∀ (x y : Int), x ∈ ret1 → y ∈ ret2 → x ≤ y → y ≤ x → x = y := by (try simp at *; expose_names); exact (fun x y a a a a_1 ↦ Int.le_antisymm a a_1); done
  -- Apply the key lemma: sorted permutations are equal
  exact List.Perm.eq_of_sorted h_antisymm h1_pairwise h2_pairwise h_ret1_perm_ret2
end Proof
