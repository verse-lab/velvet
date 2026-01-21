import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedAsc (lst : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < lst.length → lst[i]! ≤ lst[j]!

def hasNoDuplicates (lst : List Int) : Prop :=
  ∀ i j : Nat, i < lst.length → j < lst.length → i ≠ j → lst[i]! ≠ lst[j]!



def ensures1 (arr : List Int) (result : List Int) :=
  isSortedAsc result


def ensures2 (arr : List Int) (result : List Int) :=
  hasNoDuplicates result


def ensures3 (arr : List Int) (result : List Int) :=
  ∀ x : Int, x ∈ result ↔ x ∈ arr

def precondition (arr : List Int) :=
  True

def postcondition (arr : List Int) (result : List Int) :=
  ensures1 arr result ∧ ensures2 arr result ∧ ensures3 arr result


def test1_arr : List Int := [1, 1, 2, 3]

def test1_Expected : List Int := [1, 2, 3]

def test2_arr : List Int := [3, 3, 3]

def test2_Expected : List Int := [3]

def test4_arr : List Int := [5, 2, 2, 5]

def test4_Expected : List Int := [2, 5]







section Proof
theorem test1_precondition :
  precondition test1_arr := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_arr test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isSortedAsc hasNoDuplicates test1_arr test1_Expected
  refine ⟨?_, ?_, ?_⟩
  · -- sorted ascending: ∀ i j, i < j → j < 3 → [1,2,3][i]! ≤ [1,2,3][j]!
    intro i j hij hjlen
    match j, hjlen with
    | 0, _ => omega
    | 1, _ => 
      match i with
      | 0 => native_decide
      | _ + 1 => omega
    | 2, _ =>
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | _ + 2 => omega
    | n + 3, h => simp only [List.length_cons, List.length_nil] at h; omega
  · -- no duplicates
    intro i j hilen hjlen hne
    match i, hilen, j, hjlen with
    | 0, _, 0, _ => omega
    | 0, _, 1, _ => native_decide
    | 0, _, 2, _ => native_decide
    | 1, _, 0, _ => native_decide
    | 1, _, 1, _ => omega
    | 1, _, 2, _ => native_decide
    | 2, _, 0, _ => native_decide
    | 2, _, 1, _ => native_decide
    | 2, _, 2, _ => omega
    | n + 3, h, _, _ => simp only [List.length_cons, List.length_nil] at h; omega
    | _, _, n + 3, h => simp only [List.length_cons, List.length_nil] at h; omega
  · -- same elements
    intro x
    simp only [List.mem_cons, List.mem_singleton]
    tauto

theorem test2_precondition :
  precondition test2_arr := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_arr test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isSortedAsc hasNoDuplicates
  unfold test2_arr test2_Expected
  refine ⟨?_, ?_, ?_⟩
  · -- sorted ascending: vacuously true for single element list
    intro i j hij hj
    simp only [List.length_singleton] at hj
    omega
  · -- no duplicates: vacuously true for single element list
    intro i j hi hj hne
    simp only [List.length_singleton] at hi hj
    omega
  · -- same elements
    intro x
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      left
      exact h
    · intro h
      rcases h with h | h | h
      · exact h
      · exact h
      · exact h

theorem test4_precondition :
  precondition test4_arr := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_arr test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isSortedAsc hasNoDuplicates
  unfold test4_arr test4_Expected
  refine ⟨?_, ?_, ?_⟩
  · -- isSortedAsc [2, 5]
    intro i j hij hjlen
    simp only [List.length] at hjlen
    interval_cases j
    · omega
    · interval_cases i
      · native_decide
  · -- hasNoDuplicates [2, 5]
    intro i j hilen hjlen hneq
    simp only [List.length] at hilen hjlen
    interval_cases i <;> interval_cases j <;> try omega
    · native_decide
    · native_decide
  · -- ensures3: ∀ x, x ∈ [2, 5] ↔ x ∈ [5, 2, 2, 5]
    intro x
    constructor
    · intro hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · right; left; rfl
      · left; rfl
    · intro hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem uniqueness_0
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    : isSortedAsc ret1 := by
    unfold postcondition at hpost1
    unfold ensures1 at hpost1
    exact hpost1.left

theorem uniqueness_1
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    : isSortedAsc ret2 := by
    intros; expose_names; exact (uniqueness_0 arr _hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    : hasNoDuplicates ret1 := by
    unfold postcondition at hpost1
    unfold ensures2 at hpost1
    exact hpost1.right.left

theorem uniqueness_3
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    : hasNoDuplicates ret2 := by
    intros; expose_names; exact (uniqueness_2 arr _hpre ret2 ret1 hpost2 hpost1 h_sorted2 h_sorted1); done

theorem uniqueness_4
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr := by
    unfold postcondition at hpost1
    unfold ensures3 at hpost1
    exact hpost1.2.2

theorem uniqueness_5
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    (h_mem1 : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr)
    : ∀ (x : ℤ), x ∈ ret2 ↔ x ∈ arr := by
    intros; expose_names; exact (uniqueness_4 arr _hpre ret2 ret1 hpost2 hpost1 h_sorted2 h_sorted1 h_nodup2 h_nodup1 x); done

theorem uniqueness_6
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    (h_mem1 : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr)
    (h_mem2 : ∀ (x : ℤ), x ∈ ret2 ↔ x ∈ arr)
    : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    (h_mem1 : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr)
    (h_mem2 : ∀ (x : ℤ), x ∈ ret2 ↔ x ∈ arr)
    (h_same_mem : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ ret2)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1 := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have h := h_sorted1 i j hij hj
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] at h
    exact h

theorem uniqueness_8
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    (h_mem1 : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr)
    (h_mem2 : ∀ (x : ℤ), x ∈ ret2 ↔ x ∈ arr)
    (h_same_mem : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ ret2)
    (h_pairwise1 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2 := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    unfold isSortedAsc at h_sorted2
    have h := h_sorted2 i j hij hj
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] at h
    exact h

theorem uniqueness_9
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    (h_mem1 : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr)
    (h_mem2 : ∀ (x : ℤ), x ∈ ret2 ↔ x ∈ arr)
    (h_same_mem : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ ret2)
    (h_pairwise1 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1)
    (h_pairwise2 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2)
    : ret1.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hne : i ≠ j := Nat.ne_of_lt hij
    have h := h_nodup1 i j hi hj hne
    -- Convert from getElem! to getElem
    simp only [List.getElem!_eq_getElem?_getD] at h
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
    simp at h
    exact h

theorem uniqueness_10
    (arr : List ℤ)
    (_hpre : precondition arr)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (hpost1 : postcondition arr ret1)
    (hpost2 : postcondition arr ret2)
    (h_sorted1 : isSortedAsc ret1)
    (h_sorted2 : isSortedAsc ret2)
    (h_nodup1 : hasNoDuplicates ret1)
    (h_nodup2 : hasNoDuplicates ret2)
    (h_mem1 : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ arr)
    (h_mem2 : ∀ (x : ℤ), x ∈ ret2 ↔ x ∈ arr)
    (h_same_mem : ∀ (x : ℤ), x ∈ ret1 ↔ x ∈ ret2)
    (h_pairwise1 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1)
    (h_pairwise2 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2)
    (h_nodup1' : ret1.Nodup)
    : ret2.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hne : i ≠ j := Nat.ne_of_lt hij
    have h := h_nodup2 i j hi hj hne
    simp only [List.getElem!_eq_getElem?_getD] at h
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
    simp only [Option.getD_some] at h
    exact h

theorem uniqueness (arr : List Int):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract the three properties from each postcondition
  have h_sorted1 : isSortedAsc ret1 := by (try simp at *; expose_names); exact (uniqueness_0 arr _hpre ret1 ret2 hpost1 hpost2); done
  have h_sorted2 : isSortedAsc ret2 := by (try simp at *; expose_names); exact (uniqueness_1 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1); done
  have h_nodup1 : hasNoDuplicates ret1 := by (try simp at *; expose_names); exact (uniqueness_2 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2); done
  have h_nodup2 : hasNoDuplicates ret2 := by (try simp at *; expose_names); exact (uniqueness_3 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1); done
  have h_mem1 : ∀ x : Int, x ∈ ret1 ↔ x ∈ arr := by (try simp at *; expose_names); exact (uniqueness_4 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2); done
  have h_mem2 : ∀ x : Int, x ∈ ret2 ↔ x ∈ arr := by (try simp at *; expose_names); exact (uniqueness_5 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2 h_mem1); done
  -- Both lists have the same elements
  have h_same_mem : ∀ x : Int, x ∈ ret1 ↔ x ∈ ret2 := by (try simp at *; expose_names); exact (uniqueness_6 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2 h_mem1 h_mem2); done
  -- Convert isSortedAsc to List.Pairwise (· ≤ ·)
  have h_pairwise1 : List.Pairwise (· ≤ ·) ret1 := by (try simp at *; expose_names); exact (uniqueness_7 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2 h_mem1 h_mem2 h_same_mem); done
  have h_pairwise2 : List.Pairwise (· ≤ ·) ret2 := by (try simp at *; expose_names); exact (uniqueness_8 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2 h_mem1 h_mem2 h_same_mem h_pairwise1); done
  -- Convert hasNoDuplicates to List.Nodup
  have h_nodup1' : List.Nodup ret1 := by (try simp at *; expose_names); exact (uniqueness_9 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2 h_mem1 h_mem2 h_same_mem h_pairwise1 h_pairwise2); done
  have h_nodup2' : List.Nodup ret2 := by (try simp at *; expose_names); exact (uniqueness_10 arr _hpre ret1 ret2 hpost1 hpost2 h_sorted1 h_sorted2 h_nodup1 h_nodup2 h_mem1 h_mem2 h_same_mem h_pairwise1 h_pairwise2 h_nodup1'); done
  -- Show that ret1 and ret2 are permutations of each other
  have h_perm : ret1.Perm ret2 := by (try simp at *; expose_names); exact ((List.perm_ext_iff_of_nodup h_nodup1' h_nodup2').mpr h_same_mem); done
  -- Antisymmetry for integers: if a ≤ b and b ≤ a then a = b
  have h_antisymm : ∀ a b : Int, a ∈ ret1 → b ∈ ret2 → a ≤ b → b ≤ a → a = b := by (try simp at *; expose_names); exact (fun a b a_1 a_2 a_3 a_4 ↦ Int.le_antisymm a_3 a_4); done
  -- Apply the key theorem: two sorted lists that are permutations are equal
  exact List.Perm.eq_of_sorted h_antisymm h_pairwise1 h_pairwise2 h_perm
end Proof
