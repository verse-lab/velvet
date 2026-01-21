import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000










def precondition (arr : Array Int) :=
  True

def postcondition (arr : Array Int) (result : Int) :=
  ∃ distinctList : List Int,
    (∀ x, x ∈ distinctList ↔ x ∈ arr.toList) ∧
    distinctList.Nodup ∧
    result = distinctList.prod


def test1_arr : Array Int := #[2, 3, 2, 4]

def test1_Expected : Int := 24

def test3_arr : Array Int := #[]

def test3_Expected : Int := 1

def test6_arr : Array Int := #[-1, -2, -1, -3]

def test6_Expected : Int := -6







section Proof
theorem test1_precondition :
  precondition test1_arr := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_arr test1_Expected := by
  unfold postcondition test1_arr test1_Expected
  use [2, 3, 4]
  constructor
  · -- membership equivalence
    intro x
    simp only [Array.toList]
    constructor
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · simp [List.mem_cons]
      · simp [List.mem_cons]
      · simp [List.mem_cons]
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · simp [List.mem_cons]
      · simp [List.mem_cons]
      · simp [List.mem_cons]
      · simp [List.mem_cons]
  constructor
  · -- Nodup
    decide
  · -- product
    native_decide

theorem test3_precondition :
  precondition test3_arr := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_arr test3_Expected := by
  unfold postcondition test3_arr test3_Expected
  use []
  constructor
  · intro x
    simp [Array.toList_empty]
  constructor
  · exact List.nodup_nil
  · rfl

theorem test6_precondition :
  precondition test6_arr := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_arr test6_Expected := by
  unfold postcondition test6_arr test6_Expected
  use [-1, -2, -3]
  constructor
  · intro x
    simp only [Array.toList, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      rcases h with rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · right; right; right; rfl
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · left; rfl
      · right; right; rfl
  constructor
  · decide
  · native_decide

theorem uniqueness (arr : Array Int):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨L1, hmem1, hnodup1, hprod1⟩ := hpost1
  obtain ⟨L2, hmem2, hnodup2, hprod2⟩ := hpost2
  -- Show L1 and L2 are permutations
  have hmem_eq : ∀ x, x ∈ L1 ↔ x ∈ L2 := by
    intro x
    rw [hmem1 x, hmem2 x]
  have hperm : L1.Perm L2 := by
    rw [List.perm_ext_iff_of_nodup hnodup1 hnodup2]
    exact hmem_eq
  -- Products of permutations are equal
  have hprod_eq : L1.prod = L2.prod := List.Perm.prod_eq hperm
  -- Conclude
  rw [hprod1, hprod2, hprod_eq]
end Proof
