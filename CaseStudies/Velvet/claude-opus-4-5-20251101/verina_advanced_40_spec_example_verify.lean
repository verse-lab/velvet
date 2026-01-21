import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (lst : List Nat) :=
  lst.length > 0





def postcondition (lst : List Nat) (result : Nat) :=
  result ∈ lst ∧
  ∀ x, x ∈ lst → x ≤ result


def test1_lst : List Nat := [1, 2, 3]

def test1_Expected : Nat := 3

def test4_lst : List Nat := [7]

def test4_Expected : Nat := 7

def test7_lst : List Nat := [1, 100, 50]

def test7_Expected : Nat := 100







section Proof
theorem test1_precondition :
  precondition test1_lst := by
  unfold precondition test1_lst
  decide

theorem test1_postcondition :
  postcondition test1_lst test1_Expected := by
  unfold postcondition test1_lst test1_Expected
  constructor
  · -- 3 ∈ [1, 2, 3]
    simp [List.mem_cons]
  · -- ∀ x, x ∈ [1, 2, 3] → x ≤ 3
    intro x hx
    simp [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · omega
    · omega

theorem test4_precondition :
  precondition test4_lst := by
  unfold precondition test4_lst
  native_decide

theorem test4_postcondition :
  postcondition test4_lst test4_Expected := by
  unfold postcondition test4_lst test4_Expected
  constructor
  · simp [List.mem_singleton]
  · intro x hx
    simp [List.mem_singleton] at hx
    omega

theorem test7_precondition :
  precondition test7_lst := by
  unfold precondition test7_lst
  decide

theorem test7_postcondition :
  postcondition test7_lst test7_Expected := by
  unfold postcondition test7_lst test7_Expected
  constructor
  · -- Prove 100 ∈ [1, 100, 50]
    simp [List.mem_cons]
  · -- Prove ∀ x, x ∈ [1, 100, 50] → x ≤ 100
    intro x hx
    simp [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · omega  -- 1 ≤ 100
    · omega  -- 100 ≤ 100
    · omega  -- 50 ≤ 100

theorem uniqueness (lst : List Nat):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hmem1, hmax1⟩ := hpost1
  obtain ⟨hmem2, hmax2⟩ := hpost2
  have h1 : ret1 ≤ ret2 := hmax2 ret1 hmem1
  have h2 : ret2 ≤ ret1 := hmax1 ret2 hmem2
  exact Nat.le_antisymm h1 h2
end Proof
