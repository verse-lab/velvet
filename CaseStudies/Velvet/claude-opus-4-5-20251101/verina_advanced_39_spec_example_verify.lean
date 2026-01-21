import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (lst : List Nat) :=
  lst ≠ []





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
  exact List.cons_ne_nil 1 [2, 3]

theorem test1_postcondition :
  postcondition test1_lst test1_Expected := by
  unfold postcondition test1_lst test1_Expected
  constructor
  · -- Show 3 ∈ [1, 2, 3]
    simp [List.mem_cons, List.mem_singleton]
  · -- Show ∀ x, x ∈ [1, 2, 3] → x ≤ 3
    intro x hx
    simp [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · omega
    · omega

theorem test4_precondition :
  precondition test4_lst := by
  unfold precondition test4_lst
  exact List.cons_ne_nil 7 []

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
  exact List.cons_ne_nil 1 [100, 50]

theorem test7_postcondition :
  postcondition test7_lst test7_Expected := by
  unfold postcondition test7_lst test7_Expected
  constructor
  · simp [List.mem_cons]
  · intro x hx
    simp [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · omega
    · omega

theorem uniqueness (lst : List Nat):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hret1_mem, hret1_max⟩ := hpost1
  obtain ⟨hret2_mem, hret2_max⟩ := hpost2
  have h1 : ret1 ≤ ret2 := hret2_max ret1 hret1_mem
  have h2 : ret2 ≤ ret1 := hret1_max ret2 hret2_mem
  exact Nat.le_antisymm h1 h2
end Proof
