import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def MissingFrom (s : List Nat) (n : Nat) : Prop := n ∉ s



def precondition (s : List Nat) : Prop :=
  s.Sorted (· ≤ ·)






def postcondition (s : List Nat) (result : Nat) : Prop :=
  MissingFrom s result ∧
  (∀ m : Nat, m < result → m ∈ s)


def test1_s : List Nat := [0, 1, 2, 6, 9]

def test1_Expected : Nat := 3

def test3_s : List Nat := [0, 1, 2, 3, 4, 5]

def test3_Expected : Nat := 6

def test7_s : List Nat := [0, 0, 1, 1, 3]

def test7_Expected : Nat := 2







section Proof
theorem test1_precondition :
  precondition test1_s := by
  unfold precondition test1_s
  decide

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition MissingFrom test1_s test1_Expected
  constructor
  · simp
  · intro m hm
    have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hm' with rfl | rfl | rfl
    · simp
    · simp
    · simp

theorem test3_precondition :
  precondition test3_s := by
  unfold precondition test3_s
  decide

theorem test3_postcondition_0
    (m : ℕ)
    (hm : m < 6)
    : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition MissingFrom test3_s test3_Expected
  constructor
  · have hA : (6 : Nat) ∉ ([0, 1, 2, 3, 4, 5] : List Nat) := by
      (try simp at *; expose_names); exact List.count_eq_zero.mp rfl; done
    exact hA
  · intro m hm
    have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by
      (try simp at *; expose_names); exact (test3_postcondition_0 m hm); done
    rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm0 : (0 : Nat) ∈ ([0, 1, 2, 3, 4, 5] : List Nat) := by
        (try simp at *; expose_names); exact List.mem_cons_self; done
      exact hm0
    · have hm1 : (1 : Nat) ∈ ([0, 1, 2, 3, 4, 5] : List Nat) := by
        (try simp at *; expose_names); exact List.mem_of_elem_eq_true rfl; done
      exact hm1
    · have hm2 : (2 : Nat) ∈ ([0, 1, 2, 3, 4, 5] : List Nat) := by
        (try simp at *; expose_names); exact List.mem_of_elem_eq_true rfl; done
      exact hm2
    · have hm3 : (3 : Nat) ∈ ([0, 1, 2, 3, 4, 5] : List Nat) := by
        (try simp at *; expose_names); exact List.mem_of_elem_eq_true rfl; done
      exact hm3
    · have hm4 : (4 : Nat) ∈ ([0, 1, 2, 3, 4, 5] : List Nat) := by
        (try simp at *; expose_names); exact List.mem_of_elem_eq_true rfl; done
      exact hm4
    · have hm5 : (5 : Nat) ∈ ([0, 1, 2, 3, 4, 5] : List Nat) := by
        (try simp at *; expose_names); exact List.mem_of_elem_eq_true rfl; done
      exact hm5

theorem test7_precondition :
  precondition test7_s := by
  unfold precondition test7_s
  decide

theorem test7_postcondition :
  postcondition test7_s test7_Expected := by
  -- unfold the specification and the concrete test values
  unfold postcondition MissingFrom test7_s test7_Expected
  constructor
  · -- 2 is not in [0,0,1,1,3]
    simp
  · -- every m < 2 is in [0,0,1,1,3]
    intro m hm
    have hm' : m = 0 ∨ m = 1 := by
      omega
    rcases hm' with rfl | rfl <;> simp

theorem uniqueness (s : List Nat):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hsorted
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨hret1_notmem, hsmall1⟩
  rcases hpost2 with ⟨hret2_notmem, hsmall2⟩
  have hle12 : ret1 ≤ ret2 := by
    have : ¬ ret2 < ret1 := by
      intro hlt
      have hmem : ret2 ∈ s := hsmall1 ret2 hlt
      exact hret2_notmem hmem
    exact (Nat.not_lt).1 this
  have hle21 : ret2 ≤ ret1 := by
    have : ¬ ret1 < ret2 := by
      intro hlt
      have hmem : ret1 ∈ s := hsmall2 ret1 hlt
      exact hret1_notmem hmem
    exact (Nat.not_lt).1 this
  exact Nat.le_antisymm hle12 hle21
end Proof
