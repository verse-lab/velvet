import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def HasNontrivialDivisor (n : Nat) : Prop :=
  ∃ k : Nat, 1 < k ∧ k < n ∧ k ∣ n



def precondition (n : Nat) : Prop :=
  2 ≤ n




def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ ¬ HasNontrivialDivisor n


def test1_n : Nat := 2

def test1_Expected : Bool := true

def test3_n : Nat := 4

def test3_Expected : Bool := false

def test5_n : Nat := 9

def test5_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_n := by
  simp [precondition, test1_n]

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition
  -- reduce concrete constants; goal becomes `True ↔ ¬ HasNontrivialDivisor 2`
  simp [test1_n, test1_Expected]
  -- now prove `¬ HasNontrivialDivisor 2`
  unfold HasNontrivialDivisor
  intro h
  rcases h with ⟨k, hk1, hk2, hkdiv⟩
  -- from `1 < k` and `k < 2` derive a contradiction
  have : ¬ (1 < k ∧ k < 2) := by
    omega
  exact this ⟨hk1, hk2⟩

theorem test3_precondition :
  precondition test3_n := by
  simp [precondition, test3_n]

theorem test3_postcondition :
  postcondition test3_n test3_Expected := by
  -- unfold the concrete test case
  simp [postcondition, test3_n, test3_Expected, HasNontrivialDivisor]
  -- goal: ¬(∃ k, 1 < k ∧ k < 4 ∧ k ∣ 4)
  -- provide a counterexample witness k = 2
  refine ⟨2, ?_, ?_, ?_⟩
  · decide
  · decide
  · refine ⟨2, by simp⟩

theorem test5_precondition :
  precondition test5_n := by
  simp [precondition, test5_n]

theorem test5_postcondition :
  postcondition test5_n test5_Expected := by
  -- unfold and simplify the concrete test values
  simp [postcondition, test5_n, test5_Expected, HasNontrivialDivisor]
  -- goal is now: ⊢ ∃ k, 1 < k ∧ k < 9 ∧ k ∣ 9
  refine ⟨3, ?_, ?_, ?_⟩
  · decide
  · decide
  · refine ⟨3, by decide⟩

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hn
  intro ret1 ret2 hpost1 hpost2
  -- unfold the postcondition: both ret1 and ret2 are characterized by the same proposition
  unfold postcondition at hpost1 hpost2
  -- derive (ret1 = true ↔ ret2 = true) and use Bool.eq_iff_iff to conclude ret1 = ret2
  apply (Bool.eq_iff_iff).2
  constructor
  · intro h1
    have : ¬ HasNontrivialDivisor n := (hpost1.mp h1)
    exact hpost2.mpr this
  · intro h2
    have : ¬ HasNontrivialDivisor n := (hpost2.mp h2)
    exact hpost1.mpr this
end Proof
