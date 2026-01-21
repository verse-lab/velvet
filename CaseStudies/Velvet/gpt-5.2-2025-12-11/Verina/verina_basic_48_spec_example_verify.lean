import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def IsSquareNat (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n



def precondition (n : Nat) : Prop :=
  True




def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsSquareNat n) ∧
  (result = false ↔ ¬ IsSquareNat n)


def test1_n : Nat := 0

def test1_Expected : Bool := true

def test5_n : Nat := 2

def test5_Expected : Bool := false

def test8_n : Nat := 16

def test8_Expected : Bool := true







section Proof
theorem test1_precondition : precondition test1_n := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_n test1_Expected := by
  unfold postcondition test1_n test1_Expected IsSquareNat
  constructor
  · constructor
    · intro _
      refine ⟨0, ?_⟩
      simp
    · intro _
      rfl
  · constructor
    · intro h
      cases h
    · intro hnot
      exfalso
      apply hnot
      refine ⟨0, ?_⟩
      simp

theorem test5_precondition : precondition test5_n := by
    intros; expose_names; exact (trivial); done

theorem test5_postcondition : postcondition test5_n test5_Expected := by
  -- reduce to the concrete values
  simp [postcondition, test5_n, test5_Expected]
  -- it remains to show `¬ IsSquareNat 2`
  unfold IsSquareNat
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero =>
      simp at hk
  | succ k =>
      cases k with
      | zero =>
          simp at hk
      | succ k =>
          -- k = succ (succ k) ≥ 2, hence k*k ≥ 4, contradiction with hk : k*k = 2
          have hkk_ge_4 : (4 : Nat) ≤ Nat.succ (Nat.succ k) * Nat.succ (Nat.succ k) := by
            -- from 2 ≤ succ (succ k), multiply both sides by succ(succ k) (on the right)
            have h2le : (2 : Nat) ≤ Nat.succ (Nat.succ k) := by
              exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
            have h1 : 2 * Nat.succ (Nat.succ k) ≤ Nat.succ (Nat.succ k) * Nat.succ (Nat.succ k) := by
              simpa [Nat.mul_comm, Nat.mul_assoc] using
                (Nat.mul_le_mul_right (Nat.succ (Nat.succ k)) h2le)
            -- and 4 ≤ 2 * succ(succ k) since 2 ≤ succ(succ k), multiply by 2 on the left
            have h2 : (4 : Nat) ≤ 2 * Nat.succ (Nat.succ k) := by
              simpa [Nat.mul_assoc] using (Nat.mul_le_mul_left 2 h2le)
            exact le_trans h2 h1
          have : (4 : Nat) ≤ 2 := by simpa [hk] using hkk_ge_4
          exact (Nat.not_succ_le_self 1) (by simpa using this)

theorem test8_precondition : precondition test8_n := by
    intros; expose_names; exact (trivial); done

theorem test8_postcondition : postcondition test8_n test8_Expected := by
  -- First, prove the key fact that 16 is a square.
  have hsq : IsSquareNat 16 := by
    refine ⟨4, by decide⟩
  -- Now unfold/simplify the postcondition for (n = 16, result = true) and discharge both parts.
  constructor
  · -- (true = true ↔ IsSquareNat 16)
    simpa [postcondition, IsSquareNat, test8_n, test8_Expected, hsq]
  · -- (true = false ↔ ¬ IsSquareNat 16)
    -- The forward direction is impossible; the backward direction contradicts hsq.
    constructor
    · intro h
      cases h
    · intro hnot
      exfalso
      exact hnot hsq

theorem uniqueness
    (n : Nat)
    : precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hp
  intro ret1 ret2 h1 h2
  rcases h1 with ⟨h1_true, h1_false⟩
  rcases h2 with ⟨h2_true, h2_false⟩
  by_cases hs : IsSquareNat n
  · have r1t : ret1 = true := (h1_true.mpr hs)
    have r2t : ret2 = true := (h2_true.mpr hs)
    simpa [r1t, r2t]
  · have r1f : ret1 = false := (h1_false.mpr hs)
    have r2f : ret2 = false := (h2_false.mpr hs)
    simpa [r1f, r2f]
end Proof
