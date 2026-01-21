import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000






def precondition (a : Array Int) (b : Array Int) : Prop :=
  ¬(a.size = 0 ∧ b.size = 0)


instance (a : Array Int) (b : Array Int) : Decidable (precondition a b) := by
  dsimp [precondition]
  infer_instance




def postcondition (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  (result = true ↔ (∃ x : Int, x ∈ a ∧ x ∈ b))


def test1_a : Array Int := #[1, 2, 3]

def test1_b : Array Int := #[4, 5, 6]

def test1_Expected : Bool := false

def test2_a : Array Int := #[1, 2, 3]

def test2_b : Array Int := #[3, 4, 5]

def test2_Expected : Bool := true

def test7_a : Array Int := #[0]

def test7_b : Array Int := #[0]

def test7_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  unfold precondition
  native_decide

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  simp [postcondition, test1_a, test1_b, test1_Expected]

theorem test2_precondition :
  precondition test2_a test2_b := by
  unfold precondition
  native_decide

theorem test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  simp [postcondition, test2_a, test2_b, test2_Expected]

theorem test7_precondition :
  precondition test7_a test7_b := by
  unfold precondition test7_a test7_b
  native_decide

theorem test7_postcondition :
  postcondition test7_a test7_b test7_Expected := by
  unfold postcondition
  -- After unfolding/simplifying the concrete test data, the goal becomes trivial
  simp [test7_a, test7_b, test7_Expected]

theorem uniqueness (a : Array Int) (b : Array Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- unfold the postcondition equivalences
  dsimp [postcondition] at hpost1 hpost2
  -- both ret1 and ret2 are uniquely determined by the proposition on the RHS
  -- do case split on ret1
  by_cases h1 : ret1 = true
  · -- ret1 = true, so the proposition holds, hence ret2 = true
    have P : (∃ x : Int, x ∈ a ∧ x ∈ b) := (hpost1.mp h1)
    have h2 : ret2 = true := (hpost2.mpr P)
    -- now both are true
    simpa [h1, h2]
  · -- ret1 ≠ true, so ret1 = false
    have h1f : ret1 = false := eq_false_of_ne_true h1
    -- show ret2 must also be false
    have h2f : ret2 = false := by
      -- if ret2 were true we'd derive ret1 = true, contradiction
      apply eq_false_of_ne_true
      intro h2t
      have P : (∃ x : Int, x ∈ a ∧ x ∈ b) := (hpost2.mp h2t)
      have : ret1 = true := (hpost1.mpr P)
      exact h1 this
    simpa [h1f, h2f]
end Proof
