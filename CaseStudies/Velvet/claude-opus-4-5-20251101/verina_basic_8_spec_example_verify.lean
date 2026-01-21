import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) :=
  True



def ensures1 (a : Int) (b : Int) (result : Int) :=
  result ≤ a


def ensures2 (a : Int) (b : Int) (result : Int) :=
  result ≤ b


def ensures3 (a : Int) (b : Int) (result : Int) :=
  result = a ∨ result = b

def postcondition (a : Int) (b : Int) (result : Int) :=
  ensures1 a b result ∧ ensures2 a b result ∧ ensures3 a b result


def test1_a : Int := 3

def test1_b : Int := 5

def test1_Expected : Int := 3

def test4_a : Int := -3

def test4_b : Int := 5

def test4_Expected : Int := -3

def test6_a : Int := -3

def test6_b : Int := -5

def test6_Expected : Int := -5







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test1_a test1_b test1_Expected
  constructor
  · decide
  · constructor
    · decide
    · left; rfl

theorem test4_precondition :
  precondition test4_a test4_b := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_a test4_b test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test4_a test4_b test4_Expected
  constructor
  · decide
  · constructor
    · decide
    · left; rfl

theorem test6_precondition :
  precondition test6_a test6_b := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_a test6_b test6_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test6_a test6_b test6_Expected
  constructor
  · native_decide
  · constructor
    · native_decide
    · right; rfl

theorem uniqueness (a : Int) (b : Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  unfold ensures1 ensures2 ensures3 at h1 h2
  obtain ⟨h1_le_a, h1_le_b, h1_eq⟩ := h1
  obtain ⟨h2_le_a, h2_le_b, h2_eq⟩ := h2
  cases h1_eq with
  | inl h1_eq_a =>
    cases h2_eq with
    | inl h2_eq_a =>
      -- ret1 = a and ret2 = a
      rw [h1_eq_a, h2_eq_a]
    | inr h2_eq_b =>
      -- ret1 = a and ret2 = b
      -- From h1_le_b: ret1 ≤ b, and ret1 = a, so a ≤ b
      -- From h2_le_a: ret2 ≤ a, and ret2 = b, so b ≤ a
      -- Therefore a = b
      rw [h1_eq_a, h2_eq_b]
      have ha_le_b : a ≤ b := by rw [← h1_eq_a]; exact h1_le_b
      have hb_le_a : b ≤ a := by rw [← h2_eq_b]; exact h2_le_a
      exact Int.le_antisymm ha_le_b hb_le_a
  | inr h1_eq_b =>
    cases h2_eq with
    | inl h2_eq_a =>
      -- ret1 = b and ret2 = a
      -- From h1_le_a: ret1 ≤ a, and ret1 = b, so b ≤ a
      -- From h2_le_b: ret2 ≤ b, and ret2 = a, so a ≤ b
      -- Therefore a = b
      rw [h1_eq_b, h2_eq_a]
      have hb_le_a : b ≤ a := by rw [← h1_eq_b]; exact h1_le_a
      have ha_le_b : a ≤ b := by rw [← h2_eq_a]; exact h2_le_b
      exact (Int.le_antisymm ha_le_b hb_le_a).symm
    | inr h2_eq_b =>
      -- ret1 = b and ret2 = b
      rw [h1_eq_b, h2_eq_b]
end Proof
