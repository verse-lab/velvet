import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000









def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  ((x ≥ 0 ∧ result = x) ∨ (x < 0 ∧ result = -x))


def test1_x : Int := 5

def test1_Expected : Int := 5

def test2_x : Int := 0

def test2_Expected : Int := 0

def test3_x : Int := -5

def test3_Expected : Int := 5







section Proof
theorem test1_precondition : precondition test1_x := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_x test1_Expected := by
  -- `simp` fully solves the concrete arithmetic/disjunction here.
  simp [postcondition, test1_x, test1_Expected]

theorem test2_precondition : precondition test2_x := by
    intros; expose_names; exact (trivial); done

theorem test2_postcondition : postcondition test2_x test2_Expected := by
  simp [postcondition, test2_x, test2_Expected]

theorem test3_precondition : precondition test3_x := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_x test3_Expected := by
  simp [postcondition, test3_x, test3_Expected]

theorem uniqueness
    (x : Int)
    : precondition x →
  (∀ ret1 ret2,
    postcondition x ret1 →
    postcondition x ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  rcases h1 with ⟨_h1nonneg, h1cases⟩
  rcases h2 with ⟨_h2nonneg, h2cases⟩
  by_cases hx : x ≥ 0
  · have hr1 : ret1 = x := by
      cases h1cases with
      | inl h => exact h.right
      | inr h =>
          exfalso
          have : ¬ x < 0 := by
            exact Lean.Omega.Int.not_lt_of_ge (x := 0) (y := x) hx
          exact this h.left
    have hr2 : ret2 = x := by
      cases h2cases with
      | inl h => exact h.right
      | inr h =>
          exfalso
          have : ¬ x < 0 := by
            exact Lean.Omega.Int.not_lt_of_ge (x := 0) (y := x) hx
          exact this h.left
    calc
      ret1 = x := hr1
      _ = ret2 := by simpa [hr2]
  · have hxlt : x < 0 := by
      -- hx : ¬ x ≥ 0, i.e. ¬ (0 ≤ x); convert to x < 0
      exact lt_of_not_ge hx
    have hr1 : ret1 = -x := by
      cases h1cases with
      | inl h =>
          exfalso
          exact hx h.left
      | inr h => exact h.right
    have hr2 : ret2 = -x := by
      cases h2cases with
      | inl h =>
          exfalso
          exact hx h.left
      | inr h => exact h.right
    calc
      ret1 = -x := hr1
      _ = ret2 := by simpa [hr2]
end Proof
