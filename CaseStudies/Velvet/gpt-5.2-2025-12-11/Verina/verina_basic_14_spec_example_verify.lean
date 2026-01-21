import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def hasZ (s : String) : Prop :=
  ('z' ∈ s.toList) ∨ ('Z' ∈ s.toList)



def precondition (s : String) : Prop :=
  True



def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ hasZ s) ∧
  (result = false ↔ ¬ hasZ s)


def test1_s : String := "hello"

def test1_Expected : Bool := false

def test2_s : String := "zebra"

def test2_Expected : Bool := true

def test3_s : String := "Zebra"

def test3_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  -- unfold the concrete test values and the postcondition
  simp [postcondition, test1_s, test1_Expected, hasZ]

theorem test2_precondition :
  precondition test2_s := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_s test2_Expected := by
  -- unfold the concrete test values and the postcondition/hasZ definitions
  simp [postcondition, test2_s, test2_Expected, hasZ]

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  -- unfold concrete values and the postcondition
  simp [postcondition, test3_s, test3_Expected, hasZ]

theorem uniqueness (s : String) :
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨h1t, h1f⟩
  rcases hpost2 with ⟨h2t, h2f⟩
  classical
  by_cases hz : hasZ s
  · have hr1 : ret1 = true := (h1t.mpr hz)
    have hr2 : ret2 = true := (h2t.mpr hz)
    simp [hr1, hr2]
  · have hr1 : ret1 = false := (h1f.mpr hz)
    have hr2 : ret2 = false := (h2f.mpr hz)
    simp [hr1, hr2]
end Proof
