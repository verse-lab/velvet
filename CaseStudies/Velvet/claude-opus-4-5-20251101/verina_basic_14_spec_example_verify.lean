import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def ensures1 (s : String) (result : Bool) :=
  result = true ↔ (s.contains 'z' ∨ s.contains 'Z')

def ensures2 (s : String) (result : Bool) :=
  result = false ↔ (¬s.contains 'z' ∧ ¬s.contains 'Z')

def precondition (s : String) :=
  True

def postcondition (s : String) (result : Bool) :=
  ensures1 s result ∧ ensures2 s result


def test1_s : String := "hello"

def test1_Expected : Bool := false

def test2_s : String := "zebra"

def test2_Expected : Bool := true

def test4_s : String := ""

def test4_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_s test1_Expected
  constructor
  · -- ensures1: false = true ↔ ("hello".contains 'z' ∨ "hello".contains 'Z')
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · intro h
      cases h with
      | inl h1 => exact absurd h1 (by native_decide)
      | inr h2 => exact absurd h2 (by native_decide)
  · -- ensures2: false = false ↔ (¬"hello".contains 'z' ∧ ¬"hello".contains 'Z')
    constructor
    · intro _
      constructor
      · intro h; exact absurd h (by native_decide)
      · intro h; exact absurd h (by native_decide)
    · intro _
      rfl

theorem test2_precondition :
  precondition test2_s := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition_0 : "zebra".contains 'z' = true := by
    native_decide

theorem test2_postcondition_1
    (h_contains_z : "zebra".contains 'z' = true)
    (h_disj : "zebra".contains 'z' = true ∨ "zebra".contains 'Z' = true)
    (h_ensures1 : "zebra".contains 'z' = true ∨ "zebra".contains 'Z' = true)
    (h_true_ne_false : True)
    (h_not_contains_z_false : "zebra".contains 'z' = true)
    : "zebra".contains 'z' = false → "zebra".contains 'Z' = true := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_postcondition :
  postcondition test2_s test2_Expected := by
  -- First unfold definitions to see what we need to prove
  unfold postcondition ensures1 ensures2 test2_s test2_Expected
  -- Now we need: (true = true ↔ ("zebra".contains 'z' ∨ "zebra".contains 'Z')) ∧ 
  --              (true = false ↔ (¬"zebra".contains 'z' ∧ ¬"zebra".contains 'Z'))
  
  -- Establish that "zebra" contains 'z'
  have h_contains_z : "zebra".contains 'z' = true := by (try simp at *; expose_names); exact (test2_postcondition_0); done
  
  -- For ensures1 forward direction: true = true is trivial, need the disjunction
  have h_disj : "zebra".contains 'z' ∨ "zebra".contains 'Z' := by (try simp at *; expose_names); exact (Or.symm (Or.inr h_contains_z)); done
  
  -- For ensures1: true = true ↔ (contains 'z' ∨ contains 'Z')
  have h_ensures1 : true = true ↔ ("zebra".contains 'z' ∨ "zebra".contains 'Z') := by (try simp at *; expose_names); exact (h_disj); done
  
  -- For ensures2 forward: true = false is false, so forward direction holds vacuously
  have h_true_ne_false : true ≠ false := by (try simp at *; expose_names); exact (Bool.true_eq_false_eq_False); done
  
  -- For ensures2 backward: the hypothesis ¬contains 'z' ∧ ¬contains 'Z' contradicts h_contains_z
  have h_not_contains_z_false : ¬"zebra".contains 'z' → False := by (try simp at *; expose_names); exact (h_contains_z); done
  
  -- For ensures2: true = false ↔ (¬contains 'z' ∧ ¬contains 'Z')
  have h_ensures2 : true = false ↔ (¬"zebra".contains 'z' ∧ ¬"zebra".contains 'Z') := by (try simp at *; expose_names); exact (test2_postcondition_1 h_contains_z h_disj h_ensures1 h_true_ne_false h_not_contains_z_false); done
  
  -- Combine ensures1 and ensures2 into the final conjunction
  exact ⟨h_ensures1, h_ensures2⟩

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  unfold postcondition ensures1 ensures2 test4_s test4_Expected
  constructor
  · -- ensures1: false = true ↔ ("".contains 'z' ∨ "".contains 'Z')
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · intro h
      cases h with
      | inl hz => 
        have : "".contains 'z' = false := by native_decide
        simp [this] at hz
      | inr hZ => 
        have : "".contains 'Z' = false := by native_decide
        simp [this] at hZ
  · -- ensures2: false = false ↔ (¬"".contains 'z' ∧ ¬"".contains 'Z')
    constructor
    · intro _
      constructor
      · have : "".contains 'z' = false := by native_decide
        simp [this]
      · have : "".contains 'Z' = false := by native_decide
        simp [this]
    · intro _
      rfl

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  unfold ensures1 ensures2 at hpost1 hpost2
  obtain ⟨h1_iff1, h1_iff2⟩ := hpost1
  obtain ⟨h2_iff1, h2_iff2⟩ := hpost2
  -- Case split on whether s contains 'z' or 'Z'
  by_cases h : s.contains 'z' ∨ s.contains 'Z'
  · -- Case: s contains 'z' or 'Z', so both results should be true
    have hret1_true : ret1 = true := h1_iff1.mpr h
    have hret2_true : ret2 = true := h2_iff1.mpr h
    rw [hret1_true, hret2_true]
  · -- Case: s doesn't contain 'z' or 'Z', so both results should be false
    push_neg at h
    have hret1_false : ret1 = false := h1_iff2.mpr h
    have hret2_false : ret2 = false := h2_iff2.mpr h
    rw [hret1_false, hret2_false]
end Proof
