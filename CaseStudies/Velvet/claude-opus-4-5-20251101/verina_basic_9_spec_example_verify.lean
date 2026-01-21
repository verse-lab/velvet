import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def hasCommon (a : Array Int) (b : Array Int) : Prop :=
  ∃ x : Int, x ∈ a.toList ∧ x ∈ b.toList

def ensures1 (a : Array Int) (b : Array Int) (result : Bool) :=
  result = true ↔ hasCommon a b



def precondition (a : Array Int) (b : Array Int) :=
  a.size > 0 ∧ b.size > 0

def postcondition (a : Array Int) (b : Array Int) (result : Bool) :=
  ensures1 a b result


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
  unfold precondition test1_a test1_b
  constructor
  · decide
  · decide

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition ensures1 hasCommon test1_a test1_b test1_Expected
  constructor
  · -- forward: false = true → ∃ x, x ∈ [1,2,3] ∧ x ∈ [4,5,6]
    intro h
    exact absurd h Bool.false_ne_true
  · -- backward: ∃ x, x ∈ [1,2,3] ∧ x ∈ [4,5,6] → false = true
    intro ⟨x, hx_in_a, hx_in_b⟩
    simp only [Array.toList] at hx_in_a hx_in_b
    -- x ∈ [1, 2, 3] means x = 1 ∨ x = 2 ∨ x = 3
    -- x ∈ [4, 5, 6] means x = 4 ∨ x = 5 ∨ x = 6
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx_in_a hx_in_b
    rcases hx_in_a with rfl | rfl | rfl
    · -- x = 1, need 1 ∈ [4, 5, 6] which is false
      rcases hx_in_b with h | h | h <;> omega
    · -- x = 2, need 2 ∈ [4, 5, 6] which is false
      rcases hx_in_b with h | h | h <;> omega
    · -- x = 3, need 3 ∈ [4, 5, 6] which is false
      rcases hx_in_b with h | h | h <;> omega

theorem test2_precondition : precondition test2_a test2_b := by
  unfold precondition test2_a test2_b
  constructor
  · decide
  · decide

theorem test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  unfold postcondition ensures1 hasCommon test2_a test2_b test2_Expected
  constructor
  · -- Forward: true = true → ∃ x, x ∈ [1,2,3] ∧ x ∈ [3,4,5]
    intro _
    use 3
    constructor
    · -- 3 ∈ #[1, 2, 3].toList
      native_decide
    · -- 3 ∈ #[3, 4, 5].toList
      native_decide
  · -- Backward: ∃ x, x ∈ [1,2,3] ∧ x ∈ [3,4,5] → true = true
    intro _
    rfl

theorem test7_precondition :
  precondition test7_a test7_b := by
  unfold precondition test7_a test7_b
  constructor
  · native_decide
  · native_decide

theorem test7_postcondition :
  postcondition test7_a test7_b test7_Expected := by
  unfold postcondition ensures1 hasCommon test7_a test7_b test7_Expected
  constructor
  · intro _
    exact ⟨0, by native_decide, by native_decide⟩
  · intro _
    rfl

theorem uniqueness (a : Array Int) (b : Array Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- hpost1 : ret1 = true ↔ hasCommon a b
  -- hpost2 : ret2 = true ↔ hasCommon a b
  unfold postcondition ensures1 at hpost1 hpost2
  -- We need to show ret1 = ret2
  -- Using Bool.eq_iff_iff: ret1 = ret2 ↔ (ret1 ↔ ret2)
  rw [Bool.eq_iff_iff]
  -- Now we need: ret1 ↔ ret2
  -- We have: (ret1 = true) ↔ hasCommon a b  and  (ret2 = true) ↔ hasCommon a b
  -- First, note that for booleans, b ↔ (b = true)
  have h1 : ret1 ↔ (ret1 = true) := by cases ret1 <;> simp
  have h2 : ret2 ↔ (ret2 = true) := by cases ret2 <;> simp
  -- Now: ret1 ↔ (ret1 = true) ↔ hasCommon a b ↔ (ret2 = true) ↔ ret2
  calc ret1 ↔ (ret1 = true) := h1
    _ ↔ hasCommon a b := hpost1
    _ ↔ (ret2 = true) := hpost2.symm
    _ ↔ ret2 := h2.symm
end Proof
