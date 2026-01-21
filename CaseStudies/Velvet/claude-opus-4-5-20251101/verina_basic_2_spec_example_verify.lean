import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def inArrayNat (arr : Array Nat) (val : Nat) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = val



def ensures1 (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some x =>

      inArrayNat s x ∧

      (∀ i : Nat, i < s.size → x ≤ s[i]!)

def precondition (s : Array Nat) :=
  True

def postcondition (s : Array Nat) (result : Option Nat) :=
  ensures1 s result


def test1_s : Array Nat := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

def test1_Expected : Option Nat := some 1

def test3_s : Array Nat := #[1]

def test3_Expected : Option Nat := some 1

def test8_s : Array Nat := #[]

def test8_Expected : Option Nat := none







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition ensures1 test1_Expected test1_s inArrayNat
  constructor
  · exact ⟨1, by native_decide, by native_decide⟩
  · intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | 4 => native_decide
    | 5 => native_decide
    | 6 => native_decide
    | 7 => native_decide
    | 8 => native_decide
    | 9 => native_decide
    | 10 => native_decide
    | n + 11 => simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi; omega

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition ensures1 test3_Expected test3_s inArrayNat
  constructor
  · exact ⟨0, by native_decide, by native_decide⟩
  · intro i hi
    match i with
    | 0 => native_decide
    | n + 1 => simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi; omega

theorem test8_precondition :
  precondition test8_s := by
  intros; expose_names; exact (trivial); done


theorem test8_postcondition :
  postcondition test8_s test8_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (s : Array Nat):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition ensures1 at hpost1 hpost2
  cases ret1 with
  | none =>
    cases ret2 with
    | none => rfl
    | some y =>
      -- ret1 = none means s.size = 0
      -- ret2 = some y means y is in array, contradiction
      simp only at hpost1
      obtain ⟨⟨i, hi_lt, _⟩, _⟩ := hpost2
      rw [hpost1] at hi_lt
      exact absurd hi_lt (Nat.not_lt_zero i)
  | some x =>
    cases ret2 with
    | none =>
      -- ret2 = none means s.size = 0
      -- ret1 = some x means x is in array, contradiction
      simp only at hpost2
      obtain ⟨⟨i, hi_lt, _⟩, _⟩ := hpost1
      rw [hpost2] at hi_lt
      exact absurd hi_lt (Nat.not_lt_zero i)
    | some y =>
      -- Both are some, need to show x = y
      obtain ⟨⟨i, hi_lt, hi_eq⟩, hx_min⟩ := hpost1
      obtain ⟨⟨j, hj_lt, hj_eq⟩, hy_min⟩ := hpost2
      -- x is at position i, so y ≤ s[i]! = x
      have hy_le_x : y ≤ x := by
        have := hy_min i hi_lt
        rw [hi_eq] at this
        exact this
      -- y is at position j, so x ≤ s[j]! = y
      have hx_le_y : x ≤ y := by
        have := hx_min j hj_lt
        rw [hj_eq] at this
        exact this
      -- By antisymmetry, x = y
      have : x = y := Nat.le_antisymm hx_le_y hy_le_x
      simp [this]
end Proof
