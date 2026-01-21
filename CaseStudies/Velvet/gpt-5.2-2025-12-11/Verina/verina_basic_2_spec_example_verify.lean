import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (s : Array Nat) :=
  True



def postcondition (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some min =>
      s.size > 0 ∧
      (∃ i, i < s.size ∧ s[i]! = min) ∧
      (∀ j, j < s.size → min ≤ s[j]!)


def test1_s : Array Nat := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

def test1_Expected : Option Nat := some 1

def test7_s : Array Nat := #[100, 99, 98]

def test7_Expected : Option Nat := some 98

def test8_s : Array Nat := #[]

def test8_Expected : Option Nat := none







section Proof

theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem test1_postcondition_0 (j : ℕ)
    (h_j_lt_11 : j < 11)
    (h_j_bound : j < 11)
    (h_size : True) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition test1_s test1_Expected
  simp only [Option.some.injEq]
  constructor
  · have h_size : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat).size = 11 := by (try simp at *; expose_names); try exact?; done
    have h_positive : 11 > 0 := by (try simp at *; expose_names); try exact?; done
    exact h_positive
  constructor
  · use 1
    constructor
    · have h_size : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat).size = 11 := by (try simp at *; expose_names); try exact?; done
      have h_bound : 1 < 11 := by (try simp at *; expose_names); try exact?; done
      exact h_bound
    · have h_index : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[1]! = 1 := by (try simp at *; expose_names); try exact?; done
      exact h_index
  · intro j h_j_bound
    have h_size : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat).size = 11 := by (try simp at *; expose_names); try exact?; done
    have h_j_lt_11 : j < 11 := by (try simp at *; expose_names); try exact?; done
    have h_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by (try simp at *; expose_names); try exact?; done
    rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[0]! = 3 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[0]! := by (try simp at *; expose_names); try exact?; done
      rw [h0]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[1]! = 1 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[1]! := by (try simp at *; expose_names); try exact?; done
      rw [h1]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[2]! = 4 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[2]! := by (try simp at *; expose_names); try exact?; done
      rw [h2]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[3]! = 1 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[3]! := by (try simp at *; expose_names); try exact?; done
      rw [h3]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[4]! = 5 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[4]! := by (try simp at *; expose_names); try exact?; done
      rw [h4]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[5]! = 9 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[5]! := by (try simp at *; expose_names); try exact?; done
      rw [h5]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[6]! = 2 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[6]! := by (try simp at *; expose_names); try exact?; done
      rw [h6]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[7]! = 6 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[7]! := by (try simp at *; expose_names); try exact?; done
      rw [h7]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[8]! = 5 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[8]! := by (try simp at *; expose_names); try exact?; done
      rw [h8]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[9]! = 3 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[9]! := by (try simp at *; expose_names); try exact?; done
      rw [h9]; exact h_result
    · have h_val : (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[10]! = 5 := by (try simp at *; expose_names); try exact?; done
      have h_result : 1 ≤ (#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : Array Nat)[10]! := by (try simp at *; expose_names); try exact?; done
      rw [h10]; exact h_result


theorem test7_precondition :
  precondition test7_s := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem test7_postcondition :
  postcondition test7_s test7_Expected := by
  unfold postcondition test7_s test7_Expected
  simp only []
  constructor
  · -- Prove test7_s.size > 0
    decide
  constructor
  · -- Prove ∃ i, i < test7_s.size ∧ test7_s[i]! = 98
    use 2
    constructor
    · decide
    · rfl
  · -- Prove ∀ j, j < test7_s.size → 98 ≤ test7_s[j]!
    intro j hj
    have hj_bound : j < 3 := hj
    -- Case analysis: j must be 0, 1, or 2
    interval_cases j
    · -- j = 0: test7_s[0]! = 100, and 98 ≤ 100
      decide
    · -- j = 1: test7_s[1]! = 99, and 98 ≤ 99
      decide
    · -- j = 2: test7_s[2]! = 98, and 98 ≤ 98
      decide


theorem test8_precondition :
  precondition test8_s := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )



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
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  cases ret1 with
  | none =>
    cases ret2 with
    | none => rfl
    | some min2 =>
      have h_size_eq_0 : s.size = 0 := h1
      have ⟨h_size_gt_0, _, _⟩ := h2
      omega
  | some min1 =>
    cases ret2 with
    | none =>
      have ⟨h_size_gt_0, _, _⟩ := h1
      have h_size_eq_0 : s.size = 0 := h2
      omega
    | some min2 =>
      have ⟨_, ⟨i, hi, h_eq_min1⟩, h_min1⟩ := h1
      have ⟨_, ⟨j, hj, h_eq_min2⟩, h_min2⟩ := h2
      have h_min2_le_min1 : min2 ≤ min1 := by
        rw [← h_eq_min1]
        exact h_min2 i hi
      have h_min1_le_min2 : min1 ≤ min2 := by
        rw [← h_eq_min2]
        exact h_min1 j hj
      have h_eq : min1 = min2 := Nat.le_antisymm h_min1_le_min2 h_min2_le_min1
      rw [h_eq]

end Proof
