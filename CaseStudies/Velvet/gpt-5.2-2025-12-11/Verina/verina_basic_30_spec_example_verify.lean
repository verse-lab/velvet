import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def allNonzero (b : Array Int) : Prop :=
  ∀ (i : Nat), i < b.size → b[i]! ≠ 0






def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧ allNonzero b





def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
    (∀ (i : Nat), i < a.size → result[i]! = a[i]! % b[i]!)


def test1_a : Array Int := #[10, 20, 30]

def test1_b : Array Int := #[3, 7, 5]

def test1_Expected : Array Int := #[1, 6, 0]

def test3_a : Array Int := #[-10, -20, 30]

def test3_b : Array Int := #[3, -7, 5]

def test3_Expected : Array Int := #[2, 1, 0]

def test5_a : Array Int := #[7]

def test5_b : Array Int := #[3]

def test5_Expected : Array Int := #[1]







section Proof
theorem test1_precondition : precondition test1_a test1_b := by
  unfold precondition
  constructor
  · simp [test1_a, test1_b]
  · unfold allNonzero
    intro i hi
    -- decide the only possible indices using the bound i < 3
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
      have : i < 3 := by simpa [test1_b] using hi
      omega
    rcases hi' with rfl | rfl | rfl
    · simp [test1_b]
    · simp [test1_b]
    · simp [test1_b]

theorem test1_postcondition : postcondition test1_a test1_b test1_Expected := by
  unfold postcondition
  constructor
  · simp [test1_Expected, test1_a]
  · intro i hi
    -- reduce the bound to a concrete one
    have hi' : i < 3 := by simpa [test1_a] using hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
      have : i ≤ 2 := Nat.lt_succ_iff.mp hi'
      have h0or : i = 0 ∨ i = 1 ∨ i = 2 := by
        rcases Nat.eq_zero_or_pos i with h0 | hipos
        · exact Or.inl h0
        · have hi1 : i ≥ 1 := Nat.succ_le_iff.mp hipos
          have hpred : i - 1 ≤ 1 := by omega
          have : i = 1 ∨ i = 2 := by
            have : i - 1 = 0 ∨ i - 1 = 1 := by omega
            cases this with
            | inl h =>
              left
              omega
            | inr h =>
              right
              omega
          exact Or.inr (this.elim Or.inl Or.inr)
      exact h0or
    rcases hcases with rfl | rfl | rfl
    · simp [test1_Expected, test1_a, test1_b]
    · simp [test1_Expected, test1_a, test1_b]
    · simp [test1_Expected, test1_a, test1_b]

theorem test3_precondition : precondition test3_a test3_b := by
  unfold precondition
  constructor
  · simp [test3_a, test3_b]
  · unfold allNonzero
    intro i hi
    have hi' : i < 3 := by simpa [test3_b] using hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases hcases with rfl | rfl | rfl <;> simp [test3_b]

theorem test3_postcondition : postcondition test3_a test3_b test3_Expected := by
  unfold postcondition
  constructor
  · simp [test3_a, test3_Expected]
  · intro i hi
    have hi' : i < 3 := by simpa [test3_a] using hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases hcases with rfl | rfl | rfl
    · simp [test3_a, test3_b, test3_Expected]
    · simp [test3_a, test3_b, test3_Expected]
    · simp [test3_a, test3_b, test3_Expected]

theorem test5_precondition : precondition test5_a test5_b := by
  unfold precondition
  constructor
  · simp [test5_a, test5_b]
  · unfold allNonzero
    intro i hi
    have hi' : i = 0 := (Nat.lt_one_iff.mp (by simpa [test5_b] using hi))
    subst hi'
    simp [test5_b]

theorem test5_postcondition : postcondition test5_a test5_b test5_Expected := by
  unfold postcondition
  constructor
  · simp [test5_a, test5_Expected]
  · intro i hi
    have hi' : i = 0 := (Nat.lt_one_iff.mp (by simpa [test5_a] using hi))
    subst hi'
    simp [test5_a, test5_b, test5_Expected]

theorem uniqueness
    (a : Array Int)
    (b : Array Int)
    : precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨hsz1, hval1⟩
  rcases hpost2 with ⟨hsz2, hval2⟩
  apply Array.ext
    (by
      calc
        ret1.size = a.size := hsz1
        _ = ret2.size := by simpa [hsz2])
  intro i hi1 hi2
  have hia : i < a.size := by simpa [hsz1] using hi1
  -- both are equal to the same RHS given by the postcondition
  calc
    ret1[i] = ret1[i]! := by
      simp [Array.get!, hi1]
    _ = a[i]! % b[i]! := hval1 i hia
    _ = ret2[i]! := (hval2 i hia).symm
    _ = ret2[i] := by
      simp [Array.get!, hi2]
end Proof
