import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def isOdd (x : Int) : Prop := x % 2 ≠ 0

def IsOddAt (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ isOdd (a[i]!)




def IsFirstOddIndex (a : Array Int) (i : Nat) : Prop :=
  (i < a.size) ∧ isOdd (a[i]!) ∧ ∀ j : Nat, j < i → ¬ isOdd (a[j]!)



def precondition (a : Array Int) : Prop :=
  a.size > 0





def postcondition (a : Array Int) (result : Option Nat) : Prop :=
  match result with
  | none =>
      ∀ i : Nat, i < a.size → ¬ isOdd (a[i]!)
  | some i =>
      IsFirstOddIndex a i


def test1_a : Array Int := #[2, 4, 6, 8]

def test1_Expected : Option Nat := none

def test2_a : Array Int := #[3, 4, 6, 8]

def test2_Expected : Option Nat := some 0

def test3_a : Array Int := #[2, 4, 5, 8]

def test3_Expected : Option Nat := some 2







section Proof
theorem test1_precondition : precondition test1_a := by
  unfold precondition
  simp [test1_a]

theorem test1_postcondition : postcondition test1_a test1_Expected := by
  -- Step 1: unfold the expected result (it is `none`)
  have hExpected : test1_Expected = (none : Option Nat) := by
    simp [test1_Expected]
  -- Reduce the goal using the concrete expected value
  have hGoalEq : postcondition test1_a test1_Expected = postcondition test1_a (none : Option Nat) := by
    simp [hExpected]
  -- Step 2: unfold `postcondition` in the `none` case
  have hPostNone : postcondition test1_a (none : Option Nat) ↔ (∀ i : Nat, i < test1_a.size → ¬ isOdd (test1_a[i]!)) := by
    simp [postcondition]
  -- Step 3: compute the size of the concrete array
  have hSize : test1_a.size = 4 := by
    simp [test1_a]
  -- Step 6 (for each element): show each entry is not odd
  have hNotOdd0 : ¬ isOdd (test1_a[0]!) := by
    simp [isOdd, test1_a]
  have hNotOdd1 : ¬ isOdd (test1_a[1]!) := by
    simp [isOdd, test1_a]
  have hNotOdd2 : ¬ isOdd (test1_a[2]!) := by
    simp [isOdd, test1_a]
  have hNotOdd3 : ¬ isOdd (test1_a[3]!) := by
    simp [isOdd, test1_a]
  -- Steps 4-5-7: reduce the universal quantifier to the four possible indices using `i < 4`
  have hAll : ∀ i : Nat, i < test1_a.size → ¬ isOdd (test1_a[i]!) := by
    intro i hi
    have hi4 : i < 4 := by
      simpa [hSize] using hi
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      omega
    rcases hCases with rfl | rfl | rfl | rfl
    · simpa using hNotOdd0
    · simpa using hNotOdd1
    · simpa using hNotOdd2
    · simpa using hNotOdd3
  -- Conclude the postcondition for `none`, then rewrite back to `test1_Expected`
  have hPost : postcondition test1_a (none : Option Nat) := by
    exact (hPostNone.mpr hAll)
  simpa [hExpected] using hPost

theorem test2_precondition : precondition test2_a := by
  unfold precondition
  simp [test2_a]

theorem test2_postcondition : postcondition test2_a test2_Expected := by
  simp [postcondition, test2_Expected, IsFirstOddIndex, test2_a, isOdd]

theorem test3_precondition : precondition test3_a := by
  unfold precondition
  simp [test3_a]

theorem test3_postcondition : postcondition test3_a test3_Expected := by
  -- reduce postcondition with `some 2`
  simp [postcondition, test3_Expected, IsFirstOddIndex]
  constructor
  · decide
  constructor
  · -- show the element at index 2 is odd
    simp [isOdd, test3_a]
  · -- show all earlier indices are not odd
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    cases hj' with
    | inl hj0 =>
        subst hj0
        simp [isOdd, test3_a]
    | inr hj1 =>
        subst hj1
        simp [isOdd, test3_a]

theorem uniqueness
    (a : Array Int)
    : precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hPre
  intro ret1 ret2 hPost1 hPost2
  cases ret1 with
  | none =>
      cases ret2 with
      | none =>
          rfl
      | some i =>
          -- hPost1 says: no odd elements anywhere
          -- hPost2 says: i is first odd index, in particular a[i]! is odd
          have hNoOdd : ∀ k : Nat, k < a.size → ¬ isOdd (a[k]!) := by
            simpa [postcondition] using hPost1
          have hFirst : IsFirstOddIndex a i := by
            simpa [postcondition] using hPost2
          rcases hFirst with ⟨hi, hOddi, _hPrev⟩
          have : False := (hNoOdd i hi) hOddi
          exact (False.elim this)
  | some i =>
      cases ret2 with
      | none =>
          have hFirst : IsFirstOddIndex a i := by
            simpa [postcondition] using hPost1
          have hNoOdd : ∀ k : Nat, k < a.size → ¬ isOdd (a[k]!) := by
            simpa [postcondition] using hPost2
          rcases hFirst with ⟨hi, hOddi, _hPrev⟩
          have : False := (hNoOdd i hi) hOddi
          exact (False.elim this)
      | some j =>
          have hFirstI : IsFirstOddIndex a i := by
            simpa [postcondition] using hPost1
          have hFirstJ : IsFirstOddIndex a j := by
            simpa [postcondition] using hPost2
          rcases hFirstI with ⟨hi, hOddi, hPrevI⟩
          rcases hFirstJ with ⟨hj, hOddj, hPrevJ⟩
          have hij : i ≤ j := by
            by_contra hnot
            have hji : j < i := Nat.lt_of_not_ge hnot
            exact (hPrevI j hji) hOddj
          have hji : j ≤ i := by
            by_contra hnot
            have hij' : i < j := Nat.lt_of_not_ge hnot
            exact (hPrevJ i hij') hOddi
          have : i = j := Nat.le_antisymm hij hji
          simp [this]
end Proof
