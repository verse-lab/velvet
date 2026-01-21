import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def AdjacentSorted (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!


def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!



def precondition (a : Array Int) : Prop :=
  True






def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ AdjacentSorted a) ∧
  (result = true → GloballySorted a) ∧
  (result = false ↔ ¬ AdjacentSorted a)


def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_Expected : Bool := true

def test3_a : Array Int := #[1, 3, 2, 4, 5]

def test3_Expected : Bool := false

def test4_a : Array Int := #[]

def test4_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (i : ℕ)
    (hi : i + 1 < 5)
    : [1, 2, 3, 4, 5][i]?.getD 0 ≤ [2, 3, 4, 5][i]?.getD 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_1
    (i : ℕ)
    (j : ℕ)
    (hij : i < j)
    (htrue : True)
    (hj : j < 5)
    : [1, 2, 3, 4, 5][i]?.getD 0 ≤ [1, 2, 3, 4, 5][j]?.getD 0 := by
  -- `htrue` is irrelevant
  -- Since `j < 5`, we can do a finite case split on `j` and then on `i < j`.
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl
  · -- j = 0, impossible
    exfalso
    exact Nat.not_lt_zero _ hij
  · -- j = 1, then i = 0
    have hi : i = 0 := by omega
    subst hi
    decide
  · -- j = 2, then i = 0 or 1
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> decide
  · -- j = 3, then i = 0 or 1 or 2
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> decide
  · -- j = 4, then i = 0 or 1 or 2 or 3
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> decide

theorem test1_postcondition_2
    (i : ℕ)
    (hi : i + 1 < 5)
    : [1, 2, 3, 4, 5][i]?.getD 0 ≤ [2, 3, 4, 5][i]?.getD 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_precondition :
  precondition test3_a := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_Expected := by
  -- unfold the concrete inputs and the postcondition structure
  simp [postcondition, test3_a, test3_Expected]
  -- goal is now to show `¬ AdjacentSorted #[1, 3, 2, 4, 5]`
  intro hAdj
  -- use the counterexample i = 1, where 3 ≤ 2 would be required
  have hsize : 1 + 1 < (#[1, 3, 2, 4, 5] : Array Int).size := by
    decide
  have hle : (#[1, 3, 2, 4, 5] : Array Int)[1]! ≤ (#[1, 3, 2, 4, 5] : Array Int)[1 + 1]! :=
    hAdj 1 hsize
  -- compute the array entries and contradict `3 ≤ 2`
  simpa using hle

theorem test4_precondition :
  precondition test4_a := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_a test4_Expected := by
  -- unfold definitions and reduce to vacuous truths about bounds into the empty array
  simp [postcondition, test4_a, test4_Expected, AdjacentSorted, GloballySorted, Nat.not_lt_zero]

theorem uniqueness (a : Array Int):
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨h1_true, _h1_global, h1_false⟩
  rcases hpost2 with ⟨h2_true, _h2_global, h2_false⟩
  by_cases ha : AdjacentSorted a
  · have hr1 : ret1 = true := (Iff.mpr h1_true) ha
    have hr2 : ret2 = true := (Iff.mpr h2_true) ha
    simpa [hr1, hr2]
  · have hr1 : ret1 = false := (Iff.mpr h1_false) ha
    have hr2 : ret2 = false := (Iff.mpr h2_false) ha
    simpa [hr1, hr2]
end Proof
