import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing (xs : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length → xs[i]! < xs[j]!

def countLessThan (xs : List Int) (target : Int) : Nat :=
  xs.countP (· < target)



def precondition (xs : List Int) (target : Int) : Prop :=
  isStrictlyIncreasing xs



def ensures1 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result ≤ xs.length


def ensures2 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ∀ i : Nat, i < result → i < xs.length → xs[i]! < target


def ensures3 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ∀ i : Nat, result ≤ i → i < xs.length → xs[i]! ≥ target


def ensures4 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result = countLessThan xs target

def postcondition (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ensures1 xs target result ∧
  ensures2 xs target result ∧
  ensures3 xs target result ∧
  ensures4 xs target result


def test1_xs : List Int := [1, 3, 5, 6]

def test1_target : Int := 5

def test1_Expected : Nat := 2

def test2_xs : List Int := [1, 3, 5, 6]

def test2_target : Int := 2

def test2_Expected : Nat := 1

def test5_xs : List Int := []

def test5_target : Int := 3

def test5_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_xs test1_target := by
  unfold precondition isStrictlyIncreasing test1_xs
  intro i j hij hjlen
  simp only [List.length_cons, List.length_nil] at hjlen
  -- j < 4, so j ∈ {0, 1, 2, 3}, and i < j
  interval_cases j
  · -- j = 0: impossible since i < j means i < 0
    omega
  · -- j = 1: i = 0
    interval_cases i
    · native_decide
  · -- j = 2: i ∈ {0, 1}
    interval_cases i
    · native_decide
    · native_decide
  · -- j = 3: i ∈ {0, 1, 2}
    interval_cases i
    · native_decide
    · native_decide
    · native_decide

theorem test1_postcondition :
  postcondition test1_xs test1_target test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 countLessThan
  unfold test1_xs test1_target test1_Expected
  simp only [List.length_cons, List.length_nil]
  constructor
  · -- ensures1: 2 ≤ 4
    omega
  constructor
  · -- ensures2: ∀ i < 2, i < 4 → xs[i]! < 5
    intro i hi1 hi2
    interval_cases i
    · native_decide
    · native_decide
  constructor
  · -- ensures3: ∀ i ≥ 2, i < 4 → xs[i]! ≥ 5
    intro i hi1 hi2
    interval_cases i
    · native_decide
    · native_decide
  · -- ensures4: 2 = countP (· < 5) [1, 3, 5, 6]
    native_decide

theorem test2_precondition :
  precondition test2_xs test2_target := by
  unfold precondition isStrictlyIncreasing test2_xs
  intro i j hij hjlen
  simp only [List.length] at hjlen
  interval_cases j
  · omega
  · interval_cases i
    native_decide
  · interval_cases i
    · native_decide
    · native_decide
  · interval_cases i
    · native_decide
    · native_decide
    · native_decide

theorem test2_postcondition :
  postcondition test2_xs test2_target test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4
  unfold test2_xs test2_target test2_Expected
  unfold countLessThan
  simp only [List.length_cons, List.length_nil]
  constructor
  · -- ensures1: 1 ≤ 4
    omega
  constructor
  · -- ensures2: ∀ i < 1, i < 4 → xs[i]! < 2
    intro i hi1 hi2
    interval_cases i
    native_decide
  constructor
  · -- ensures3: ∀ i ≥ 1, i < 4 → xs[i]! ≥ 2
    intro i hi1 hi2
    interval_cases i
    all_goals native_decide
  · -- ensures4: 1 = countP (· < 2) [1, 3, 5, 6]
    native_decide

theorem test5_precondition :
  precondition test5_xs test5_target := by
  unfold precondition isStrictlyIncreasing test5_xs
  intro i j _ hj
  simp only [List.length_nil] at hj
  exact absurd hj (Nat.not_lt_zero j)

theorem test5_postcondition :
  postcondition test5_xs test5_target test5_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4
  unfold test5_xs test5_target test5_Expected
  unfold countLessThan
  simp only [List.length_nil, List.countP_nil]
  constructor
  · omega
  constructor
  · intro i hi
    omega
  constructor
  · intro i _ hi
    omega
  · trivial

theorem uniqueness (xs : List Int) (target : Int):
  precondition xs target →
  (∀ ret1 ret2,
    postcondition xs target ret1 →
    postcondition xs target ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  unfold ensures4 at h1 h2
  have heq1 : ret1 = countLessThan xs target := h1.2.2.2
  have heq2 : ret2 = countLessThan xs target := h2.2.2.2
  rw [heq1, heq2]
end Proof
