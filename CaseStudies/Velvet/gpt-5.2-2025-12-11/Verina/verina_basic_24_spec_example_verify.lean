import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def IsFirstIdx (a : Array Int) (p : Int → Prop) (i : Nat) : Prop :=
  i < a.size ∧ p (a[i]!) ∧ ∀ k : Nat, k < i → ¬ p (a[k]!)



def precondition (a : Array Int) : Prop :=
  (∃ i : Nat, i < a.size ∧ Even (a[i]!)) ∧
  (∃ j : Nat, j < a.size ∧ Odd (a[j]!))

def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ i : Nat, ∃ j : Nat,
    IsFirstIdx a (fun x => Even x) i ∧
    IsFirstIdx a (fun x => Odd x) j ∧
    result = a[i]! - a[j]!


def test1_a : Array Int := #[2, 3, 4, 5]

def test1_Expected : Int := -1

def test2_a : Array Int := #[1, 4, 6, 8]

def test2_Expected : Int := 3

def test6_a : Array Int := #[0, -3, 2, 5]

def test6_Expected : Int := 3







section Proof
theorem test1_precondition : precondition test1_a := by
  unfold precondition test1_a
  constructor
  · refine ⟨0, ?_, ?_⟩
    · decide
    · decide
  · refine ⟨1, ?_, ?_⟩
    · decide
    · decide

theorem test1_postcondition : postcondition test1_a test1_Expected := by
  unfold postcondition
  refine ⟨0, 1, ?_, ?_, ?_⟩
  · -- first even at index 0
    unfold IsFirstIdx
    refine ⟨?_, ?_, ?_⟩
    · simp [test1_a]
    · -- Even 2
      native_decide
    · intro k hk
      exact (Nat.not_lt_zero k hk).elim
  · -- first odd at index 1
    unfold IsFirstIdx
    refine ⟨?_, ?_, ?_⟩
    · simp [test1_a]
    · -- Odd 3
      native_decide
    · intro k hk
      have hk' : k = 0 := by
        simpa using (Nat.lt_succ_iff.mp hk)
      subst hk'
      -- ¬ Odd 2
      native_decide
  · simp [test1_Expected, test1_a]

theorem test2_precondition : precondition test2_a := by
  unfold precondition
  constructor
  · refine ⟨1, ?_, ?_⟩
    · simp [test2_a]
    · -- `simp` reduces the array lookup to `4`, then `decide` closes `Even 4`
      simpa [test2_a] using (by decide : Even (4 : Int))
  · refine ⟨0, ?_, ?_⟩
    · simp [test2_a]
    · simpa [test2_a] using (by decide : Odd (1 : Int))

theorem test2_postcondition : postcondition test2_a test2_Expected := by
  unfold postcondition
  refine ⟨1, 0, ?_, ?_, ?_⟩
  · -- first even index is 1
    unfold IsFirstIdx
    constructor
    · simp [test2_a]
    constructor
    · simp [test2_a, Int.even_iff]
    · intro k hk
      have hk' : k = 0 := (Nat.lt_one_iff.mp hk)
      subst hk'
      simp [test2_a, Int.even_iff]
  · -- first odd index is 0
    unfold IsFirstIdx
    constructor
    · simp [test2_a]
    constructor
    · simp [test2_a, Int.odd_iff]
    · intro k hk
      exact (Nat.not_lt_zero k hk).elim
  · -- result is a[1] - a[0]
    simp [test2_a, test2_Expected]

theorem test6_precondition : precondition test6_a := by
  unfold precondition
  constructor
  · refine ⟨0, ?_, ?_⟩
    · simp [test6_a]
    · simp [test6_a]
  · refine ⟨1, ?_, ?_⟩
    · simp [test6_a]
    · -- `simp [test6_a]` reduces `test6_a[1]!` to `-3`, then `simp` can rewrite `Odd (-3)` to `Odd 3`
      -- so we finish by `decide`.
      have : Odd (-3 : Int) := by decide
      simpa [test6_a] using this

theorem test6_postcondition : postcondition test6_a test6_Expected := by
  unfold postcondition
  refine ⟨0, 1, ?_, ?_, ?_⟩
  · -- first even index is 0
    unfold IsFirstIdx
    refine ⟨?_, ?_, ?_⟩
    · simp [test6_a]
    · simp [test6_a]
    · intro k hk
      exact (Nat.not_lt_zero k hk).elim
  · -- first odd index is 1
    unfold IsFirstIdx
    refine ⟨?_, ?_, ?_⟩
    · simp [test6_a]
    · -- a[1] = -3 is odd
      simpa [test6_a] using (by decide : Odd (-3 : Int))
    · intro k hk
      have hk0 : k = 0 := by
        have hk' : k ≤ 0 := Nat.le_of_lt_succ hk
        exact Nat.le_antisymm hk' (Nat.zero_le k)
      subst hk0
      simp [test6_a]
  · -- compute result
    simp [test6_Expected, test6_a]

theorem uniqueness
    (a : Array Int)
    : precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨i1, j1, hEven1, hOdd1, hret1⟩
  rcases hpost2 with ⟨i2, j2, hEven2, hOdd2, hret2⟩

  have hi : i1 = i2 := by
    rcases hEven1 with ⟨_hi1_lt, hi1_even, hi1_min⟩
    rcases hEven2 with ⟨_hi2_lt, hi2_even, hi2_min⟩
    have hni1lt : ¬ i1 < i2 := by
      intro hlt
      have : ¬ Even (a[i1]!) := hi2_min i1 hlt
      exact this hi1_even
    have hni2lt : ¬ i2 < i1 := by
      intro hlt
      have : ¬ Even (a[i2]!) := hi1_min i2 hlt
      exact this hi2_even
    exact (Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt i1 i2 hni1lt hni2lt)

  have hj : j1 = j2 := by
    rcases hOdd1 with ⟨_hj1_lt, hj1_odd, hj1_min⟩
    rcases hOdd2 with ⟨_hj2_lt, hj2_odd, hj2_min⟩
    have hnj1lt : ¬ j1 < j2 := by
      intro hlt
      have : ¬ Odd (a[j1]!) := hj2_min j1 hlt
      exact this hj1_odd
    have hnj2lt : ¬ j2 < j1 := by
      intro hlt
      have : ¬ Odd (a[j2]!) := hj1_min j2 hlt
      exact this hj2_odd
    exact (Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt j1 j2 hnj1lt hnj2lt)

  -- rewrite both results to the same indices
  subst hi
  subst hj
  simpa [hret1, hret2]
end Proof
