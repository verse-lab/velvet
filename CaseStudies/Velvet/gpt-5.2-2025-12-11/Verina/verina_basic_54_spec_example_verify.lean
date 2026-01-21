import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!


def natAbsDiff (x : Int) (y : Int) : Nat :=
  Int.natAbs (x - y)

def isMinPairwiseAbsDiff (a : Array Int) (b : Array Int) (d : Nat) : Prop :=
  (∃ (i : Nat) (j : Nat), i < a.size ∧ j < b.size ∧ natAbsDiff a[i]! b[j]! = d) ∧
  (∀ (i : Nat) (j : Nat), i < a.size → j < b.size → d ≤ natAbsDiff a[i]! b[j]!)




def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧
  b.size > 0 ∧
  isSortedNondecreasing a ∧
  isSortedNondecreasing b




def postcondition (a : Array Int) (b : Array Int) (result : Nat) : Prop :=
  isMinPairwiseAbsDiff a b result


def test1_a : Array Int := #[1, 3, 5]

def test1_b : Array Int := #[2, 4, 6]

def test1_Expected : Nat := 1

def test4_a : Array Int := #[1, 2, 3, 4, 5]

def test4_b : Array Int := #[3]

def test4_Expected : Nat := 0

def test6_a : Array Int := #[-7]

def test6_b : Array Int := #[4]

def test6_Expected : Nat := 11







section Proof
theorem test1_precondition : precondition test1_a test1_b := by
  unfold precondition
  constructor
  · -- test1_a.size > 0
    simp [test1_a]
  constructor
  · -- test1_b.size > 0
    simp [test1_b]
  constructor
  · -- isSortedNondecreasing test1_a
    unfold isSortedNondecreasing
    intro i j hij hj
    have hj' : j < 3 := by simpa [test1_a] using hj
    have hij' : i < 3 := lt_trans hij hj'
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    have hj'' : j = 0 ∨ j = 1 ∨ j = 2 := by
      omega
    rcases hi with rfl | rfl | rfl <;> rcases hj'' with rfl | rfl | rfl
    · cases (Nat.lt_irrefl 0 hij)
    · simp [test1_a]
    · simp [test1_a]
    · have : ¬ (1 < 0) := by decide
      exact (False.elim (this hij))
    · cases (Nat.lt_irrefl 1 hij)
    · simp [test1_a]
    · have : ¬ (2 < 0) := by decide
      exact (False.elim (this hij))
    · have : ¬ (2 < 1) := by decide
      exact (False.elim (this hij))
    · cases (Nat.lt_irrefl 2 hij)
  · -- isSortedNondecreasing test1_b
    unfold isSortedNondecreasing
    intro i j hij hj
    have hj' : j < 3 := by simpa [test1_b] using hj
    have hij' : i < 3 := lt_trans hij hj'
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    have hj'' : j = 0 ∨ j = 1 ∨ j = 2 := by
      omega
    rcases hi with rfl | rfl | rfl <;> rcases hj'' with rfl | rfl | rfl
    · cases (Nat.lt_irrefl 0 hij)
    · simp [test1_b]
    · simp [test1_b]
    · have : ¬ (1 < 0) := by decide
      exact (False.elim (this hij))
    · cases (Nat.lt_irrefl 1 hij)
    · simp [test1_b]
    · have : ¬ (2 < 0) := by decide
      exact (False.elim (this hij))
    · have : ¬ (2 < 1) := by decide
      exact (False.elim (this hij))
    · cases (Nat.lt_irrefl 2 hij)

theorem test1_postcondition_0
    (i : ℕ)
    (hi : i < test1_a.size)
    : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hi' : i < 3 := by
    simpa [test1_a] using hi
  omega

theorem test1_postcondition_1
    (j : ℕ)
    (hj : j < test1_b.size)
    : j = 0 ∨ j = 1 ∨ j = 2 := by
    intros; expose_names; exact (test1_postcondition_0 j hj); done

theorem test1_postcondition : postcondition test1_a test1_b test1_Expected := by
  unfold postcondition
  unfold test1_Expected
  unfold isMinPairwiseAbsDiff
  apply And.intro
  · -- existence: exhibit i = 0, j = 0 with distance 1
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · have hA0 : (0 : Nat) < test1_a.size := by (try simp at *; expose_names); exact (Nat.zero_lt_succ [3, 5].length); done
      exact hA0
    · have hB0 : (0 : Nat) < test1_b.size := by (try simp at *; expose_names); exact (Nat.zero_lt_succ [4, 6].length); done
      exact hB0
    · have hvalA00 : test1_a[0]! = (1 : Int) := by (try simp at *; expose_names); exact rfl; done
      have hvalB00 : test1_b[0]! = (2 : Int) := by (try simp at *; expose_names); exact rfl; done
      have habs : natAbsDiff (1 : Int) (2 : Int) = 1 := by (try simp at *; expose_names); exact (rfl); done
      -- rewrite array values into the natAbsDiff goal and finish by computed abs
      simpa [natAbsDiff, hvalA00, hvalB00] using habs
  · -- minimality: for all i j in bounds, 1 ≤ natAbsDiff a[i] b[j]
    intro i j hi hj
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by (try simp at *; expose_names); exact (test1_postcondition_0 i hi); done
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by (try simp at *; expose_names); exact (test1_postcondition_1 j hj); done
    rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
    · -- (i,j)=(0,0): |1-2|=1
      have h : natAbsDiff test1_a[0]! test1_b[0]! = 1 := by (try simp at *; expose_names); exact (rfl); done
      simpa [h]
    · -- (0,1): |1-4|=3
      have h : natAbsDiff test1_a[0]! test1_b[1]! = 3 := by (try simp at *; expose_names); exact (rfl); done
      have hle : (1 : Nat) ≤ 3 := by (try simp at *; expose_names); exact hi; done
      exact hle.trans_eq (by simpa [h])
    · -- (0,2): |1-6|=5
      have h : natAbsDiff test1_a[0]! test1_b[2]! = 5 := by (try simp at *; expose_names); exact (rfl); done
      have hle : (1 : Nat) ≤ 5 := by (try simp at *; expose_names); exact NeZero.one_le; done
      exact hle.trans_eq (by simpa [h])
    · -- (1,0): |3-2|=1
      have h : natAbsDiff test1_a[1]! test1_b[0]! = 1 := by (try simp at *; expose_names); exact (rfl); done
      simpa [h]
    · -- (1,1): |3-4|=1
      have h : natAbsDiff test1_a[1]! test1_b[1]! = 1 := by (try simp at *; expose_names); exact (rfl); done
      simpa [h]
    · -- (1,2): |3-6|=3
      have h : natAbsDiff test1_a[1]! test1_b[2]! = 3 := by (try simp at *; expose_names); exact (rfl); done
      have hle : (1 : Nat) ≤ 3 := by (try simp at *; expose_names); exact Nat.one_le_of_lt hi; done
      exact hle.trans_eq (by simpa [h])
    · -- (2,0): |5-2|=3
      have h : natAbsDiff test1_a[2]! test1_b[0]! = 3 := by (try simp at *; expose_names); exact (rfl); done
      have hle : (1 : Nat) ≤ 3 := by (try simp at *; expose_names); exact hj; done
      exact hle.trans_eq (by simpa [h])
    · -- (2,1): |5-4|=1
      have h : natAbsDiff test1_a[2]! test1_b[1]! = 1 := by (try simp at *; expose_names); exact (rfl); done
      simpa [h]
    · -- (2,2): |5-6|=1
      have h : natAbsDiff test1_a[2]! test1_b[2]! = 1 := by (try simp at *; expose_names); exact (rfl); done
      simpa [h]

theorem test4_precondition : precondition test4_a test4_b := by
  unfold precondition
  constructor
  · -- test4_a.size > 0
    decide
  constructor
  · -- test4_b.size > 0
    decide
  constructor
  · -- isSortedNondecreasing test4_a
    unfold isSortedNondecreasing
    intro i j hij hj
    have hj' : j < 5 := by simpa [test4_a] using hj
    have hij' : i < 5 := Nat.lt_trans hij hj'
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      omega
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
      rcases hjcases with rfl | rfl | rfl | rfl | rfl <;>
      simp [test4_a] at hij ⊢
  · -- isSortedNondecreasing test4_b
    unfold isSortedNondecreasing
    intro i j hij hj
    have : False := by
      have hj' : j < 1 := by simpa [test4_b] using hj
      omega
    exact False.elim this

theorem test4_postcondition : postcondition test4_a test4_b test4_Expected := by
  unfold postcondition
  unfold isMinPairwiseAbsDiff
  constructor
  · refine ⟨2, 0, ?_, ?_, ?_⟩
    · simp [test4_a]
    · simp [test4_b]
    · simp [natAbsDiff, test4_a, test4_b, test4_Expected]
  · intro i j hi hj
    simpa [test4_Expected] using (Nat.zero_le (natAbsDiff test4_a[i]! test4_b[j]!))

theorem test6_precondition : precondition test6_a test6_b := by
  unfold precondition
  constructor
  · -- test6_a.size > 0
    simp [test6_a]
  constructor
  · -- test6_b.size > 0
    simp [test6_b]
  constructor
  · -- isSortedNondecreasing test6_a
    unfold isSortedNondecreasing
    intro i j hij hj
    have : j = 0 := by
      -- j < 1 since test6_a.size = 1
      simpa [test6_a] using (Nat.lt_one_iff.mp (by simpa [test6_a] using hj))
    subst this
    exact (Nat.not_lt_zero i hij).elim
  · -- isSortedNondecreasing test6_b
    unfold isSortedNondecreasing
    intro i j hij hj
    have : j = 0 := by
      simpa [test6_b] using (Nat.lt_one_iff.mp (by simpa [test6_b] using hj))
    subst this
    exact (Nat.not_lt_zero i hij).elim

theorem test6_postcondition : postcondition test6_a test6_b test6_Expected := by
  -- `simp` can close the goal entirely for this singleton/singleton case.
  simp [postcondition, isMinPairwiseAbsDiff, natAbsDiff, test6_a, test6_b, test6_Expected]

theorem uniqueness
    (a : Array Int)
    (b : Array Int)
    : precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hp
  intro ret1 ret2 hpost1 hpost2
  -- unfold postcondition/isMinPairwiseAbsDiff and extract existence/minimality parts
  rcases hpost1 with ⟨hex1, hmin1⟩
  rcases hpost2 with ⟨hex2, hmin2⟩
  -- ret1 ≤ ret2 using minimality of ret1 and existence witness for ret2
  have h₁₂ : ret1 ≤ ret2 := by
    rcases hex2 with ⟨i2, j2, hi2, hj2, hEq2⟩
    have : ret1 ≤ natAbsDiff a[i2]! b[j2]! := hmin1 i2 j2 hi2 hj2
    simpa [hEq2] using this
  -- ret2 ≤ ret1 using minimality of ret2 and existence witness for ret1
  have h₂₁ : ret2 ≤ ret1 := by
    rcases hex1 with ⟨i1, j1, hi1, hj1, hEq1⟩
    have : ret2 ≤ natAbsDiff a[i1]! b[j1]! := hmin2 i1 j1 hi1 hj1
    simpa [hEq1] using this
  exact Nat.le_antisymm h₁₂ h₂₁
end Proof
