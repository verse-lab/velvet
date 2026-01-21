import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def FoundIndex (a : Array Int) (key : Int) (result : Int) : Prop :=
  0 ≤ result ∧
  (Int.toNat result) < a.size ∧
  a[(Int.toNat result)]! = key ∧
  ∀ (j : Int), 0 ≤ j ∧ j < result → a[(Int.toNat j)]! ≠ key

def KeyAbsent (a : Array Int) (key : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≠ key



def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  (result = -1 ∧ KeyAbsent a key) ∨
  (result ≠ -1 ∧ FoundIndex a key result)


def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_key : Int := 3

def test1_Expected : Int := 2

def test5_a : Array Int := #[0, -3, -1, -3]

def test5_key : Int := (-3)

def test5_Expected : Int := 1

def test9_a : Array Int := #[7, 7, 7]

def test9_key : Int := 7

def test9_Expected : Int := 0







section Proof
theorem test1_precondition : precondition test1_a test1_key := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (j : ℤ)
    (hj : 0 ≤ j ∧ j < 2)
    (h_ne : True)
    (h0 : True)
    (hsize : True)
    (hget : True)
    : j = 0 ∨ j = 1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition : postcondition test1_a test1_key test1_Expected := by
  -- Step 1-2: unfold/simplify constants and the postcondition shape
  dsimp [postcondition, test1_a, test1_key, test1_Expected]
  -- Goal is now: (2 = -1 ∧ KeyAbsent #[1,2,3,4,5] 3) ∨ (2 ≠ -1 ∧ FoundIndex #[1,2,3,4,5] 3 2)

  -- Step 3: choose the right disjunct (since 2 ≠ -1)
  apply Or.inr

  -- Step 4: prove the first conjunct of the right disjunct
  have h_ne : (2 : Int) ≠ (-1 : Int) := by
    (try simp at *; expose_names); exact not_eq_of_beq_eq_false rfl; done

  -- Step 5: reduce FoundIndex to its four conjuncts
  have h_found : FoundIndex (#[1, 2, 3, 4, 5] : Array Int) (3 : Int) (2 : Int) := by
    -- Step 6: 0 ≤ result
    have h0 : (0 : Int) ≤ (2 : Int) := by
      (try simp at *; expose_names); exact Int.zero_le_ofNat 2; done
    -- Step 7: (Int.toNat result) < a.size
    have hsize : (Int.toNat (2 : Int)) < (#[1, 2, 3, 4, 5] : Array Int).size := by
      (try simp at *; expose_names); exact (Int.toNat_lt h0).mpr h0; done
    -- Step 8: a[Int.toNat result]! = key
    have hget : (#[1, 2, 3, 4, 5] : Array Int)[(Int.toNat (2 : Int))]! = (3 : Int) := by
      (try simp at *; expose_names); exact rfl; done
    -- Step 9-13: minimality for all j with 0 ≤ j ∧ j < 2
    have hmin : ∀ (j : Int), 0 ≤ j ∧ j < (2 : Int) → (#[1, 2, 3, 4, 5] : Array Int)[(Int.toNat j)]! ≠ (3 : Int) := by
      intro j hj
      -- Step 10-13: only j = 0 or j = 1 are possible; split by cases
      have hj_cases : j = 0 ∨ j = 1 := by
        (try simp at *; expose_names); exact (test1_postcondition_0 j hj h_ne h0 hsize hget); done
      cases hj_cases with
      | inl hj0 =>
        -- Step 11: j = 0 case
        have hneq0 : (#[1, 2, 3, 4, 5] : Array Int)[(Int.toNat (0 : Int))]! ≠ (3 : Int) := by
          (try simp at *; expose_names); exact not_eq_of_beq_eq_false rfl; done
        simpa [hj0] using hneq0
      | inr hj1 =>
        -- Step 12: j = 1 case
        have hneq1 : (#[1, 2, 3, 4, 5] : Array Int)[(Int.toNat (1 : Int))]! ≠ (3 : Int) := by
          (try simp at *; expose_names); exact not_eq_of_beq_eq_false rfl; done
        simpa [hj1] using hneq1
    -- Step 14: assemble FoundIndex
    exact And.intro h0 (And.intro hsize (And.intro hget hmin))

  -- Step 15-16: assemble the right disjunct and finish
  exact And.intro h_ne h_found

theorem test5_precondition : precondition test5_a test5_key := by
    intros; expose_names; exact (trivial); done

theorem test5_postcondition_0
    (j : ℤ)
    (hj : 0 ≤ j ∧ j < 1)
    (h_ne : True)
    (h0 : True)
    (hsize : True)
    (hget : True)
    : j = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition : postcondition test5_a test5_key test5_Expected := by
  -- Step 1-2: unfold/simplify constants and the postcondition shape
  dsimp [postcondition, test5_a, test5_key, test5_Expected]
  -- Goal:
  --   (1 = -1 ∧ KeyAbsent #[0,-3,-1,-3] (-3)) ∨ (1 ≠ -1 ∧ FoundIndex #[0,-3,-1,-3] (-3) 1)

  -- Step 3: choose the right disjunct (since 1 ≠ -1)
  apply Or.inr

  -- Step 4: prove the first conjunct of the right disjunct
  have h_ne : (1 : Int) ≠ (-1 : Int) := by
    (try simp at *; expose_names); exact not_eq_of_beq_eq_false rfl; done

  -- Step 5-11: prove FoundIndex by proving its four conjuncts
  have h_found : FoundIndex (#[0, -3, -1, -3] : Array Int) (-3 : Int) (1 : Int) := by
    -- Step 6: 0 ≤ result
    have h0 : (0 : Int) ≤ (1 : Int) := by
      (try simp at *; expose_names); exact Int.one_nonneg; done
    -- Step 7: (Int.toNat result) < a.size
    have hsize : (Int.toNat (1 : Int)) < (#[0, -3, -1, -3] : Array Int).size := by
      (try simp at *; expose_names); exact Nat.lt_of_sub_eq_succ rfl; done
    -- Step 8: a[Int.toNat result]! = key
    have hget : (#[0, -3, -1, -3] : Array Int)[(Int.toNat (1 : Int))]! = (-3 : Int) := by
      (try simp at *; expose_names); exact rfl; done
    -- Step 9-10: minimality: any j with 0 ≤ j ∧ j < 1 must not hit key
    have hmin : ∀ (j : Int), 0 ≤ j ∧ j < (1 : Int) → (#[0, -3, -1, -3] : Array Int)[(Int.toNat j)]! ≠ (-3 : Int) := by
      intro j hj
      -- Step 9: show j must be 0
      have hj0 : j = 0 := by
        (try simp at *; expose_names); exact (test5_postcondition_0 j hj h_ne h0 hsize hget); done
      -- Step 10: check index 0 is 0, hence not -3
      have hneq0 : (#[0, -3, -1, -3] : Array Int)[(Int.toNat (0 : Int))]! ≠ (-3 : Int) := by
        (try simp at *; expose_names); exact not_eq_of_beq_eq_false rfl; done
      simpa [hj0] using hneq0
    -- Step 11: assemble FoundIndex
    exact And.intro h0 (And.intro hsize (And.intro hget hmin))

  -- Step 12-13: assemble the right disjunct and finish
  exact And.intro h_ne h_found

theorem test9_precondition : precondition test9_a test9_key := by
    intros; expose_names; exact (trivial); done

theorem test9_postcondition : postcondition test9_a test9_key test9_Expected := by
  -- unfold constants and choose the right disjunct
  unfold postcondition test9_a test9_key test9_Expected
  right
  constructor
  · simp
  · -- prove FoundIndex #[7,7,7] 7 0
    unfold FoundIndex
    constructor
    · simp
    constructor
    · simp
    constructor
    · simp
    · intro j hj
      have hjlt : j < 0 := hj.2
      have hjge : 0 ≤ j := hj.1
      have : False := by
        have : ¬ (0 ≤ j) := by simpa using (Int.not_le_of_gt hjlt)
        exact this hjge
      exact False.elim this

theorem uniqueness
    (a : Array Int)
    (key : Int)
    : precondition a key →
  (∀ ret1 ret2,
    postcondition a key ret1 →
    postcondition a key ret2 →
    ret1 = ret2) := by
  intro _hp
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  cases h1 with
  | inl h1m1 =>
    rcases h1m1 with ⟨hret1, hAbs⟩
    cases h2 with
    | inl h2m1 =>
      rcases h2m1 with ⟨hret2, _hAbs2⟩
      simp [hret1, hret2]
    | inr h2fi =>
      rcases h2fi with ⟨hret2ne, hFound2⟩
      rcases hFound2 with ⟨h0, hlt, hget, _hmin⟩
      have hne : a[(Int.toNat ret2)]! ≠ key := hAbs (Int.toNat ret2) hlt
      exact (hne hget).elim
  | inr h1fi =>
    rcases h1fi with ⟨hret1ne, hFound1⟩
    cases h2 with
    | inl h2m1 =>
      rcases h2m1 with ⟨hret2, hAbs⟩
      rcases hFound1 with ⟨h0, hlt, hget, _hmin⟩
      have hne : a[(Int.toNat ret1)]! ≠ key := hAbs (Int.toNat ret1) hlt
      exact (hne hget).elim
    | inr h2fi =>
      rcases h2fi with ⟨_hret2ne, hFound2⟩
      rcases hFound1 with ⟨h01, hlt1, hget1, hmin1⟩
      rcases hFound2 with ⟨h02, hlt2, hget2, hmin2⟩
      have hle12 : ret1 ≤ ret2 := by
        have : ¬ (ret2 < ret1) := by
          intro hlt21
          have hne : a[(Int.toNat ret2)]! ≠ key := hmin1 ret2 ⟨h02, hlt21⟩
          exact (hne hget2).elim
        exact Lean.Omega.Int.le_of_not_lt this
      have hle21 : ret2 ≤ ret1 := by
        have : ¬ (ret1 < ret2) := by
          intro hlt12
          have hne : a[(Int.toNat ret1)]! ≠ key := hmin2 ret1 ⟨h01, hlt12⟩
          exact (hne hget1).elim
        exact Lean.Omega.Int.le_of_not_lt this
      exact Int.le_antisymm hle12 hle21
end Proof
