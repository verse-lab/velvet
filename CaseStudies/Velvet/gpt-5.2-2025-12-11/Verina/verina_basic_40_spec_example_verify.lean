import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def InArray (s : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < s.size ∧ s[i]! = x


def IsMinVal (s : Array Int) (m : Int) : Prop :=
  InArray s m ∧ ∀ i : Nat, i < s.size → m ≤ s[i]!


def IsSecondAboveMin (s : Array Int) (m : Int) (x : Int) : Prop :=
  InArray s x ∧ m < x ∧
    (∀ y : Int, InArray s y → m < y → x ≤ y)






def precondition (s : Array Int) : Prop :=
  s.size ≥ 2 ∧
  (∃ i : Nat, ∃ j : Nat,
    i < s.size ∧ j < s.size ∧ i ≠ j ∧ s[i]! ≠ s[j]!)




def postcondition (s : Array Int) (result : Int) : Prop :=
  ∃ m : Int, IsMinVal s m ∧ IsSecondAboveMin s m result


def test1_s : Array Int := #[5, 3, 1, 4, 2]

def test1_Expected : Int := 2

def test6_s : Array Int := #[1, 1, 2, 2, 3]

def test6_Expected : Int := 2

def test7_s : Array Int := #[-5, -1, -3, 0]

def test7_Expected : Int := -3







section Proof
theorem test1_precondition :
  precondition test1_s := by
  unfold precondition test1_s
  constructor
  · decide
  · refine ⟨0, 1, ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · simp

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  -- unfold the concrete goal
  dsimp [postcondition, test1_s, test1_Expected]
  -- choose m = 1 (the minimum)
  refine ⟨(1 : Int), ?_, ?_⟩
  · -- IsMinVal #[5,3,1,4,2] 1
    dsimp [IsMinVal]
    constructor
    · -- InArray ... 1 (at index 2)
      dsimp [InArray]
      refine ⟨2, ?_, ?_⟩
      · decide
      · simp
    · -- ∀ i < size, 1 ≤ s[i]!
      intro i hi
      have hi' : i < 5 := by
        simpa using hi
      have hle : i ≤ 4 := Nat.le_of_lt_succ hi'
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> simp
  · -- IsSecondAboveMin #[5,3,1,4,2] 1 2
    dsimp [IsSecondAboveMin]
    refine And.intro ?_ (And.intro ?_ ?_)
    · -- InArray ... 2 (at index 4)
      dsimp [InArray]
      refine ⟨4, ?_, ?_⟩
      · decide
      · simp
    · -- 1 < 2
      decide
    · -- minimality: any y in array with 1 < y satisfies 2 ≤ y
      intro y hy hym
      rcases hy with ⟨i, hi, hiy⟩
      have hi' : i < 5 := by
        simpa [test1_s] using hi
      have hle : i ≤ 4 := Nat.le_of_lt_succ hi'
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · -- i = 0, y = 5
        have hy' : y = (5 : Int) := by
          -- hiy : s[0]! = y, but simp gives s[0]! = 5
          exact (Eq.symm (by simpa [test1_s] using hiy))
        subst hy'
        decide
      · -- i = 1, y = 3
        have hy' : y = (3 : Int) := by
          exact (Eq.symm (by simpa [test1_s] using hiy))
        subst hy'
        decide
      · -- i = 2, y = 1 contradicts 1 < y
        have hy' : y = (1 : Int) := by
          exact (Eq.symm (by simpa [test1_s] using hiy))
        subst hy'
        have : ¬ ((1 : Int) < 1) := by decide
        exact (this hym).elim
      · -- i = 3, y = 4
        have hy' : y = (4 : Int) := by
          exact (Eq.symm (by simpa [test1_s] using hiy))
        subst hy'
        decide
      · -- i = 4, y = 2
        have hy' : y = (2 : Int) := by
          exact (Eq.symm (by simpa [test1_s] using hiy))
        subst hy'
        decide

theorem test6_precondition :
  precondition test6_s := by
  unfold precondition test6_s
  constructor
  · simp
  · refine ⟨0, 2, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · decide
    · simp

theorem test6_postcondition :
  postcondition test6_s test6_Expected := by
  -- exhibit m = 1
  unfold postcondition
  refine ⟨(1 : Int), ?_, ?_⟩
  · -- IsMinVal test6_s 1
    unfold IsMinVal
    constructor
    · -- InArray test6_s 1 (index 0)
      unfold InArray
      refine ⟨0, ?_, ?_⟩ <;> simp [test6_s]
    · -- 1 ≤ s[i]! for all i in bounds
      intro i hi
      have hi' : i < 5 := by simpa [test6_s] using hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        omega
      rcases hcases with rfl | hcases
      · simp [test6_s]
      rcases hcases with rfl | hcases
      · simp [test6_s]
      rcases hcases with rfl | hcases
      · simp [test6_s]
      rcases hcases with rfl | hcases
      · simp [test6_s]
      · rcases hcases with rfl
        simp [test6_s]
  · -- IsSecondAboveMin test6_s 1 test6_Expected (=2)
    unfold IsSecondAboveMin
    constructor
    · -- InArray test6_s 2 (index 2)
      unfold InArray
      refine ⟨2, ?_, ?_⟩ <;> simp [test6_s, test6_Expected]
    · constructor
      · -- 1 < 2
        simp [test6_Expected]
      · -- minimality: any y in array with 1 < y satisfies 2 ≤ y
        intro y hy hmy
        rcases hy with ⟨i, hi, hget⟩
        have hi' : i < 5 := by simpa [test6_s] using hi
        have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
          omega
        rcases hcases with rfl | hcases
        · -- i=0 -> y = 1, contradiction with 1 < y
          have hy1' : (1 : Int) = y := by simpa [test6_s] using hget
          have hy1 : y = (1 : Int) := hy1'.symm
          exfalso
          simpa [hy1] using hmy
        rcases hcases with rfl | hcases
        · -- i=1 -> y = 1, contradiction
          have hy1' : (1 : Int) = y := by simpa [test6_s] using hget
          have hy1 : y = (1 : Int) := hy1'.symm
          exfalso
          simpa [hy1] using hmy
        rcases hcases with rfl | hcases
        · -- i=2 -> y = 2
          have hy2' : (2 : Int) = y := by simpa [test6_s] using hget
          have hy2 : y = (2 : Int) := hy2'.symm
          simp [test6_Expected, hy2]
        rcases hcases with rfl | hcases
        · -- i=3 -> y = 2
          have hy2' : (2 : Int) = y := by simpa [test6_s] using hget
          have hy2 : y = (2 : Int) := hy2'.symm
          simp [test6_Expected, hy2]
        · -- i=4 -> y = 3
          rcases hcases with rfl
          have hy3' : (3 : Int) = y := by simpa [test6_s] using hget
          have hy3 : y = (3 : Int) := hy3'.symm
          simp [test6_Expected, hy3]

theorem test7_precondition :
  precondition test7_s := by
  unfold precondition
  constructor
  · -- size ≥ 2
    simp [test7_s]
  · -- two distinct indices with different values
    refine ⟨0, 1, ?_, ?_, ?_, ?_⟩
    · simp [test7_s]
    · simp [test7_s]
    · decide
    · simp [test7_s]

theorem test7_postcondition :
  postcondition test7_s test7_Expected := by
  -- choose the minimum m = -5
  refine ⟨(-5 : Int), ?_, ?_⟩
  · -- IsMinVal test7_s (-5)
    constructor
    · -- InArray test7_s (-5)
      refine ⟨0, ?_, ?_⟩ <;> simp [InArray, test7_s]
    · -- ∀ i, i < size → -5 ≤ s[i]!
      intro i hi
      have hi' : i < 4 := by simpa [test7_s] using hi
      -- enumerate i < 4
      match i with
      | 0 =>
          simp [test7_s]
      | Nat.succ i =>
          have hi3 : i < 3 := Nat.lt_of_succ_lt_succ hi'
          match i with
          | 0 =>
              simp [test7_s]
          | Nat.succ i =>
              have hi2 : i < 2 := Nat.lt_of_succ_lt_succ hi3
              match i with
              | 0 =>
                  simp [test7_s]
              | Nat.succ i =>
                  have hi1 : i < 1 := Nat.lt_of_succ_lt_succ hi2
                  have : i = 0 := Nat.lt_one_iff.mp hi1
                  subst this
                  simp [test7_s]
  · -- IsSecondAboveMin test7_s (-5) (-3)
    -- unfold expected value so we don't get stuck with test7_Expected
    change IsSecondAboveMin test7_s (-5 : Int) (-3 : Int)
    constructor
    · -- InArray test7_s (-3)
      refine ⟨2, ?_, ?_⟩ <;> simp [InArray, test7_s]
    · constructor
      · -- -5 < -3
        decide
      · -- ∀ y, InArray s y → -5 < y → -3 ≤ y
        intro y hy hmin
        rcases hy with ⟨i, hi, hget⟩
        have hi' : i < 4 := by simpa [test7_s] using hi
        -- enumerate i < 4, rewrite y, and finish by arithmetic/contradiction
        match i with
        | 0 =>
            have : y = (-5 : Int) := by simpa [test7_s] using hget.symm
            subst this
            exact (lt_irrefl (-5 : Int) hmin).elim
        | Nat.succ i =>
            have hi3 : i < 3 := Nat.lt_of_succ_lt_succ hi'
            match i with
            | 0 =>
                have : y = (-1 : Int) := by simpa [test7_s] using hget.symm
                subst this
                decide
            | Nat.succ i =>
                have hi2 : i < 2 := Nat.lt_of_succ_lt_succ hi3
                match i with
                | 0 =>
                    have : y = (-3 : Int) := by simpa [test7_s] using hget.symm
                    subst this
                    decide
                | Nat.succ i =>
                    have hi1 : i < 1 := Nat.lt_of_succ_lt_succ hi2
                    have : i = 0 := Nat.lt_one_iff.mp hi1
                    subst this
                    have : y = (0 : Int) := by simpa [test7_s] using hget.symm
                    subst this
                    decide

theorem uniqueness (s : Array Int):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨m1, hmin1, hsec1⟩
  rcases hpost2 with ⟨m2, hmin2, hsec2⟩

  -- Show the minimum is unique: m1 = m2
  have hm2_le_m1 : m2 ≤ m1 := by
    rcases hmin1.1 with ⟨i, hi, him⟩
    have : m2 ≤ s[i]! := hmin2.2 i hi
    simpa [him] using this
  have hm1_le_m2 : m1 ≤ m2 := by
    rcases hmin2.1 with ⟨i, hi, him⟩
    have : m1 ≤ s[i]! := hmin1.2 i hi
    simpa [him] using this
  have hm : m1 = m2 := Int.le_antisymm hm1_le_m2 hm2_le_m1

  -- Rewrite second-above-min properties to use the same minimum
  have hsec1' : IsSecondAboveMin s m2 ret1 := by simpa [hm] using hsec1
  have hsec2' : IsSecondAboveMin s m2 ret2 := by simpa using hsec2

  -- Use minimality clauses both ways
  have hret1_le_ret2 : ret1 ≤ ret2 :=
    (hsec1'.2.2) ret2 hsec2'.1 hsec2'.2.1
  have hret2_le_ret1 : ret2 ≤ ret1 :=
    (hsec2'.2.2) ret1 hsec1'.1 hsec1'.2.1

  exact Int.le_antisymm hret1_le_ret2 hret2_le_ret1
end Proof
