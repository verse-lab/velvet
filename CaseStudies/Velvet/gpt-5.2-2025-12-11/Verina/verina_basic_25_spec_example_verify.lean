import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def gaussSumNat (n : Nat) : Nat :=
  n * (n + 1) / 2



def precondition (n : Nat) : Prop :=
  True








def postcondition (n : Nat) (result : Int × Float) : Prop :=
  result.1 = Int.ofNat (gaussSumNat n) ∧
  (n = 0 → result.2 = 0.0) ∧
  (n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n))


def test1_n : Nat := 5

def test1_Expected : Int × Float := (15, 3.0)

def test4_n : Nat := 0

def test4_Expected : Int × Float := (0, 0.0)

def test5_n : Nat := 2

def test5_Expected : Int × Float := (3, 1.5)







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  -- unfold concrete values and the postcondition, then split the conjunctions
  unfold postcondition test4_n test4_Expected
  constructor
  · -- result.1 = Int.ofNat (gaussSumNat 0)
    simp [gaussSumNat]
  constructor
  · -- 0 = 0 → 0.0 = 0.0
    intro _
    rfl
  · -- 0 > 0 → ...
    intro h
    exfalso
    exact Nat.lt_irrefl 0 h

theorem test5_precondition :
  precondition test5_n := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition_0
    (h2pos : True)
    : 1.5 = Float.ofInt 3 / Float.ofNat 2 := by
    sorry

theorem test5_postcondition :
  postcondition test5_n test5_Expected := by
  -- Step 1-3: unfold the concrete inputs/expected output and the postcondition
  unfold test5_n test5_Expected postcondition

  -- Goal is a conjunction of three statements; split them
  constructor
  · -- Conjunct 1: (3, 1.5).1 = Int.ofNat (gaussSumNat 2)
    have hGauss : gaussSumNat 2 = 3 := by
      -- gaussSumNat 2 = 2 * (2 + 1) / 2 = 3
      -- can be done by simp/norm_num with [gaussSumNat]
      (try simp at *; expose_names); exact rfl; done
    have hInt : Int.ofNat (gaussSumNat 2) = (3 : Int) := by
      -- rewrite by hGauss
      simpa [hGauss]
    -- simplify fst of the pair and close
    simpa [hInt]

  constructor
  · -- Conjunct 2: 2 = 0 → (3, 1.5).2 = 0.0
    intro h20
    have hFalse : False := by
      -- 2 ≠ 0, contradiction
      have hne : (2 : Nat) ≠ 0 := by
        -- a simple `decide`/`simp` proof works
        (try simp at *; expose_names); exact Ne.symm (Nat.zero_ne_add_one 1); done
      exact (hne h20).elim
    exact False.elim hFalse

  · -- Conjunct 3: 2 > 0 → (3, 1.5).2 = Float.ofInt (3, 1.5).1 / Float.ofNat 2
    intro h2pos
    have hFloatEq : (1.5 : Float) = (Float.ofInt (3 : Int)) / (Float.ofNat 2) := by
      -- compute the concrete Float expression
      -- (may be doable with `native_decide`/`decide`/`simp` depending on simp support)
      (try simp at *; expose_names); exact (test5_postcondition_0 h2pos); done
    -- simplify projections to match hFloatEq
    simpa using hFloatEq

theorem uniqueness (n : Nat) :
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hn
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨h1fst, h1n0, h1npos⟩
  rcases hpost2 with ⟨h2fst, h2n0, h2npos⟩
  have hfst : ret1.1 = ret2.1 := by
    -- both are equal to Int.ofNat (gaussSumNat n)
    exact Eq.trans h1fst (Eq.symm h2fst)
  have hsnd : ret1.2 = ret2.2 := by
    cases Nat.eq_zero_or_pos n with
    | inl hn0 =>
        have : ret1.2 = 0.0 := h1n0 hn0
        have : ret2.2 = 0.0 := h2n0 hn0
        simpa [this] using (Eq.trans (h1n0 hn0) (Eq.symm (h2n0 hn0)))
    | inr hnpos =>
        -- use the >0 branch and the fact that fst components are equal
        have hret1 : ret1.2 = Float.ofInt ret1.1 / Float.ofNat n := h1npos hnpos
        have hret2 : ret2.2 = Float.ofInt ret2.1 / Float.ofNat n := h2npos hnpos
        -- rewrite ret2.1 to ret1.1 in hret2 and chain
        have hret2' : ret2.2 = Float.ofInt ret1.1 / Float.ofNat n := by
          simpa [hfst] using hret2
        exact Eq.trans hret1 (Eq.symm hret2')
  -- conclude pair equality from component equalities
  cases ret1 with
  | mk a1 b1 =>
    cases ret2 with
    | mk a2 b2 =>
      -- rewrite goals in terms of components
      simp at hfst hsnd
      simp [hfst, hsnd]
end Proof
