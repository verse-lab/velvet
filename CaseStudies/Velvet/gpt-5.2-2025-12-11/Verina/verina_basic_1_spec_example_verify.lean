import Lean
import Mathlib.Tactic

/- Problem Description
    hasOppositeSign: determine whether two integers have opposite signs.

    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. Zero is considered neither positive nor negative.
    3. Two integers have opposite signs exactly when one is strictly positive
       and the other is strictly negative.
    4. Equivalently, both must be nonzero and their signs (via Int.sign)
       must be different and opposite.
    5. Int.sign x = 1 if x > 0; Int.sign x = -1 if x < 0; Int.sign x = 0 if x = 0.
    6. The method should return true iff a and b have opposite signs.
    7. It should return false if both are nonnegative, both are nonpositive,
       or if at least one is zero.

    We formalize this using inequalities on Int.
-/

section Specs

@[loomAbstractionSimp]
def hasOppositeSignSpec (a: Int) (b: Int) : Prop :=
  (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)

end Specs

section TestCases

-- Test case 1: example with a negative and a positive integer (-5, 10) → true
-- (taken from the original problem's first example)
def test1_a : Int := -5
def test1_b : Int := 10
def test1_Expected : Bool := true

-- Test case 2: positive and negative reversed (5, -10) → true
def test2_a : Int := 5
def test2_b : Int := -10
def test2_Expected : Bool := true

-- Test case 3: both positive (5, 10) → false
def test3_a : Int := 5
def test3_b : Int := 10
def test3_Expected : Bool := false

-- Test case 4: both negative (-5, -10) → false
def test4_a : Int := -5
def test4_b : Int := -10
def test4_Expected : Bool := false

-- Test case 5: one zero, one positive (0, 10) → false
def test5_a : Int := 0
def test5_b : Int := 10
def test5_Expected : Bool := false

-- Test case 6: one zero, one negative (0, -10) → false
def test6_a : Int := 0
def test6_b : Int := -10
def test6_Expected : Bool := false

-- Test case 7: both zero (0, 0) → false
def test7_a : Int := 0
def test7_b : Int := 0
def test7_Expected : Bool := false

-- Test case 8: small magnitude opposite signs (-1, 1) → true
def test8_a : Int := -1
def test8_b : Int := 1
def test8_Expected : Bool := true

end TestCases

section TestsVerify

-------------------------------
-- Verifications
-------------------------------

section Impl

-- Pre/Post Conditions
def ensures1 (a: Int) (b: Int) (result: Bool) := result = true ↔ hasOppositeSignSpec a b
def precondition (a: Int) (b: Int) := True
def postcondition (a: Int) (b: Int) (result: Bool) :=
  ensures1 a b result

end Impl

open Classical

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_a test1_b := by
  trivial

lemma test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro _
    right
    constructor
    · decide
    · decide
  · intro _
    rfl

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_a test2_b := by
  trivial

lemma test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro _
    left
    constructor
    · decide
    · decide
  · intro _
    rfl

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_a test3_b := by
  trivial

lemma test3_postcondition :
  postcondition test3_a test3_b test3_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro h
    cases h
  · intro h
    have hnot : ¬ hasOppositeSignSpec 5 10 := by
      intro h'
      cases h' with
      | inl h1 =>
          have : ¬ (10 : Int) < 0 := by decide
          exact this h1.right
      | inr h2 =>
          have : ¬ (5 : Int) < 0 := by decide
          exact this h2.left
    exact (hnot h).elim

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_a test4_b := by
  trivial

lemma test4_postcondition :
  postcondition test4_a test4_b test4_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro h
    cases h
  · intro h
    have hnot : ¬ hasOppositeSignSpec (-5) (-10) := by
      intro h'
      cases h' with
      | inl h1 =>
          have : ¬ (-5 : Int) > 0 := by decide
          exact this h1.left
      | inr h2 =>
          have : ¬ (-10 : Int) > 0 := by decide
          exact this h2.right
    exact (hnot h).elim

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_a test5_b := by
  trivial

lemma test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro h
    cases h
  · intro h
    have hnot : ¬ hasOppositeSignSpec 0 10 := by
      intro h'
      cases h' with
      | inl h1 =>
          have : ¬ (0 : Int) > 0 := by decide
          exact this h1.left
      | inr h2 =>
          have : ¬ (0 : Int) < 0 := by decide
          exact this h2.left
    exact (hnot h).elim

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_a test6_b := by
  trivial

lemma test6_postcondition :
  postcondition test6_a test6_b test6_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro h
    cases h
  · intro h
    have hnot : ¬ hasOppositeSignSpec 0 (-10) := by
      intro h'
      cases h' with
      | inl h1 =>
          have : ¬ (0 : Int) > 0 := by decide
          exact this h1.left
      | inr h2 =>
          have : ¬ (0 : Int) < 0 := by decide
          exact this h2.left
    exact (hnot h).elim

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_a test7_b := by
  trivial

lemma test7_postcondition :
  postcondition test7_a test7_b test7_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro h
    cases h
  · intro h
    have hnot : ¬ hasOppositeSignSpec 0 0 := by
      intro h'
      cases h' with
      | inl h1 =>
          have : ¬ (0 : Int) > 0 := by decide
          exact this h1.left
      | inr h2 =>
          have : ¬ (0 : Int) < 0 := by decide
          exact this h2.left
    exact (hnot h).elim

----------------------------
-- Verification: test8
----------------------------
lemma test8_precondition :
  precondition test8_a test8_b := by
  trivial

lemma test8_postcondition :
  postcondition test8_a test8_b test8_Expected := by
  unfold postcondition ensures1 hasOppositeSignSpec
  constructor
  · intro _
    right
    constructor
    · decide
    · decide
  · intro _
    rfl

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (a: Int) (b: Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _ ret1 ret2 h1 h2
  unfold postcondition ensures1 at h1 h2
  cases ret1 <;> cases ret2 <;> simp at h1 h2
  · simp
  · have : hasOppositeSignSpec a b := (h2.mpr rfl)
    have : False := h1.mp this
    exact this.elim
  · have : hasOppositeSignSpec a b := (h1.mpr rfl)
    have : False := h2.mp this
    exact this.elim
  · simp

end TestsVerify