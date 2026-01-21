import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

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
section Impl
method hasOppositeSign (a: Int) (b: Int)
  return (result: Bool)
  ensures result = true ↔ hasOppositeSignSpec a b
  do
  if a > 0 ∧ b < 0 then
    return true
  else if a < 0 ∧ b > 0 then
    return true
  else
    return false
end Impl
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
section Assertions
-- Test case 1
/--
info: DivM.res true
-/
#guard_msgs in
#eval (hasOppositeSign test1_a test1_b).run

example : (hasOppositeSign test1_a test1_b).run = DivM.res test1_Expected := by
  rfl
    

-- Test case 2
/--
info: DivM.res true
-/
#guard_msgs in
#eval (hasOppositeSign test2_a test2_b).run

-- Test case 3
/--
info: DivM.res false
-/
#guard_msgs in
#eval (hasOppositeSign test3_a test3_b).run

-- Test case 4
/--
info: DivM.res false
-/
#guard_msgs in
#eval (hasOppositeSign test4_a test4_b).run

-- Test case 5
/--
info: DivM.res false
-/
#guard_msgs in
#eval (hasOppositeSign test5_a test5_b).run

-- Test case 6
/--
info: DivM.res false
-/
#guard_msgs in
#eval (hasOppositeSign test6_a test6_b).run

-- Test case 7
/--
info: DivM.res false
-/
#guard_msgs in
#eval (hasOppositeSign test7_a test7_b).run

-- Test case 8
/--
info: DivM.res true
-/
#guard_msgs in
#eval (hasOppositeSign test8_a test8_b).run
end Assertions
section Pbt

extract_program_for hasOppositeSign
prove_precondition_decidable_for hasOppositeSign
prove_postcondition_decidable_for hasOppositeSign
derive_tester_for hasOppositeSign
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := hasOppositeSignTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt
section Proof

-- prove_correct hasOppositeSign by
--   loom_solve <;> (simp at *; expose_names)  


theorem goal_0 (a : ℤ)
    (b : ℤ)
    (a_2 : b < 0)
    (a_1 : 0 < a) : hasOppositeSignSpec a b := by
  -- Unfold the definition of hasOppositeSignSpec
  unfold hasOppositeSignSpec
  -- We prove the left side of the disjunction
  apply Or.inl
  -- Now we prove the conjunction a > 0 ∧ b < 0
  apply And.intro
  · -- First part: a > 0
    exact a_1
  · -- Second part: b < 0
    exact a_2


theorem goal_1 (a : ℤ)
    (b : ℤ)
    (a_1 : a < 0)
    (if_neg : 0 < a → 0 ≤ b)
    (a_2 : 0 < b) : hasOppositeSignSpec a b := by
  -- hasOppositeSignSpec a b = (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)
  right
  constructor
  · exact a_1
  · exact a_2


theorem goal_2 (a : ℤ)
    (b : ℤ)
    (if_neg : 0 < a → 0 ≤ b)
    (if_neg_1 : a < 0 → b ≤ 0) : ¬hasOppositeSignSpec a b := by
  intro h
  unfold hasOppositeSignSpec at h
  cases h with
  | inl h₁ =>
    rcases h₁ with ⟨ha_pos, hb_neg⟩
    have hb_nonneg : 0 ≤ b := if_neg ha_pos
    have : (0 : ℤ) < 0 := lt_of_le_of_lt hb_nonneg hb_neg
    exact lt_irrefl _ this
  | inr h₂ =>
    rcases h₂ with ⟨ha_neg, hb_pos⟩
    have hb_nonpos : b ≤ 0 := if_neg_1 ha_neg
    have : (0 : ℤ) < 0 := lt_of_lt_of_le hb_pos hb_nonpos
    exact lt_irrefl _ this



prove_correct hasOppositeSign by
  loom_solve <;> (simp at *; expose_names)
  exact (goal_0 a b a_2 a_1)
  exact (goal_1 a b a_1 if_neg a_2)
  exact (goal_2 a b if_neg if_neg_1)  


end Proof
