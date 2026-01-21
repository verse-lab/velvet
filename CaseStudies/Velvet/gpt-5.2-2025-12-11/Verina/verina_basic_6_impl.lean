import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    verina_basic_6: Minimum of three integers

    Natural language breakdown:
    1. The input consists of three integers a, b, and c.
    2. The function returns an integer result intended to be the minimum among a, b, and c.
    3. The result must be less than or equal to each input: result ≤ a, result ≤ b, and result ≤ c.
    4. The result must be one of the inputs: result = a or result = b or result = c.
    5. There are no rejected inputs; all Int inputs are valid.
-/

section Specs
-- No rejected inputs.
-- IMPORTANT: SpecDSL requires parameter names and order to match exactly between
-- precondition and the corresponding prefix of postcondition.
def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  (result ≤ a ∧ result ≤ b ∧ result ≤ c) ∧
  (result = a ∨ result = b ∨ result = c)
end Specs

section Impl
method minOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
    let mut m := a
    if b <= m then
      m := b
    else
      pure ()
    if c <= m then
      m := c
    else
      pure ()
    return m
end Impl

section TestCases
-- Test case 1: descending positives (given example)
def test1_a : Int := 3
def test1_b : Int := 2
def test1_c : Int := 1
def test1_Expected : Int := 1

-- Test case 2: all equal
def test2_a : Int := 5
def test2_b : Int := 5
def test2_c : Int := 5
def test2_Expected : Int := 5

-- Test case 3: distinct positives with first minimum
def test3_a : Int := 10
def test3_b : Int := 20
def test3_c : Int := 15
def test3_Expected : Int := 10

-- Test case 4: includes negative, first is minimum
def test4_a : Int := -1
def test4_b : Int := 2
def test4_c : Int := 3
def test4_Expected : Int := -1

-- Test case 5: includes negative, second is minimum
def test5_a : Int := 2
def test5_b : Int := -3
def test5_c : Int := 4
def test5_Expected : Int := -3

-- Test case 6: includes negative, third is minimum
def test6_a : Int := 2
def test6_b : Int := 3
def test6_c : Int := -5
def test6_Expected : Int := -5

-- Test case 7: zeros and positive
def test7_a : Int := 0
def test7_b : Int := 0
def test7_c : Int := 1
def test7_Expected : Int := 0

-- Test case 8: symmetric around zero
def test8_a : Int := 0
def test8_b : Int := -1
def test8_c : Int := 1
def test8_Expected : Int := -1

-- Test case 9: all negative
def test9_a : Int := -5
def test9_b : Int := -2
def test9_c : Int := -3
def test9_Expected : Int := -5

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test5, test9
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((minOfThree test1_a test1_b test1_c).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((minOfThree test2_a test2_b test2_c).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((minOfThree test3_a test3_b test3_c).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((minOfThree test4_a test4_b test4_c).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((minOfThree test5_a test5_b test5_c).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((minOfThree test6_a test6_b test6_c).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((minOfThree test7_a test7_b test7_c).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((minOfThree test8_a test8_b test8_c).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((minOfThree test9_a test9_b test9_c).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for minOfThree
prove_precondition_decidable_for minOfThree
prove_postcondition_decidable_for minOfThree
derive_tester_for minOfThree
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let arg_2 ← Plausible.SampleableExt.interpSample (Int)
    let res := minOfThreeTester arg_0 arg_1 arg_2
    pure ((arg_0, arg_1, arg_2), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct minOfThree by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (a : ℤ)
    (b : ℤ)
    (c : ℤ)
    (require_1 : precondition a b c)
    (if_pos : b ≤ a)
    (if_pos_1 : c ≤ b) : postcondition a b c c := by
  unfold postcondition
  constructor
  · constructor
    · exact Int.le_trans if_pos_1 if_pos
    · constructor
      · exact if_pos_1
      · exact le_rfl
  · exact Or.inr (Or.inr rfl)

theorem goal_1 (a : ℤ)
    (b : ℤ)
    (c : ℤ)
    (require_1 : precondition a b c)
    (if_pos : b ≤ a)
    (if_neg : b < c) : postcondition a b c b := by
  unfold postcondition
  have h_b_le_a : b ≤ a := by
    exact if_pos
  have h_b_le_b : b ≤ b := by
    exact le_rfl
  have h_b_le_c : b ≤ c := by
    exact le_of_lt if_neg
  have h_ineq : b ≤ a ∧ b ≤ b ∧ b ≤ c := by
    constructor
    · exact h_b_le_a
    · constructor
      · exact h_b_le_b
      · exact h_b_le_c
  have h_mem : b = a ∨ b = b ∨ b = c := by
    exact Or.inr (Or.inl rfl)
  constructor
  · exact h_ineq
  · exact h_mem

theorem goal_2 (a : ℤ)
    (b : ℤ)
    (c : ℤ)
    (require_1 : precondition a b c)
    (if_pos : c ≤ a)
    (if_neg : a < b) : postcondition a b c c := by
  unfold postcondition
  constructor
  · constructor
    · exact if_pos
    · constructor
      ·
        have hab : a ≤ b := Int.le_of_lt if_neg
        exact le_trans if_pos hab
      · exact le_rfl
  · right
    right
    rfl

theorem goal_3 (a : ℤ)
    (b : ℤ)
    (c : ℤ)
    (require_1 : precondition a b c)
    (if_neg : a < b)
    (if_neg_1 : a < c) : postcondition a b c a := by
  unfold postcondition
  constructor
  · constructor
    · exact le_rfl
    · constructor
      · exact Int.le_of_lt if_neg
      · exact Int.le_of_lt if_neg_1
  · exact Or.inl rfl


prove_correct minOfThree by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
  apply goal_1 <;> assumption
  apply goal_2 <;> assumption
  apply goal_3 <;> assumption
end Proof
