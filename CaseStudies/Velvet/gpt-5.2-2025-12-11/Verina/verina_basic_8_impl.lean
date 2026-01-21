import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    myMin: Determine the minimum of two integers.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must be less than or equal to a, and less than or equal to b.
    4. The result must be one of the inputs (either a or b).
    5. When a = b, returning either one is allowed (they are equal).
-/

section Specs
-- No helper functions are necessary: we can specify the minimum using order and equality.

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ (result = a ∨ result = b)
end Specs

section Impl
method myMin (a : Int) (b : Int) return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
    if a <= b then
      return a
    else
      return b
end Impl

section TestCases
-- Test case 1: example (a = 3, b = 5)
def test1_a : Int := 3
def test1_b : Int := 5
def test1_Expected : Int := 3

-- Test case 2: a > b
def test2_a : Int := 10
def test2_b : Int := 7
def test2_Expected : Int := 7

-- Test case 3: a = b
def test3_a : Int := 4
def test3_b : Int := 4
def test3_Expected : Int := 4

-- Test case 4: negative and positive
def test4_a : Int := -3
def test4_b : Int := 5
def test4_Expected : Int := -3

-- Test case 5: positive and negative
def test5_a : Int := 3
def test5_b : Int := -5
def test5_Expected : Int := -5

-- Test case 6: both negative
def test6_a : Int := -3
def test6_b : Int := -5
def test6_Expected : Int := -5

-- Test case 7: zero and positive
def test7_a : Int := 0
def test7_b : Int := 10
def test7_Expected : Int := 0

-- Test case 8: zero and negative
def test8_a : Int := 0
def test8_b : Int := -10
def test8_Expected : Int := -10

-- Recommend to validate: 1, 3, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((myMin test1_a test1_b).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((myMin test2_a test2_b).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((myMin test3_a test3_b).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((myMin test4_a test4_b).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((myMin test5_a test5_b).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((myMin test6_a test6_b).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((myMin test7_a test7_b).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((myMin test8_a test8_b).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for myMin
prove_precondition_decidable_for myMin
prove_postcondition_decidable_for myMin
derive_tester_for myMin
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := myMinTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct myMin by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (a : ℤ)
    (b : ℤ)
    (require_1 : precondition a b)
    (if_pos : a ≤ b) : postcondition a b a := by
    unfold postcondition
    constructor
    · exact le_rfl
    · constructor
      · exact if_pos
      · exact Or.inl rfl

theorem goal_1 (a : ℤ)
    (b : ℤ)
    (require_1 : precondition a b)
    (if_neg : b < a) : postcondition a b b := by
    unfold postcondition
    constructor
    · exact le_of_lt if_neg
    · constructor
      · exact le_rfl
      · exact Or.inr rfl


prove_correct myMin by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
  apply goal_1 <;> assumption
end Proof
