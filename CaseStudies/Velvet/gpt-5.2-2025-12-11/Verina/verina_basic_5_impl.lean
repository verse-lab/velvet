import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-
Problem Description:
  multiply: Multiply two integers.
  Natural language breakdown:
  1. The input consists of two integers a and b.
  2. The output is an integer representing the arithmetic product of a and b.
  3. There are no restrictions on inputs (they may be negative, zero, or positive).
  4. The result is uniquely determined by integer multiplication.
-/

section Specs
-- No helper functions are needed: Int has built-in multiplication via `Int.instMul`.

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result = a * b
end Specs

section Impl
method multiply (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  let prod := a * b
  return prod
end Impl

section TestCases
-- Test case 1: example (3 * 4)
def test1_a : Int := 3
def test1_b : Int := 4
def test1_Expected : Int := 12

-- Test case 2: positive times negative
def test2_a : Int := 3
def test2_b : Int := (-4)
def test2_Expected : Int := (-12)

-- Test case 3: negative times positive
def test3_a : Int := (-3)
def test3_b : Int := 4
def test3_Expected : Int := (-12)

-- Test case 4: negative times negative
def test4_a : Int := (-3)
def test4_b : Int := (-4)
def test4_Expected : Int := 12

-- Test case 5: zero times positive
def test5_a : Int := 0
def test5_b : Int := 5
def test5_Expected : Int := 0

-- Test case 6: positive times zero
def test6_a : Int := 5
def test6_b : Int := 0
def test6_Expected : Int := 0

-- Test case 7: zero times zero
def test7_a : Int := 0
def test7_b : Int := 0
def test7_Expected : Int := 0

-- Test case 8: larger magnitude mix
def test8_a : Int := 123
def test8_b : Int := (-45)
def test8_Expected : Int := (-5535)

-- Recommend to validate: test1, test4, test5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((multiply test1_a test1_b).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((multiply test2_a test2_b).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((multiply test3_a test3_b).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((multiply test4_a test4_b).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((multiply test5_a test5_b).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((multiply test6_a test6_b).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((multiply test7_a test7_b).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((multiply test8_a test8_b).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for multiply
prove_precondition_decidable_for multiply
prove_postcondition_decidable_for multiply
derive_tester_for multiply
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := multiplyTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct multiply by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (a : ℤ)
    (b : ℤ)
    (require_1 : precondition a b) : postcondition a b (a * b) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


prove_correct multiply by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
