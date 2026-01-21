import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    DoubleQuadruple: return the pair consisting of twice and four-times the input integer.
    Natural language breakdown:
    1. The input is an integer x.
    2. The output is a pair (a, b) of integers.
    3. The first component a equals 2 * x.
    4. The second component b equals 4 * x.
    5. The method is defined for all integers (no preconditions).
-/

section Specs
def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int × Int) : Prop :=
  result.1 = (2 : Int) * x ∧
  result.2 = (4 : Int) * x
end Specs

section Impl
method DoubleQuadruple (x: Int)
  return (result: (Int × Int))
  require precondition x
  ensures postcondition x result
  do
    let a : Int := (2 : Int) * x
    let b : Int := (4 : Int) * x
    return (a, b)
end Impl

section TestCases
-- Test case 1: example x = 0
def test1_x : Int := 0
def test1_Expected : (Int × Int) := (0, 0)

-- Test case 2: x = 1
def test2_x : Int := 1
def test2_Expected : (Int × Int) := (2, 4)

-- Test case 3: x = -1
def test3_x : Int := -1
def test3_Expected : (Int × Int) := (-2, -4)

-- Test case 4: x = 10
def test4_x : Int := 10
def test4_Expected : (Int × Int) := (20, 40)

-- Test case 5: x = -5
def test5_x : Int := -5
def test5_Expected : (Int × Int) := (-10, -20)

-- Test case 6: x = 2
def test6_x : Int := 2
def test6_Expected : (Int × Int) := (4, 8)

-- Test case 7: x = -2
def test7_x : Int := -2
def test7_Expected : (Int × Int) := (-4, -8)

-- Test case 8: a larger magnitude positive x
def test8_x : Int := 123
def test8_Expected : (Int × Int) := (246, 492)

-- Test case 9: a larger magnitude negative x
def test9_x : Int := -123
def test9_Expected : (Int × Int) := (-246, -492)

-- Recommend to validate: 1, 2, 3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((DoubleQuadruple test1_x).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((DoubleQuadruple test2_x).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((DoubleQuadruple test3_x).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((DoubleQuadruple test4_x).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((DoubleQuadruple test5_x).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((DoubleQuadruple test6_x).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((DoubleQuadruple test7_x).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((DoubleQuadruple test8_x).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((DoubleQuadruple test9_x).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for DoubleQuadruple
prove_precondition_decidable_for DoubleQuadruple
prove_postcondition_decidable_for DoubleQuadruple
derive_tester_for DoubleQuadruple
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let res := DoubleQuadrupleTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct DoubleQuadruple by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (x : ℤ)
    : postcondition x (2 * x, 4 * x) := by
    unfold postcondition
    constructor <;> rfl


prove_correct DoubleQuadruple by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 x)
end Proof
