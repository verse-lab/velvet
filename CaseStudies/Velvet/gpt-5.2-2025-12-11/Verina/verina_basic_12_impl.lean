import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    cubeSurfaceArea: compute the surface area of a cube from its edge length.

    Natural language breakdown:
    1. The input is a natural number `size`, the length of an edge of a cube.
    2. The surface area of a cube equals 6 times the area of one face.
    3. Each face is a square with area `size ^ 2`.
    4. Therefore, the surface area equals `6 * (size ^ 2)`.
    5. The output is a natural number.
    6. There are no rejected inputs.
-/

section Specs
-- No helper definitions are required beyond standard Nat arithmetic and exponentiation.

def precondition (size : Nat) : Prop :=
  True

def postcondition (size : Nat) (result : Nat) : Prop :=
  result = 6 * (size ^ 2)
end Specs

section Impl
method cubeSurfaceArea (size : Nat) return (result : Nat)
  require precondition size
  ensures postcondition size result
  do
    let area := 6 * (size ^ 2)
    return area
end Impl

section TestCases
-- Test case 1: example from prompt: size = 3
-- Surface area = 6 * 3^2 = 54

def test1_size : Nat := 3
def test1_Expected : Nat := 54

-- Test case 2: size = 1

def test2_size : Nat := 1
def test2_Expected : Nat := 6

-- Test case 3: size = 10

def test3_size : Nat := 10
def test3_Expected : Nat := 600

-- Test case 4: size = 5

def test4_size : Nat := 5
def test4_Expected : Nat := 150

-- Test case 5: size = 2

def test5_size : Nat := 2
def test5_Expected : Nat := 24

-- Test case 6: edge case size = 0

def test6_size : Nat := 0
def test6_Expected : Nat := 0

-- Test case 7: another typical value

def test7_size : Nat := 7
def test7_Expected : Nat := 294

-- Test case 8: another value to cover arithmetic

def test8_size : Nat := 4
def test8_Expected : Nat := 96

-- Recommend to validate: test1, test2, test6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((cubeSurfaceArea test1_size).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((cubeSurfaceArea test2_size).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((cubeSurfaceArea test3_size).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((cubeSurfaceArea test4_size).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((cubeSurfaceArea test5_size).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((cubeSurfaceArea test6_size).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((cubeSurfaceArea test7_size).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((cubeSurfaceArea test8_size).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for cubeSurfaceArea
prove_precondition_decidable_for cubeSurfaceArea
prove_postcondition_decidable_for cubeSurfaceArea
derive_tester_for cubeSurfaceArea
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := cubeSurfaceAreaTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct cubeSurfaceArea by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (size : ℕ)
    (require_1 : precondition size)
    : postcondition size (6 * size ^ 2) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


prove_correct cubeSurfaceArea by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
