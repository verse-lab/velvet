import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    cubeElements: Replace every element of an integer array with its cube.
    Natural language breakdown:
    1. Input is an array of integers (possibly empty).
    2. Output is an array of integers with the same size as the input.
    3. For each valid index i, the output element at i equals the cube of the input element at i.
    4. Cubing means multiplying the element by itself three times: x * x * x.
    5. There are no additional preconditions; the function must work for any array.
-/

section Specs
-- Helper: integer cube
-- We use direct multiplication to avoid needing extra exponentiation imports.
def intCube (x : Int) : Int := x * x * x

def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: size preserved and pointwise cube relation.
-- Using Nat indices with a[i]! as recommended.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
    (∀ (i : Nat), i < a.size → result[i]! = intCube (a[i]!))
end Specs

section Impl
method cubeElements (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  let mut result := Array.replicate a.size (0 : Int)
  let mut i : Nat := 0
  while i < a.size
    -- Invariant 1: index i stays within bounds, enabling safe reads/writes and proving termination at exit.
    -- Init: i=0. Preserved: i increments by 1 while condition ensures i<a.size. Exit: i=a.size.
    invariant "i_bounds" (i ≤ a.size)
    -- Invariant 2: result array size is unchanged and matches input size.
    -- Init: replicate has size a.size. Preserved: set! preserves size. Needed for postcondition.
    invariant "size_preserved" (result.size = a.size)
    -- Invariant 3: all positions already processed (< i) satisfy the cube relation.
    -- Init: vacuously true at i=0. Preserved: body sets index i correctly and doesn't change earlier indices.
    -- Exit with i=a.size gives the full pointwise postcondition.
    invariant "prefix_cubed" (∀ (k : Nat), k < i → result[k]! = intCube (a[k]!))
  do
    let x := a[i]!
    result := result.set! i (intCube x)
    i := i + 1
  return result
end Impl

section TestCases
-- Test case 1: example given in the prompt

def test1_a : Array Int := #[1, 2, 3, 4]
def test1_Expected : Array Int := #[1, 8, 27, 64]

-- Test case 2: includes zero and negative values

def test2_a : Array Int := #[0, -1, -2, 3]
def test2_Expected : Array Int := #[0, -1, -8, 27]

-- Test case 3: empty array

def test3_a : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: singleton positive

def test4_a : Array Int := #[5]
def test4_Expected : Array Int := #[125]

-- Test case 5: repeated negative values

def test5_a : Array Int := #[-3, -3]
def test5_Expected : Array Int := #[-27, -27]

-- Test case 6: mixture with sign variety

def test6_a : Array Int := #[-10, 1, 2]
def test6_Expected : Array Int := #[-1000, 1, 8]

-- Test case 7: all zeros

def test7_a : Array Int := #[0, 0, 0]
def test7_Expected : Array Int := #[0, 0, 0]

-- Test case 8: longer mixed values

def test8_a : Array Int := #[2, -4, 0, 7, -1]
def test8_Expected : Array Int := #[8, -64, 0, 343, -1]

-- Recommend to validate: test1, test2, test3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((cubeElements test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((cubeElements test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((cubeElements test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((cubeElements test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((cubeElements test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((cubeElements test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((cubeElements test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((cubeElements test8_a).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for cubeElements
prove_precondition_decidable_for cubeElements
prove_postcondition_decidable_for cubeElements
derive_tester_for cubeElements
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := cubeElementsTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct cubeElements by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_i_bounds : i ≤ a.size)
    (invariant_size_preserved : result.size = a.size)
    (invariant_prefix_cubed : ∀ k < i, result[k]! = intCube a[k]!)
    (i_1 : ℕ)
    (result_1 : Array ℤ)
    (done_1 : a.size ≤ i)
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition a result_1 := by
    rcases i_2 with ⟨hi, hres⟩
    -- From bounds at loop exit, i = a.size
    have hiSize : i = a.size := Nat.le_antisymm invariant_i_bounds done_1
    constructor
    · -- size preserved
      simpa [hres] using invariant_size_preserved
    · intro j hj
      -- turn j < a.size into j < i using i = a.size
      have hji : j < i := by simpa [hiSize] using hj
      -- use invariant on the full range
      have : result[j]! = intCube a[j]! := invariant_prefix_cubed j hji
      simpa [hres] using this


prove_correct cubeElements by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
