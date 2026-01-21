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
    double_array_elements: Transform an array of integers by doubling each element.
    Natural language breakdown:
    1. Input is an array s of integers.
    2. Output is an array result of integers.
    3. The output array has the same size as the input array.
    4. For every valid index i (i < s.size), result[i]! equals 2 * s[i]!. 
    5. The input array is assumed valid, and doubling does not overflow (modeled as standard Int arithmetic).
-/

section Specs
-- Helper definition: element-wise doubling relation between input and output arrays.
-- We use Nat indices and Array.get! access with an explicit range hypothesis i < s.size.
def DoubledArray (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ (i : Nat), i < s.size → result[i]! = (2 : Int) * s[i]!

def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  DoubledArray s result
end Specs

section Impl
method double_array_elements (s : Array Int) return (result : Array Int)
  require precondition s
  ensures postcondition s result
  do
    let mut result := Array.replicate s.size (0 : Int)
    let mut i : Nat := 0
    while i < s.size
      -- i stays within bounds of the array; needed for safe indexing and to conclude i = s.size at exit.
      -- Init: i=0, s.size is Nat so 0 ≤ i and i ≤ s.size. Preserved by i := i+1 under guard i < s.size.
      invariant "inv_i_bounds" i ≤ s.size
      -- result always has the same size as s; preserved by set!.
      -- Init: replicate has size s.size. Preserved: set! does not change array size.
      invariant "inv_size" result.size = s.size
      -- Elements already processed [0, i) are correctly doubled.
      -- Init: vacuously true for i=0. Preserved: set! at index i establishes property for new i.
      invariant "inv_prefix_doubled" (∀ (k : Nat), k < i → result[k]! = (2 : Int) * s[k]!)
      done_with i = s.size
    do
      result := result.set! i ((2 : Int) * s[i]!)
      i := i + 1
    return result
end Impl

section TestCases
-- Test case 1: empty array
-- (Given example from the problem statement)
def test1_s : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: typical positive integers
-- (Given example from the problem statement)
def test2_s : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Array Int := #[2, 4, 6, 8, 10]

-- Test case 3: includes zero and negative
-- (Given example from the problem statement)
def test3_s : Array Int := #[0, -1, 5]
def test3_Expected : Array Int := #[0, -2, 10]

-- Test case 4: single element positive
-- (Given example from the problem statement)
def test4_s : Array Int := #[100]
def test4_Expected : Array Int := #[200]

-- Test case 5: all negative
-- (Given example from the problem statement)
def test5_s : Array Int := #[-3, -4]
def test5_Expected : Array Int := #[-6, -8]

-- Test case 6: single element zero

def test6_s : Array Int := #[0]
def test6_Expected : Array Int := #[0]

-- Test case 7: mixed signs

def test7_s : Array Int := #[7, -8, 9, -10]
def test7_Expected : Array Int := #[14, -16, 18, -20]

-- Test case 8: repeated values

def test8_s : Array Int := #[2, 2, 2]
def test8_Expected : Array Int := #[4, 4, 4]

-- Recommend to validate: test1, test2, test3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((double_array_elements test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((double_array_elements test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((double_array_elements test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((double_array_elements test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((double_array_elements test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((double_array_elements test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((double_array_elements test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((double_array_elements test8_s).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for double_array_elements
prove_precondition_decidable_for double_array_elements
prove_postcondition_decidable_for double_array_elements
derive_tester_for double_array_elements
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := double_array_elementsTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct double_array_elements by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : Array ℤ)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_size : result.size = s.size)
    (invariant_inv_prefix_doubled : ∀ k < i, result[k]! = 2 * s[k]!)
    (done_1 : i = s.size)
    (i_1 : ℕ)
    (result_1 : Array ℤ)
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition s result_1 := by
  -- unfold the postcondition / DoubledArray spec
  unfold postcondition
  unfold DoubledArray
  constructor
  · -- size equality
    simpa [i_2.right] using invariant_inv_size
  · -- pointwise doubling
    intro j hj
    have hj' : j < i := by
      -- rewrite `hj : j < s.size` using `done_1 : i = s.size`
      simpa [done_1] using hj
    have hval : result[j]! = 2 * s[j]! := invariant_inv_prefix_doubled j hj'
    simpa [i_2.right] using hval


prove_correct double_array_elements by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s i result invariant_inv_size invariant_inv_prefix_doubled done_1 i_1 result_1 i_2)
end Proof
