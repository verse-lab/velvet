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
    removeElement: remove the element at index k from an array of integers.
    Natural language breakdown:
    1. Inputs are an integer array s and a natural number k (0-indexed).
    2. k is assumed to be a valid index, i.e., 0 ≤ k < s.size.
    3. The output is an array containing all elements of s except the one at index k.
    4. Elements before index k are unchanged and keep their positions.
    5. Elements after index k are shifted left by one position.
    6. The output array has size exactly s.size - 1.
-/

section Specs
-- Helper: describe the element-wise relationship between input and output after removing index k.
-- For output index i:
-- * if i < k, output[i] = s[i]
-- * if i ≥ k, output[i] = s[i+1]

def precondition (s : Array Int) (k : Nat) : Prop :=
  k < s.size

def postcondition (s : Array Int) (k : Nat) (result : Array Int) : Prop :=
  result.size + 1 = s.size ∧
  (∀ (i : Nat), i < result.size →
      (if i < k then result[i]! = s[i]! else result[i]! = s[i + 1]!))
end Specs

section Impl
method removeElement (s : Array Int) (k : Nat)
  return (result : Array Int)
  require precondition s k
  ensures postcondition s k result
  do
  let mut result := Array.replicate (s.size - 1) (0:Int)
  let mut i : Nat := 0
  while i < result.size
    -- Bounds: i is within result indices; initialization i=0, preservation by i:=i+1 under loop guard.
    invariant "inv_i_le" i ≤ result.size
    -- Result size is fixed and matches specification: since k < s.size, we have s.size > 0 so (s.size - 1) is well-defined.
    invariant "inv_res_size" result.size + 1 = s.size
    -- Prefix correctness: all already-filled positions satisfy the remove-at-k relationship.
    invariant "inv_prefix" ∀ (j : Nat), j < i →
      (if j < k then result[j]! = s[j]! else result[j]! = s[j + 1]!)
  do
    if i < k then
      result := result.set! i (s[i]!)
    else
      result := result.set! i (s[i + 1]!)
    i := i + 1
  return result
end Impl

section TestCases
-- Test case 1: example from prompt
-- remove index 2 from #[1,2,3,4,5]

def test1_s : Array Int := #[1, 2, 3, 4, 5]
def test1_k : Nat := 2
def test1_Expected : Array Int := #[1, 2, 4, 5]

-- Test case 2: remove first element

def test2_s : Array Int := #[10, 20, 30, 40]
def test2_k : Nat := 0
def test2_Expected : Array Int := #[20, 30, 40]

-- Test case 3: remove last element

def test3_s : Array Int := #[10, 20, 30, 40]
def test3_k : Nat := 3
def test3_Expected : Array Int := #[10, 20, 30]

-- Test case 4: singleton array becomes empty

def test4_s : Array Int := #[7]
def test4_k : Nat := 0
def test4_Expected : Array Int := #[]

-- Test case 5: remove from middle with negative ints

def test5_s : Array Int := #[-1, 0, 5, -7]
def test5_k : Nat := 1
def test5_Expected : Array Int := #[-1, 5, -7]

-- Test case 6: remove from size-2 array, remove last

def test6_s : Array Int := #[3, 9]
def test6_k : Nat := 1
def test6_Expected : Array Int := #[3]

-- Test case 7: remove from size-2 array, remove first

def test7_s : Array Int := #[3, 9]
def test7_k : Nat := 0
def test7_Expected : Array Int := #[9]

-- Test case 8: repeated values; removing one occurrence at index k

def test8_s : Array Int := #[2, 2, 2, 2]
def test8_k : Nat := 2
def test8_Expected : Array Int := #[2, 2, 2]

-- Recommend to validate: 1, 2, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((removeElement test1_s test1_k).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((removeElement test2_s test2_k).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((removeElement test3_s test3_k).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((removeElement test4_s test4_k).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((removeElement test5_s test5_k).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((removeElement test6_s test6_k).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((removeElement test7_s test7_k).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((removeElement test8_s test8_k).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for removeElement
prove_precondition_decidable_for removeElement
prove_postcondition_decidable_for removeElement
derive_tester_for removeElement
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Nat)
    let res := removeElementTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct removeElement by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : Array ℤ)
    (k : ℕ)
    (require_1 : precondition s k)
    : s.size - 1 + 1 = s.size := by
    -- unfold the precondition to get k < s.size
    have hk : k < s.size := by
      simpa [precondition] using require_1
    -- derive 0 < s.size from 0 ≤ k and k < s.size
    have hpos : 0 < s.size := by
      exact Nat.lt_of_le_of_lt (Nat.zero_le k) hk
    -- finish with the standard lemma
    simpa using (Nat.sub_one_add_one_eq_of_pos hpos)

theorem goal_1
    (s : Array ℤ)
    (k : ℕ)
    (require_1 : precondition s k)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_le : i ≤ result.size)
    (invariant_inv_res_size : result.size + 1 = s.size)
    (invariant_inv_prefix : ∀ j < i, if j < k then result[j]! = s[j]! else result[j]! = s[j + 1]!)
    (i_1 : ℕ)
    (result_1 : Array ℤ)
    (done_1 : result.size ≤ i)
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition s k result_1 := by
    rcases i_2 with ⟨hi, hres⟩
    have hiSize : i = result.size := Nat.le_antisymm invariant_inv_i_le done_1
    unfold postcondition
    constructor
    · -- size part
      simpa [hres] using invariant_inv_res_size
    · -- pointwise part
      intro t ht
      have ht' : t < result.size := by simpa [hres] using ht
      have hti : t < i := by simpa [hiSize] using ht'
      have := invariant_inv_prefix t hti
      simpa [hres] using this


prove_correct removeElement by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s k require_1)
  exact (goal_1 s k require_1 i result invariant_inv_i_le invariant_inv_res_size invariant_inv_prefix i_1 result_1 done_1 i_2)
end Proof
