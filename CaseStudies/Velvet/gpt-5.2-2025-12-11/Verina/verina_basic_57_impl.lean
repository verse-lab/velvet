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
    CountLessThan: count how many numbers in an integer array are strictly less than a given threshold.
    Natural language breakdown:
    1. Input is an array of integers `numbers` and an integer `threshold`.
    2. An element contributes to the count exactly when it is strictly less than `threshold`.
    3. The output is a natural number equal to the number of indices `i` within bounds such that `numbers[i]! < threshold`.
    4. The function must work for any array (including empty) and any integer threshold.
    5. The result is uniquely determined by the set of in-bounds indices satisfying the predicate.
-/

section Specs
-- Helper: count of elements satisfying a boolean predicate, using List.countP on the array's list view.
-- This is a mathematical characterization of the desired count.
-- (Using Mathlib/Std's List.countP and Array.toList.)
def countLessThanSpec (numbers : Array Int) (threshold : Int) : Nat :=
  (numbers.toList.countP (fun x => x < threshold))

-- No preconditions.
def precondition (numbers : Array Int) (threshold : Int) : Prop :=
  True

-- Postcondition: result equals the number of elements strictly less than threshold.
-- This is expressed as a count over the list view of the array.
def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) : Prop :=
  result = countLessThanSpec numbers threshold
end Specs

section Impl
method CountLessThan (numbers : Array Int) (threshold : Int)
  return (result : Nat)
  require precondition numbers threshold
  ensures postcondition numbers threshold result
  do
  let mut i : Nat := 0
  let mut cnt : Nat := 0
  while i < numbers.size
    -- Invariant 1: index stays within bounds of the array.
    -- Init: i=0. Preserved: i increments by 1 and guard implies i < size.
    invariant "inv_i_bounds" i ≤ numbers.size

    -- Invariant 2: bridge between array size and list length, enabling list indexing facts from i < size.
    -- Init/Preserved: numbers is immutable, so this equality remains true.
    invariant "inv_len" numbers.toList.length = numbers.size

    -- Invariant 3: cnt is the number of elements < threshold in the processed prefix.
    -- Init: i=0, take 0 has count 0. Preserved: one-step extension corresponds to the current element.
    -- (Uses inv_len to relate i < numbers.size to i < numbers.toList.length.)
    invariant "inv_cnt_take" cnt = (numbers.toList.take i).countP (fun x => x < threshold)

    done_with i = numbers.size
  do
    if numbers[i]! < threshold then
      cnt := cnt + 1
    i := i + 1
  return cnt
end Impl

section TestCases
-- Test case 1: example from prompt
-- numbers = #[1,2,3,4,5], threshold = 3 => 1 and 2 are less than 3

def test1_numbers : Array Int := #[1, 2, 3, 4, 5]
def test1_threshold : Int := 3
def test1_Expected : Nat := 2

-- Test case 2: empty array

def test2_numbers : Array Int := #[]
def test2_threshold : Int := 10
def test2_Expected : Nat := 0

-- Test case 3: mix with negatives; threshold = 0

def test3_numbers : Array Int := #[-1, 0, 1]
def test3_threshold : Int := 0
def test3_Expected : Nat := 1

-- Test case 4: unsorted array; count elements less than 5

def test4_numbers : Array Int := #[5, 6, 7, 2, 1]
def test4_threshold : Int := 5
def test4_Expected : Nat := 2

-- Test case 5: all equal to threshold (strictly less gives 0)

def test5_numbers : Array Int := #[3, 3, 3, 3]
def test5_threshold : Int := 3
def test5_Expected : Nat := 0

-- Test case 6: threshold very large; all elements counted

def test6_numbers : Array Int := #[-2, 0, 5]
def test6_threshold : Int := 100

def test6_Expected : Nat := 3

-- Test case 7: threshold very small; none counted

def test7_numbers : Array Int := #[-10, 0, 10]
def test7_threshold : Int := (-11)
def test7_Expected : Nat := 0

-- Test case 8: single element less than threshold

def test8_numbers : Array Int := #[42]
def test8_threshold : Int := 100
def test8_Expected : Nat := 1

-- Test case 9: single element equal to threshold (strictly less => 0)

def test9_numbers : Array Int := #[7]
def test9_threshold : Int := 7
def test9_Expected : Nat := 0

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((CountLessThan test1_numbers test1_threshold).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CountLessThan test2_numbers test2_threshold).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CountLessThan test3_numbers test3_threshold).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CountLessThan test4_numbers test4_threshold).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CountLessThan test5_numbers test5_threshold).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CountLessThan test6_numbers test6_threshold).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CountLessThan test7_numbers test7_threshold).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CountLessThan test8_numbers test8_threshold).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((CountLessThan test9_numbers test9_threshold).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for CountLessThan
prove_precondition_decidable_for CountLessThan
prove_postcondition_decidable_for CountLessThan
derive_tester_for CountLessThan
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := CountLessThanTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct CountLessThan by
  -- loom_solve <;> (try simp at *; expose_names)
end Proof
