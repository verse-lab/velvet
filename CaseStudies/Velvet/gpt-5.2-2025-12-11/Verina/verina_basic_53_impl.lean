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
    CalSum: determine the sum of the first N natural numbers.
    Natural language breakdown:
    1. The input N is a natural number (Nat).
    2. The intended output is the sum 1 + 2 + ... + N.
    3. If N = 0, the sum is 0.
    4. For any N, the sum is characterized by the closed form N * (N + 1) / 2.
    5. There are no additional preconditions beyond providing a Nat.
-/

section Specs
-- Helper function: Gauss closed form for the sum 1 + 2 + ... + N.
-- We choose a fresh name to avoid collisions with any existing declarations.
-- Note: In Nat, division is truncated, but for N*(N+1) it is exact since the product is even.
def gaussSumCal (N : Nat) : Nat :=
  N * (N + 1) / 2

def precondition (N : Nat) : Prop :=
  True

def postcondition (N : Nat) (result : Nat) : Prop :=
  result = gaussSumCal N
end Specs

section Impl
method CalSum (N: Nat)
  return (result: Nat)
  require precondition N
  ensures postcondition N result
  do
  let mut i : Nat := 0
  let mut acc : Nat := 0
  while i < N
    -- Invariant: loop index stays within bounds; initialized with i=0 and preserved by i := i+1.
    invariant "CalSum_inv_bounds" i ≤ N
    -- Invariant: accumulator equals the Gauss sum of the current index i.
    -- Initialization: acc=0=gaussSumCal 0. Preservation: after i:=i+1 and acc:=acc+i, acc becomes sum 1..i.
    -- Sufficiency: on exit i=N, gives acc=gaussSumCal N.
    invariant "CalSum_inv_acc" acc = gaussSumCal i
    done_with (i = N)
  do
    i := i + 1
    acc := acc + i
  return acc
end Impl

section TestCases
-- Test case 1: example from prompt tests (N = 0)
-- Expected: 0

def test1_N : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: N = 1
-- Expected: 1

def test2_N : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: N = 5
-- Expected: 15

def test3_N : Nat := 5
def test3_Expected : Nat := 15

-- Test case 4: N = 10
-- Expected: 55

def test4_N : Nat := 10
def test4_Expected : Nat := 55

-- Test case 5: N = 20
-- Expected: 210

def test5_N : Nat := 20
def test5_Expected : Nat := 210

-- Additional representative cases

-- Test case 6: small even N = 2
-- Expected: 3

def test6_N : Nat := 2
def test6_Expected : Nat := 3

-- Test case 7: small odd N = 3
-- Expected: 6

def test7_N : Nat := 3
def test7_Expected : Nat := 6

-- Test case 8: larger but reasonable N = 100
-- Expected: 5050

def test8_N : Nat := 100
def test8_Expected : Nat := 5050

-- Recommend to validate: test1, test3, test4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((CalSum test1_N).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CalSum test2_N).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CalSum test3_N).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CalSum test4_N).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CalSum test5_N).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CalSum test6_N).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CalSum test7_N).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CalSum test8_N).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for CalSum
prove_precondition_decidable_for CalSum
prove_postcondition_decidable_for CalSum
derive_tester_for CalSum
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := CalSumTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct CalSum by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (N : ℕ)
    (acc : ℕ)
    (i : ℕ)
    (if_pos : i < N)
    (h_gi : gaussSumCal i = i * (i + 1) / 2)
    (h_gip1 : gaussSumCal (i + 1) = (i + 1) * (i + 1 + 1) / 2)
    (h_acc_rw : acc = gaussSumCal i)
    (h_reduce : gaussSumCal i = i * (i + 1) / 2)
    : i * (i + 1) / 2 + (i + 1) = (i + 1) * (i + 1 + 1) / 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (N : ℕ)
    (acc : ℕ)
    (i : ℕ)
    (invariant_CalSum_inv_acc : acc = gaussSumCal i)
    (if_pos : i < N)
    : acc + (i + 1) = gaussSumCal (i + 1) := by
  -- Step 1: rewrite LHS using the accumulator invariant
  have h_acc_rw : acc + (i + 1) = gaussSumCal i + (i + 1) := by
    simpa [invariant_CalSum_inv_acc]

  -- Step 2: unfold gaussSumCal at i
  have h_gi : gaussSumCal i = i * (i + 1) / 2 := by
    simp [gaussSumCal]

  -- Step 3: unfold gaussSumCal at i+1 (keep it in the canonical form)
  have h_gip1 : gaussSumCal (i + 1) = (i + 1) * ((i + 1) + 1) / 2 := by
    simp [gaussSumCal]

  -- Step 4: reduce main arithmetic goal to a closed-form identity
  have h_reduce :
      gaussSumCal i + (i + 1) = (i * (i + 1) / 2) + (i + 1) := by
    simpa [h_gi]

  -- Step 5: key arithmetic identity in Nat (proved elsewhere / by ring-like arithmetic)
  have h_closed :
      (i * (i + 1) / 2) + (i + 1) = (i + 1) * ((i + 1) + 1) / 2 := by
    -- this is the algebraic step: i*(i+1)/2 + (i+1) = (i+1)*(i+2)/2
    -- handled by Nat arithmetic lemmas about /2 being exact on these numerators
    (try simp at *; expose_names); exact (goal_0_0 N acc i if_pos h_gi h_gip1 h_acc_rw h_reduce); done

  -- Step 6: conclude gaussSumCal i + (i+1) = gaussSumCal (i+1)
  have h_step : gaussSumCal i + (i + 1) = gaussSumCal (i + 1) := by
    -- rewrite both sides using h_reduce, h_closed, and h_gip1
    calc
      gaussSumCal i + (i + 1) = (i * (i + 1) / 2) + (i + 1) := by simpa [h_reduce]
      _ = (i + 1) * ((i + 1) + 1) / 2 := by simpa [h_closed]
      _ = gaussSumCal (i + 1) := by simpa [h_gip1]

  -- Step 7: substitute back to prove the original goal
  calc
    acc + (i + 1) = gaussSumCal i + (i + 1) := by simpa [h_acc_rw]
    _ = gaussSumCal (i + 1) := by simpa [h_step]

theorem goal_1 : 0 = gaussSumCal 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2
    (N : ℕ)
    (acc : ℕ)
    (i : ℕ)
    (invariant_CalSum_inv_acc : acc = gaussSumCal i)
    (done_1 : i = N)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : acc = i_1 ∧ i = i_2)
    : postcondition N i_1 := by
    -- unfold postcondition
    simp [postcondition]
    -- extract acc = i_1
    have hAcc : acc = i_1 := i_3.left
    -- rewrite invariant at termination
    have hAccN : acc = gaussSumCal N := by
      simpa [done_1] using invariant_CalSum_inv_acc
    -- conclude
    exact (hAcc.symm.trans hAccN)


prove_correct CalSum by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 N acc i invariant_CalSum_inv_acc if_pos)
  exact (goal_1)
  exact (goal_2 N acc i invariant_CalSum_inv_acc done_1 i_1 i_2 i_3)
end Proof
