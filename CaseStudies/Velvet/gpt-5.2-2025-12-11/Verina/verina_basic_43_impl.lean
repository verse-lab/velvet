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
    sumOfFourthPowerOfOddNumbers: compute the sum of the fourth powers of the first n odd natural numbers.
    Natural language breakdown:
    1. The input n is a natural number representing how many odd numbers are included.
    2. The k-th odd natural number (0-based) is (2*k + 1).
    3. We consider the first n odd numbers: (2*0+1), (2*1+1), ..., (2*(n-1)+1).
    4. Each of these odd numbers is raised to the 4th power.
    5. The output is the sum of these fourth powers.
    6. If n = 0, the sum is over an empty collection and equals 0.
-/

section Specs
-- Helper: the k-th odd natural number (0-based)
def oddAt (k : Nat) : Nat := 2 * k + 1

-- Helper: sum of fourth powers of the first n odd numbers, as a finite sum over `range n`.
-- We avoid the binder notation `∑ k in ...` because it may not parse in this environment.
def sumFourthOdd (n : Nat) : Nat :=
  (Finset.range n).sum (fun k => (oddAt k) ^ 4)

-- No preconditions: n is a Nat already.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: the result is exactly the finite sum of the fourth powers of the first n odd numbers.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = sumFourthOdd n
end Specs

section Impl
method sumOfFourthPowerOfOddNumbers (n: Nat) return (result: Nat)
  require precondition n
  ensures postcondition n result
  do
  let mut i : Nat := 0
  let mut s : Nat := 0
  while i < n
    -- i stays within bounds of the range we are summing over.
    -- Init: i=0. Preserved: i increments by 1 but loop guard ensures i<n.
    invariant "inv_bounds" i ≤ n
    -- s is the partial sum of fourth powers of the first i odd numbers.
    -- Init: s=0 = sum over range 0. Preserved: we add the i-th term and then increment i.
    invariant "inv_partial_sum" s = sumFourthOdd i
    done_with (i = n)
  do
    let odd := 2 * i + 1
    let term := odd ^ 4
    s := s + term
    i := i + 1
  return s
end Impl

section TestCases
-- Test case 1: example n = 0
-- Sum over empty set = 0

def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 => 1^4 = 1

def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2 => 1^4 + 3^4 = 1 + 81 = 82

def test3_n : Nat := 2
def test3_Expected : Nat := 82

-- Test case 4: n = 3 => 1^4 + 3^4 + 5^4 = 707

def test4_n : Nat := 3
def test4_Expected : Nat := 707

-- Test case 5: n = 4 => previous + 7^4 = 3108

def test5_n : Nat := 4
def test5_Expected : Nat := 3108

-- Test case 6: n = 5 => previous + 9^4 = 9669

def test6_n : Nat := 5
def test6_Expected : Nat := 9669

-- Test case 7: n = 6 => previous + 11^4 = 24310

def test7_n : Nat := 6
def test7_Expected : Nat := 24310

-- Test case 8: n = 7 => previous + 13^4 = 52871

def test8_n : Nat := 7
def test8_Expected : Nat := 52871

-- Test case 9: n = 8 => previous + 15^4 = 103496

def test9_n : Nat := 8
def test9_Expected : Nat := 103496

-- Recommend to validate: test1, test2, test6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((sumOfFourthPowerOfOddNumbers test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for sumOfFourthPowerOfOddNumbers
prove_precondition_decidable_for sumOfFourthPowerOfOddNumbers
prove_postcondition_decidable_for sumOfFourthPowerOfOddNumbers
derive_tester_for sumOfFourthPowerOfOddNumbers
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := sumOfFourthPowerOfOddNumbersTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct sumOfFourthPowerOfOddNumbers by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (i : ℕ)
    (s : ℕ)
    (invariant_inv_bounds : i ≤ n)
    (invariant_inv_partial_sum : s = sumFourthOdd i)
    (if_pos : i < n)
    : s + (2 * i + 1) ^ 4 = sumFourthOdd (i + 1) := by
  -- replace s by the known partial sum
  subst invariant_inv_partial_sum
  -- unfold the definition and use the standard range-succ sum decomposition
  simp [sumFourthOdd, oddAt, Finset.sum_range_succ]

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    : 0 = sumFourthOdd 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2
    (n : ℕ)
    (require_1 : precondition n)
    (i : ℕ)
    (s : ℕ)
    (invariant_inv_bounds : i ≤ n)
    (invariant_inv_partial_sum : s = sumFourthOdd i)
    (done_1 : i = n)
    (i_1 : ℕ)
    (s_1 : ℕ)
    (i_2 : i = i_1 ∧ s = s_1)
    : postcondition n s_1 := by
    -- unfold the postcondition and use the invariant at loop exit
    have hs1 : s = s_1 := i_2.2
    have hsN : s = sumFourthOdd n := by
      simpa [done_1] using invariant_inv_partial_sum
    -- transfer from s to s_1
    have : s_1 = sumFourthOdd n := by
      calc
        s_1 = s := by simpa [hs1] using (rfl : s_1 = s_1)
        _ = sumFourthOdd n := hsN
    simpa [postcondition] using this


prove_correct sumOfFourthPowerOfOddNumbers by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 i s invariant_inv_bounds invariant_inv_partial_sum if_pos)
  exact (goal_1 n require_1)
  exact (goal_2 n require_1 i s invariant_inv_bounds invariant_inv_partial_sum done_1 i_1 s_1 i_2)
end Proof
