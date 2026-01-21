import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumOfSquaresOfFirstNOddNumbers: Sum of squares of the first n odd natural numbers.
    Natural language breakdown:
    1. The input n is a natural number, so it is non-negative.
    2. The first n odd natural numbers are 1, 3, 5, ..., (2*n - 1).
    3. The desired output is the sum of the squares of these n odd numbers.
    4. The result must match the closed-form value (n * (2*n - 1) * (2*n + 1)) / 3.
    5. The function is total: it must accept any n : Nat.
-/

section Specs
-- Helper: the numerator of the closed-form expression.
-- We keep this as a separate definition to improve readability.
def oddSquaresClosedFormNumerator (n : Nat) : Nat :=
  n * (2 * n - 1) * (2 * n + 1)

-- Precondition: none (the problem statement allows all Nat inputs).
def precondition (n : Nat) : Prop :=
  True

-- Postcondition:
-- The result is the natural-number division by 3 of the closed-form numerator.
-- Note: We avoid specifying the Finset sum (a reference implementation) and
-- we also avoid unavailable Mathlib imports.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = oddSquaresClosedFormNumerator n / 3
end Specs

section Impl
method sumOfSquaresOfFirstNOddNumbers (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    let num := oddSquaresClosedFormNumerator n
    let res := num / 3
    return res
end Impl

section TestCases
-- Test case 1: n = 0 (example from the provided tests)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 -> 1
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2 -> 10
def test3_n : Nat := 2
def test3_Expected : Nat := 10

-- Test case 4: n = 3 -> 35
def test4_n : Nat := 3
def test4_Expected : Nat := 35

-- Test case 5: n = 4 -> 84
def test5_n : Nat := 4
def test5_Expected : Nat := 84

-- Test case 6: n = 5 -> 165
def test6_n : Nat := 5
def test6_Expected : Nat := 165

-- Test case 7: n = 10 -> 1330
def test7_n : Nat := 10
def test7_Expected : Nat := 1330

-- Test case 8: additional mid-size sanity check: n = 6 -> 286
def test8_n : Nat := 6
def test8_Expected : Nat := 286

-- Test case 9: another check: n = 7 -> 455
def test9_n : Nat := 7
def test9_Expected : Nat := 455

-- Recommend to validate: test1, test3, test7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((sumOfSquaresOfFirstNOddNumbers test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for sumOfSquaresOfFirstNOddNumbers
prove_precondition_decidable_for sumOfSquaresOfFirstNOddNumbers
prove_postcondition_decidable_for sumOfSquaresOfFirstNOddNumbers
derive_tester_for sumOfSquaresOfFirstNOddNumbers
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := sumOfSquaresOfFirstNOddNumbersTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct sumOfSquaresOfFirstNOddNumbers by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (n : ℕ)
    (require_1 : precondition n) : postcondition n (oddSquaresClosedFormNumerator n / 3) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


prove_correct sumOfSquaresOfFirstNOddNumbers by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
