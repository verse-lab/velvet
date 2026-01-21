import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isDivisibleBy11: Determine whether a given integer is divisible by 11
    Natural language breakdown:
    1. We have an input integer n
    2. An integer n is divisible by 11 if and only if there exists an integer k such that n = 11 * k
    3. Equivalently, n is divisible by 11 if and only if n % 11 = 0
    4. The method should return true if n is divisible by 11
    5. The method should return false if n is not divisible by 11
    6. Zero is divisible by 11 (0 = 11 * 0)
    7. Negative integers can also be divisible by 11 (e.g., -11, -22)
    8. The divisibility relation is symmetric under negation

    Property-oriented specification:
    - We use the built-in divisibility predicate from Lean: 11 ∣ n
    - This means: there exists an integer c such that n = 11 * c
    - The result should be true if and only if 11 divides n
-/

section Specs

-- Use Lean's built-in divisibility predicate for integers
-- 11 ∣ n means: ∃ c, n = 11 * c

def precondition (n : Int) :=
  True  -- no preconditions

@[loomAbstractionSimp]
def postcondition (n : Int) (result : Bool) :=
  result = true ↔ (11 : Int) ∣ n

end Specs

section Impl

method isDivisibleBy11 (n: Int)
  return (result: Bool)
  require precondition n
  ensures postcondition n result
  do
  let remainder := n % 11
  if remainder = 0 then
    return true
  else
    return false

end Impl

section TestCases

-- Test case 1: Zero is divisible by 11
def test1_n : Int := 0
def test1_Expected : Bool := true

-- Test case 2: 11 is divisible by 11
def test2_n : Int := 11
def test2_Expected : Bool := true

-- Test case 3: 22 is divisible by 11
def test3_n : Int := 22
def test3_Expected : Bool := true

-- Test case 4: 23 is not divisible by 11
def test4_n : Int := 23
def test4_Expected : Bool := false

-- Test case 5: 33 is divisible by 11
def test5_n : Int := 33
def test5_Expected : Bool := true

-- Test case 6: -11 is divisible by 11
def test6_n : Int := -11
def test6_Expected : Bool := true

-- Test case 7: -22 is divisible by 11
def test7_n : Int := -22
def test7_Expected : Bool := true

-- Test case 8: 1 is not divisible by 11
def test8_n : Int := 1
def test8_Expected : Bool := false

-- Test case 9: -1 is not divisible by 11
def test9_n : Int := -1
def test9_Expected : Bool := false

-- Test case 10: 121 is divisible by 11 (11 * 11)
def test10_n : Int := 121
def test10_Expected : Bool := true

-- Recommend to validate: 1, 2, 4

end TestCases

section Assertions

-- Test case 1

#assert_same_evaluation #[((isDivisibleBy11 test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isDivisibleBy11 test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isDivisibleBy11 test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isDivisibleBy11 test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isDivisibleBy11 test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isDivisibleBy11 test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isDivisibleBy11 test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isDivisibleBy11 test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isDivisibleBy11 test9_n).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isDivisibleBy11 test10_n).run), DivM.res test10_Expected ]

end Assertions

section Pbt

extract_program_for isDivisibleBy11
prove_precondition_decidable_for isDivisibleBy11
prove_postcondition_decidable_for isDivisibleBy11
derive_tester_for isDivisibleBy11
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let res := isDivisibleBy11Tester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    

end Pbt

section Proof

-- prove_correct isDivisibleBy11 by
--   loom_solve <;> (try simp at *; expose_names)


theorem goal_0 (n : ℤ)
    (require_1 : precondition n)
    (if_pos : n % 11 = 0) : postcondition n true := by
  unfold postcondition
  simp only [true_iff]
  exact Int.dvd_of_emod_eq_zero if_pos


theorem goal_1 (n : ℤ)
    (require_1 : precondition n)
    (if_neg : ¬n % 11 = 0) : postcondition n false := by
  unfold postcondition
  simp only [Bool.false_eq_true, false_iff]
  intro h
  apply if_neg
  exact Int.emod_eq_zero_of_dvd h



prove_correct isDivisibleBy11 by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 if_pos)
  exact (goal_1 n require_1 if_neg)

end Proof
