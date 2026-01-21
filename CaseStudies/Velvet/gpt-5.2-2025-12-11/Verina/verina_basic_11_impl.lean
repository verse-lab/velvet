import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. Input n is a natural number (hence non-negative by type).
    2. The last digit in base 10 is the remainder when dividing n by 10.
    3. The result must be a natural number between 0 and 9 inclusive.
    4. The returned digit must satisfy: result = n % 10.
-/

section Specs
-- Preconditions: no additional requirements because n : Nat is already non-negative.
def precondition (n : Nat) : Prop :=
  True

-- Postconditions:
-- 1) result is exactly the remainder mod 10
-- 2) result is a decimal digit (0..9), captured by result < 10
-- Note: the bound is redundant given result = n % 10, but kept for readability.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = n % 10 ∧ result < 10
end Specs

section Impl
method lastDigit (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    let d := n % 10
    return d
end Impl

section TestCases
-- Test case 1: example from prompt
-- n = 123 -> 3

def test1_n : Nat := 123
def test1_Expected : Nat := 3

-- Test case 2: n = 0 -> 0

def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: large number
-- 987654321 % 10 = 1

def test3_n : Nat := 987654321
def test3_Expected : Nat := 1

-- Test case 4: exact multiple of 10

def test4_n : Nat := 10
def test4_Expected : Nat := 0

-- Test case 5: repeated 9s

def test5_n : Nat := 999
def test5_Expected : Nat := 9

-- Test case 6: typical two-digit number

def test6_n : Nat := 45
def test6_Expected : Nat := 5

-- Test case 7: another multiple of 10

def test7_n : Nat := 100
def test7_Expected : Nat := 0

-- Test case 8: single digit remains unchanged

def test8_n : Nat := 5
def test8_Expected : Nat := 5

-- Recommend to validate: test1, test2, test4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((lastDigit test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((lastDigit test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((lastDigit test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((lastDigit test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((lastDigit test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((lastDigit test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((lastDigit test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((lastDigit test8_n).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for lastDigit
prove_precondition_decidable_for lastDigit
prove_postcondition_decidable_for lastDigit
derive_tester_for lastDigit
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := lastDigitTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct lastDigit by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    : postcondition n (n % 10) := by
    unfold postcondition
    constructor
    · rfl
    ·
      have hpos : 0 < (10 : ℕ) := by decide
      simpa using (Nat.mod_lt n hpos)


prove_correct lastDigit by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
