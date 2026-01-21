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
    sumOfDigits: compute the sum of the base-10 digits of a non-negative integer.
    Natural language breakdown:
    1. The input n is a natural number (a non-negative integer).
    2. Consider the canonical base-10 digit list of n given by Mathlib: `Nat.digits 10 n`.
       This list is in little-endian order (least-significant digit first).
    3. Each element of `Nat.digits 10 n` is a digit in the range 0..9.
    4. The output is the sum of these digits.
    5. In particular, for n = 0, the digit list is empty and the sum is 0.
    6. The result is a natural number.
-/

section Specs
-- No special precondition: input is already a Nat.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is exactly the sum of the canonical base-10 digits.
-- Using `Nat.digits` makes the specification canonical and uniquely determines the result.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (Nat.digits 10 n).sum
end Specs

section Impl
method sumOfDigits (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  let mut t := n
  let mut s : Nat := 0
  while t > 0
    -- Invariant: accumulator tracks the sum of digits already removed from `t`.
    -- Initialization: `t = n`, so removed prefix is `[]` and sum is 0.
    -- Preservation: writing `t = 10*q + r` with `r = t % 10`, `q = t / 10`, we add `r` to `s` and set `t := q`.
    -- Sufficiency: on exit `t = 0`, the removed digits are exactly `Nat.digits 10 n`, hence `s` is their sum.
    invariant "sumOfDigits_acc" s + (Nat.digits 10 t).sum = (Nat.digits 10 n).sum
  do
    let d := t % 10
    s := s + d
    t := t / 10
  return s
end Impl

section TestCases
-- Test case 1: example from prompt
-- 12345 -> 1+2+3+4+5 = 15

def test1_n : Nat := 12345
def test1_Expected : Nat := 15

-- Test case 2: zero

def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: large mixed digits

def test3_n : Nat := 987654321
def test3_Expected : Nat := 45

-- Test case 4: repeated ones

def test4_n : Nat := 11111
def test4_Expected : Nat := 5

-- Test case 5: includes zeros in the middle

def test5_n : Nat := 1001
def test5_Expected : Nat := 2

-- Test case 6: all 9s

def test6_n : Nat := 9999
def test6_Expected : Nat := 36

-- Test case 7: single digit

def test7_n : Nat := 7
def test7_Expected : Nat := 7

-- Test case 8: trailing zeros

def test8_n : Nat := 1200
def test8_Expected : Nat := 3

-- Test case 9: power of 10

def test9_n : Nat := 10000
def test9_Expected : Nat := 1

-- Recommend to validate: test1, test2, test5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((sumOfDigits test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((sumOfDigits test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((sumOfDigits test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((sumOfDigits test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((sumOfDigits test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((sumOfDigits test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((sumOfDigits test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((sumOfDigits test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((sumOfDigits test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for sumOfDigits
prove_precondition_decidable_for sumOfDigits
prove_postcondition_decidable_for sumOfDigits
derive_tester_for sumOfDigits
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := sumOfDigitsTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct sumOfDigits by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (s : ℕ)
    (t : ℕ)
    (invariant_sumOfDigits_acc : s + (Nat.digits 10 t).sum = (Nat.digits 10 n).sum)
    (if_pos : 0 < t)
    : s + t % 10 + (Nat.digits 10 (t / 10)).sum = (Nat.digits 10 n).sum := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    (s : ℕ)
    (t : ℕ)
    (invariant_sumOfDigits_acc : s + (Nat.digits 10 t).sum = (Nat.digits 10 n).sum)
    (i : ℕ)
    (t_1 : ℕ)
    (done_1 : t = 0)
    (i_1 : s = i ∧ t = t_1)
    : postcondition n i := by
    -- unfold the postcondition
    unfold postcondition
    -- extract s = i from the bookkeeping conjunction
    have hsi : s = i := i_1.left
    -- use the invariant at termination t = 0
    have hs : s = (Nat.digits 10 n).sum := by
      have := invariant_sumOfDigits_acc
      -- substitute t = 0 and simplify digits/sum
      -- Nat.digits 10 0 = [] and ([]).sum = 0, so s + 0 = ...
      simpa [done_1] using this
    -- transfer from s to i
    exact (Eq.symm hsi).trans hs


prove_correct sumOfDigits by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 s t invariant_sumOfDigits_acc if_pos)
  exact (goal_1 n require_1 s t invariant_sumOfDigits_acc i t_1 done_1 i_1)
end Proof
