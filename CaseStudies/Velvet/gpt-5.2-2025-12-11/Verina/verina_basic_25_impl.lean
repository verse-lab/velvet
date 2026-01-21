import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Batteries.Lean.Float

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumAndAverage: compute the sum and average of the first n natural numbers.
    Natural language breakdown:
    1. Input n is a natural number.
    2. The sum is the sum of all natural numbers from 0 to n inclusive.
    3. The sum satisfies Gauss' identity: 2 * sum = n * (n + 1).
    4. The output sum is returned as an Int and must be nonnegative.
    5. The average is a Float intended to represent sum / n.
    6. Although the narrative says n is positive, the tests include n = 0.
    7. For n = 0, the output is defined by the tests as (0, 0.0).
    8. For n > 0, the average is defined using Float division of the converted sum by Float.ofNat n.
-/

section Specs
-- Helper: closed-form Gauss sum as a Nat (this is specification-level, non-recursive).
-- We use Nat arithmetic; for n=0 this yields 0.
def gaussSumNat (n : Nat) : Nat :=
  n * (n + 1) / 2

-- Precondition: allow all n to match provided tests (including n = 0).
def precondition (n : Nat) : Prop :=
  True

-- Postcondition:
-- 1) result.1 is exactly the Gauss sum (as an Int).
-- 2) result.2 is the average:
--    - if n = 0, it is 0.0 (per tests)
--    - if n > 0, it is Float.ofInt result.1 / Float.ofNat n
-- This fully determines the output for every n.
def postcondition (n : Nat) (result : Int × Float) : Prop :=
  result.1 = Int.ofNat (gaussSumNat n) ∧
  (n = 0 → result.2 = 0.0) ∧
  (n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n))
end Specs

section Impl
method sumAndAverage (n: Nat) return (result: Int × Float)
  require precondition n
  ensures postcondition n result
  do
    let sumNat : Nat := gaussSumNat n
    let sumInt : Int := Int.ofNat sumNat

    if n = 0 then
      return (sumInt, 0.0)
    else
      let avg : Float := (Float.ofInt sumInt) / (Float.ofNat n)
      return (sumInt, avg)
end Impl

section TestCases
-- Test case 1: example from prompt: n = 5
-- Sum 0..5 = 15, average = 15/5 = 3.0

def test1_n : Nat := 5

def test1_Expected : Int × Float := (15, 3.0)

-- Test case 2: n = 1
-- Sum 0..1 = 1, average = 1/1 = 1.0

def test2_n : Nat := 1

def test2_Expected : Int × Float := (1, 1.0)

-- Test case 3: n = 10
-- Sum 0..10 = 55, average = 55/10 = 5.5

def test3_n : Nat := 10

def test3_Expected : Int × Float := (55, 5.5)

-- Test case 4: edge case from prompt: n = 0
-- By the tests: sum = 0 and average = 0.0

def test4_n : Nat := 0

def test4_Expected : Int × Float := (0, 0.0)

-- Test case 5: n = 2
-- Sum 0..2 = 3, average = 3/2 = 1.5

def test5_n : Nat := 2

def test5_Expected : Int × Float := (3, 1.5)

-- Additional representative cases (not in the original provided list)

-- Test case 6: n = 3
-- Sum = 6, average = 2.0

def test6_n : Nat := 3

def test6_Expected : Int × Float := (6, 2.0)

-- Test case 7: n = 4
-- Sum = 10, average = 2.5

def test7_n : Nat := 4

def test7_Expected : Int × Float := (10, 2.5)

-- Test case 8: n = 6
-- Sum = 21, average = 3.5

def test8_n : Nat := 6

def test8_Expected : Int × Float := (21, 3.5)

-- Test case 9: n = 8
-- Sum = 36, average = 4.5

def test9_n : Nat := 8

def test9_Expected : Int × Float := (36, 4.5)

-- Recommend to validate: test1, test4, test5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((sumAndAverage test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((sumAndAverage test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((sumAndAverage test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((sumAndAverage test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((sumAndAverage test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((sumAndAverage test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((sumAndAverage test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((sumAndAverage test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((sumAndAverage test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 169, Column 0
-- Message: unsolved goals
-- case refine_2.refine_1
-- n : ℕ
-- result : ℤ × Float
-- ⊢ Decidable (n = 0 → result.2 = 0.0)
-- 
-- case refine_2.refine_2
-- n : ℕ
-- result : ℤ × Float
-- ⊢ Decidable (n > 0 → result.2 = Float.ofInt result.1 / Float.ofNat n)
-- Line: prove_postcondition_decidable_for sumAndAverage
-- [ERROR] Line 171, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for sumAndAverage
-- prove_precondition_decidable_for sumAndAverage
-- prove_postcondition_decidable_for sumAndAverage
-- derive_tester_for sumAndAverage
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
--     let res := sumAndAverageTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct sumAndAverage by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (if_pos : n = 0)
    : postcondition n (↑(gaussSumNat n), 0.0) := by
  unfold postcondition
  constructor
  · rfl
  · constructor
    · intro _
      rfl
    · intro hn
      have : False := by
        -- rewrite `n` to `0` in `hn`, getting `0 > 0`, which is impossible
        simpa [if_pos] using hn
      exact this.elim

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    (if_neg : ¬n = 0)
    : postcondition n (↑(gaussSumNat n), Float.ofInt ↑(gaussSumNat n) / Float.ofNat n) := by
  unfold postcondition
  constructor
  · rfl
  constructor
  · intro h
    exact (if_neg h).elim
  · intro hn
    simp


prove_correct sumAndAverage by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 if_pos)
  exact (goal_1 n require_1 if_neg)
end Proof
