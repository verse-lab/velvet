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
    isPrime: Determine whether a given natural number is prime.
    Natural language breakdown:
    1. The input is a natural number n, and the task assumes n ≥ 2.
    2. A natural number n is prime iff it has no divisor k with 1 < k < n.
    3. Equivalently: n is prime iff for every k with 1 < k < n, k does not divide n.
    4. The method returns a Bool: true exactly when n is prime, and false otherwise.
    5. Inputs that violate n ≥ 2 are outside the intended domain.
-/

section Specs
-- Helper predicate: "n has a nontrivial divisor"
-- This matches the problem statement directly and avoids relying on any particular algorithm.
def HasNontrivialDivisor (n : Nat) : Prop :=
  ∃ k : Nat, 1 < k ∧ k < n ∧ k ∣ n

-- Precondition: input is expected to satisfy n ≥ 2.
def precondition (n : Nat) : Prop :=
  2 ≤ n

-- Postcondition: result is true iff there is no nontrivial divisor.
-- This uniquely determines the Bool output.
def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ ¬ HasNontrivialDivisor n
end Specs

section Impl
method isPrime (n : Nat) return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  -- Brute-force check for any divisor k with 2 ≤ k < n.
  -- If we find one, n is composite.
  let mut k : Nat := 2
  let mut composite : Bool := false
  while k < n ∧ composite = false
    -- Invariant: k stays within bounds; needed for modular reasoning and to show progress.
    -- Initialization: k = 2 and precondition gives 2 ≤ n, so k ≤ n.
    -- Preservation: k only increases by 1 when composite stays false; otherwise k unchanged.
    invariant "inv_bounds" (2 ≤ k ∧ k ≤ n)
    -- Invariant: when we mark composite, we have actually found a nontrivial divisor of n.
    -- Initialization: composite = false, so vacuously true.
    -- Preservation: the only assignment setting composite := true happens under guard n % k = 0,
    -- giving witness k; k < n follows from loop guard k < n.
    invariant "inv_composite_witness" (composite = true → ∃ d : Nat, 1 < d ∧ d < n ∧ d ∣ n)
    -- Invariant: if we have not marked composite yet, then no nontrivial divisor has been found
    -- among all candidates in [2, k).
    -- Initialization: k = 2 makes the range empty.
    -- Preservation: when n % k ≠ 0, we increment k, extending the checked range by one.
    -- If n % k = 0, we set composite := true, so antecedent composite = false is false.
    invariant "inv_checked" (composite = false → ∀ d : Nat, 2 ≤ d ∧ d < k → n % d ≠ 0)
    done_with (k = n ∨ composite = true)
  do
    if n % k = 0 then
      composite := true
    else
      k := k + 1
  if composite = true then
    return false
  else
    return true
end Impl

section TestCases
-- Test case 1: n = 2 (smallest prime; example from prompt)
def test1_n : Nat := 2
def test1_Expected : Bool := true

-- Test case 2: n = 3 (prime)
def test2_n : Nat := 3
def test2_Expected : Bool := true

-- Test case 3: n = 4 (composite)
def test3_n : Nat := 4
def test3_Expected : Bool := false

-- Test case 4: n = 5 (prime)
def test4_n : Nat := 5
def test4_Expected : Bool := true

-- Test case 5: n = 9 (composite square)
def test5_n : Nat := 9
def test5_Expected : Bool := false

-- Test case 6: n = 11 (prime)
def test6_n : Nat := 11
def test6_Expected : Bool := true

-- Test case 7: n = 12 (composite even)
def test7_n : Nat := 12
def test7_Expected : Bool := false

-- Test case 8: n = 13 (prime)
def test8_n : Nat := 13
def test8_Expected : Bool := true

-- Reject input example (outside precondition): n = 0
-- This is not a test with expected output because it violates precondition.
def reject1_n : Nat := 0

-- Recommend to validate: 1, 3, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isPrime test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isPrime test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isPrime test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isPrime test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isPrime test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isPrime test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isPrime test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isPrime test8_n).run), DivM.res test8_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 138, Column 0
-- Message: unsolved goals
-- n : ℕ
-- result : Bool
-- ⊢ Decidable (postcondition n result)
-- Line: prove_postcondition_decidable_for isPrime
-- [ERROR] Line 140, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for isPrime
-- prove_precondition_decidable_for isPrime
-- prove_postcondition_decidable_for isPrime
-- derive_tester_for isPrime
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
--     let res := isPrimeTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isPrime by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (composite : Bool)
    (k : ℕ)
    (a : 2 ≤ k)
    (a_1 : k ≤ n)
    (invariant_inv_composite_witness : composite = true → ∃ d, 1 < d ∧ d < n ∧ d ∣ n)
    (invariant_inv_checked : composite = false → ∀ (d : ℕ), 2 ≤ d → d < k → ¬n % d = 0)
    (a_2 : k < n)
    (a_3 : composite = false)
    (if_pos : n % k = 0)
    : ∃ d, 1 < d ∧ d < n ∧ d ∣ n := by
    refine ⟨k, ?_, a_2, ?_⟩
    · exact lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) a
    · exact Nat.dvd_of_mod_eq_zero if_pos

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    (composite : Bool)
    (k : ℕ)
    (a : 2 ≤ k)
    (a_1 : k ≤ n)
    (invariant_inv_composite_witness : composite = true → ∃ d, 1 < d ∧ d < n ∧ d ∣ n)
    (invariant_inv_checked : composite = false → ∀ (d : ℕ), 2 ≤ d → d < k → ¬n % d = 0)
    (if_neg : k < n → composite = true)
    : composite = true → ∃ d, 1 < d ∧ d < n ∧ d ∣ n := by
    intros; expose_names; exact (invariant_inv_composite_witness h); done

theorem goal_2
    (n : ℕ)
    (require_1 : precondition n)
    : 2 ≤ n := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_3
    (n : ℕ)
    (require_1 : precondition n)
    (composite : Bool)
    (k : ℕ)
    (a : 2 ≤ k)
    (a_1 : k ≤ n)
    (invariant_inv_composite_witness : composite = true → ∃ d, 1 < d ∧ d < n ∧ d ∣ n)
    (invariant_inv_checked : composite = false → ∀ (d : ℕ), 2 ≤ d → d < k → ¬n % d = 0)
    (done_1 : k = n ∨ composite = true)
    (i : Bool)
    (k_1 : ℕ)
    (if_pos : i = true)
    (i_1 : composite = i ∧ k = k_1)
    : postcondition n false := by
    unfold postcondition
    -- derive `composite = true` from bookkeeping equalities
    have hcomp : composite = true := by
      calc
        composite = i := i_1.1
        _ = true := if_pos
    have hdiv : HasNontrivialDivisor n := by
      rcases invariant_inv_composite_witness hcomp with ⟨d, hd⟩
      exact ⟨d, hd⟩
    constructor
    · intro h
      -- from false = true, anything follows
      cases h
    · intro hnot
      -- contradiction with the divisor witness
      exfalso
      exact hnot hdiv

theorem goal_4
    (n : ℕ)
    (require_1 : precondition n)
    (composite : Bool)
    (k : ℕ)
    (a : 2 ≤ k)
    (a_1 : k ≤ n)
    (invariant_inv_composite_witness : composite = true → ∃ d, 1 < d ∧ d < n ∧ d ∣ n)
    (invariant_inv_checked : composite = false → ∀ (d : ℕ), 2 ≤ d → d < k → ¬n % d = 0)
    (done_1 : k = n ∨ composite = true)
    (i : Bool)
    (k_1 : ℕ)
    (i_1 : composite = i ∧ k = k_1)
    (if_neg : i = false)
    : postcondition n true := by
    unfold postcondition
    simp
    -- reduce to proving: ¬ HasNontrivialDivisor n
    have hcompFalse : composite = false := by
      -- composite = i and i = false
      exact Eq.trans i_1.1 if_neg
    have hk : k = n := by
      cases done_1 with
      | inl hkn => exact hkn
      | inr hct =>
          exfalso
          -- contradiction: composite = true and composite = false
          exact Bool.noConfusion (hcompFalse.symm.trans hct)
    -- now show no nontrivial divisor exists
    intro hHas
    rcases hHas with ⟨d, hd1, hdlt, hddvd⟩
    have hd2 : 2 ≤ d := by
      exact Nat.succ_le_of_lt hd1
    have hdltk : d < k := by
      -- rewrite hk : k = n
      simpa [hk] using hdlt
    have hmodne : ¬ n % d = 0 := by
      exact invariant_inv_checked hcompFalse d hd2 hdltk
    have hmodeq : n % d = 0 := by
      exact Nat.mod_eq_zero_of_dvd hddvd
    exact hmodne hmodeq


prove_correct isPrime by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 composite k a a_1 invariant_inv_composite_witness invariant_inv_checked a_2 a_3 if_pos)
  exact (goal_1 n require_1 composite k a a_1 invariant_inv_composite_witness invariant_inv_checked if_neg)
  exact (goal_2 n require_1)
  exact (goal_3 n require_1 composite k a a_1 invariant_inv_composite_witness invariant_inv_checked done_1 i k_1 if_pos i_1)
  exact (goal_4 n require_1 composite k a a_1 invariant_inv_composite_witness invariant_inv_checked done_1 i k_1 i_1 if_neg)
end Proof
