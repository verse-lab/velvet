import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    countSumDivisibleBy: Count numbers smaller than n whose digit sum is divisible by d
    Natural language breakdown:
    1. Given a natural number n and a divisor d (where d > 0)
    2. For each number k in the range [0, n), compute the sum of its digits
    3. Check if this digit sum is divisible by d
    4. Count how many such numbers satisfy this divisibility condition
    5. The digit sum of a number is the sum of all its decimal digits
       - e.g., digitSum(123) = 1 + 2 + 3 = 6
    6. A number's digit sum is divisible by d if d ∣ digitSum(k)
    7. Edge cases:
       - n = 0: no numbers to check, result is 0
       - n = 1: only check 0, digitSum(0) = 0, d ∣ 0 always, so result is 1
       - d = 1: all digit sums are divisible by 1, result is n
-/

section Specs
register_specdef_allow_recursion

-- Helper function to compute the sum of digits of a natural number
-- This is a standard mathematical concept that requires recursion
def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)

-- Precondition: d must be positive
def precondition (n : Nat) (d : Nat) : Prop :=
  d > 0

-- Postcondition: result equals the cardinality of the set of numbers in [0, n)
-- whose digit sum is divisible by d
-- Using Finset.filter and Finset.range for a property-based specification
def postcondition (n : Nat) (d : Nat) (result : Nat) : Prop :=
  result = (Finset.filter (fun k => d ∣ digitSum k) (Finset.range n)).card
end Specs

section Impl
method countSumDivisibleBy (n : Nat) (d : Nat)
  return (result : Nat)
  require precondition n d
  ensures postcondition n d result
  do
  let mut count := 0
  let mut k := 0
  while k < n
    -- Invariant 1: k is bounded by n
    -- Init: k starts at 0, so 0 ≤ k ≤ n holds
    -- Preservation: k increments by 1 each iteration, loop guard ensures k < n before increment, so k+1 ≤ n
    -- Sufficiency: when k = n, we've processed all numbers in [0, n)
    invariant "k_bounds" 0 ≤ k ∧ k ≤ n
    -- Invariant 2: count equals the number of integers in [0, k) with digit sum divisible by d
    -- Init: k = 0, count = 0, Finset.range 0 is empty so card is 0
    -- Preservation: if digitSum k divisible by d, count increases by 1, matching the filter including k
    -- Sufficiency: at k = n, count = card of filter over [0, n) = postcondition
    invariant "count_correct" count = (Finset.filter (fun i => d ∣ digitSum i) (Finset.range k)).card
    done_with k = n
  do
    let sum := digitSum k
    if sum % d = 0 then
      count := count + 1
    k := k + 1
  return count
end Impl

section TestCases
-- Test case 1: n = 0, d = 2 - no numbers to check
def test1_n : Nat := 0
def test1_d : Nat := 2
def test1_Expected : Nat := 0

-- Test case 2: n = 1, d = 2 - only 0, digitSum(0) = 0, divisible by 2
def test2_n : Nat := 1
def test2_d : Nat := 2
def test2_Expected : Nat := 1

-- Test case 3: n = 10, d = 3 - check 0-9, digitSums divisible by 3: 0, 3, 6, 9
def test3_n : Nat := 10
def test3_d : Nat := 3
def test3_Expected : Nat := 4

-- Test case 4: n = 12, d = 2 - check 0-11
-- digitSums: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2
-- divisible by 2: 0, 2, 4, 6, 8, 11 (positions with even digit sums) = 6
def test4_n : Nat := 12
def test4_d : Nat := 2
def test4_Expected : Nat := 6

-- Test case 5: n = 20, d = 5 - check 0-19
-- Numbers with digit sum divisible by 5: 0 (sum=0), 5 (sum=5), 14 (sum=5), 19 (sum=10)
def test5_n : Nat := 20
def test5_d : Nat := 5
def test5_Expected : Nat := 4

-- Test case 6: n = 5, d = 1 - all digit sums divisible by 1
def test6_n : Nat := 5
def test6_d : Nat := 1
def test6_Expected : Nat := 5

-- Test case 7: n = 100, d = 9 - checking larger range
-- Numbers 0-99 with digit sum divisible by 9: 0, 9, 18, 27, 36, 45, 54, 63, 72, 81, 90, 99 = 12
def test7_n : Nat := 100
def test7_d : Nat := 9
def test7_Expected : Nat := 12

-- Test case 8: n = 15, d = 7
-- digitSums: 0,1,2,3,4,5,6,7,8,9,1,2,3,4,5
-- divisible by 7: 0 (sum=0), 7 (sum=7) = 2
def test8_n : Nat := 15
def test8_d : Nat := 7
def test8_Expected : Nat := 2

-- Recommend to validate: 1, 2, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((countSumDivisibleBy test1_n test1_d).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((countSumDivisibleBy test2_n test2_d).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((countSumDivisibleBy test3_n test3_d).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((countSumDivisibleBy test4_n test4_d).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((countSumDivisibleBy test5_n test5_d).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((countSumDivisibleBy test6_n test6_d).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((countSumDivisibleBy test7_n test7_d).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((countSumDivisibleBy test8_n test8_d).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for countSumDivisibleBy
prove_precondition_decidable_for countSumDivisibleBy
prove_postcondition_decidable_for countSumDivisibleBy
derive_tester_for countSumDivisibleBy
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let arg_1 ← Plausible.SampleableExt.interpSample (Nat)
    let res := countSumDivisibleByTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct countSumDivisibleBy by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (d : ℕ)
    (require_1 : precondition n d)
    (count : ℕ)
    (k : ℕ)
    (a_1 : k ≤ n)
    (invariant_count_correct : count = {i ∈ Finset.range k | d ∣ digitSum i}.card)
    (if_pos : k < n)
    (if_pos_1 : digitSum k % d = 0)
    (a : True)
    : count + 1 = {i ∈ Finset.range (k + 1) | d ∣ digitSum i}.card := by
    -- Convert digitSum k % d = 0 to d ∣ digitSum k
    have hdvd : d ∣ digitSum k := Nat.dvd_of_mod_eq_zero if_pos_1
    -- Rewrite range (k + 1) as insert k (range k)
    rw [Finset.range_succ]
    -- Rewrite filter of insert when predicate holds
    rw [Finset.filter_insert]
    -- Since d ∣ digitSum k, the if-then-else simplifies
    simp only [hdvd, ↓reduceIte]
    -- k is not in range k
    have hnotmem : k ∉ Finset.range k := Finset.not_mem_range_self
    -- k is not in the filtered set (since filter is a subset)
    have hnotmem_filter : k ∉ Finset.filter (fun i => d ∣ digitSum i) (Finset.range k) := by
      intro hmem
      have hmem_range := Finset.mem_of_mem_filter k hmem
      exact hnotmem hmem_range
    -- Use card_insert_of_not_mem
    rw [Finset.card_insert_of_not_mem hnotmem_filter]
    -- Now we have count + 1 = card + 1, and count = card from invariant
    rw [invariant_count_correct]

theorem goal_1
    (n : ℕ)
    (d : ℕ)
    (require_1 : precondition n d)
    (count : ℕ)
    (k : ℕ)
    (a_1 : k ≤ n)
    (invariant_count_correct : count = {i ∈ Finset.range k | d ∣ digitSum i}.card)
    (if_pos : k < n)
    (if_neg : ¬digitSum k % d = 0)
    (a : True)
    : count = {i ∈ Finset.range (k + 1) | d ∣ digitSum i}.card := by
    -- First, convert the negation of mod to negation of divisibility
    have h_not_dvd : ¬(d ∣ digitSum k) := by
      intro h_dvd
      have : digitSum k % d = 0 := Nat.dvd_iff_mod_eq_zero.mp h_dvd
      exact if_neg this
    -- Rewrite range (k + 1) as insert k (range k)
    have h_range : Finset.range (k + 1) = insert k (Finset.range k) := by
      exact Finset.range_succ
    -- Rewrite the RHS using h_range
    rw [h_range]
    -- Use filter_insert lemma
    rw [Finset.filter_insert]
    -- Since the predicate is false for k, the if simplifies
    simp only [h_not_dvd, ite_false]
    -- Now we just need the invariant
    exact invariant_count_correct

theorem goal_2
    (n : ℕ)
    (d : ℕ)
    (require_1 : precondition n d)
    (count : ℕ)
    (k : ℕ)
    (a_1 : k ≤ n)
    (invariant_count_correct : count = {i ∈ Finset.range k | d ∣ digitSum i}.card)
    (done_1 : k = n)
    (i : ℕ)
    (k_1 : ℕ)
    (a : True)
    (i_1 : count = i ∧ k = k_1)
    : postcondition n d i := by
    unfold postcondition
    have h1 : count = i := i_1.1
    rw [done_1] at invariant_count_correct
    rw [← h1]
    exact invariant_count_correct


prove_correct countSumDivisibleBy by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n d require_1 count k a_1 invariant_count_correct if_pos if_pos_1 a)
  exact (goal_1 n d require_1 count k a_1 invariant_count_correct if_pos if_neg a)
  exact (goal_2 n d require_1 count k a_1 invariant_count_correct done_1 i k_1 a i_1)
end Proof
