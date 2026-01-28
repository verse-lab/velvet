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
