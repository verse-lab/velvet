import CaseStudies.Velvet.Std

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

-- Helper function to compute the sum of digits of a natural number
-- This is a standard mathematical concept that requires recursion
def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)

section Impl
method countSumDivisibleBy (n : Nat) (d : Nat)
  return (result : Nat)
  require d > 0
  ensures result = (Finset.filter (fun k => d ∣ digitSum k) (Finset.range n)).card
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

attribute [grind] Finset.range_succ Finset.filter_insert Nat.dvd_iff_mod_eq_zero

prove_correct countSumDivisibleBy by
  loom_solve
