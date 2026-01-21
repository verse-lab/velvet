import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Defs

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- findExponents: Decompose a natural number n into its prime factorization components
-- Natural language breakdown:
-- 1. Given a positive natural number n and a non-empty list of distinct primes
-- 2. n can be expressed as a product of powers of the given primes: n = ∏ p^e
-- 3. We need to find the exponent e for each prime p in the input list
-- 4. The output is a list of pairs (p, e) where p is a prime from the input and e is its exponent
-- 5. Every prime in the input list must appear in the output
-- 6. The primes in output should correspond to the input primes in order
-- 7. The exponent of a prime p in n is the p-adic valuation (how many times p divides n)
-- 8. Preconditions:
--    - n > 0 (positive number)
--    - primes is non-empty
--    - all elements in primes are prime numbers
--    - primes list has no duplicates
--    - n must be fully factorizable by the given primes (all prime factors of n are in the list)

section Specs
-- Helper: check if all elements in a list are prime
def allPrimes (primes : List Nat) : Prop :=
  ∀ p, p ∈ primes → Nat.Prime p

-- Helper: extract the first components of pairs
def firsts (pairs : List (Nat × Nat)) : List Nat :=
  pairs.map (fun ⟨p, _⟩ => p)

-- Helper: check if all prime factors of n are in the given list
def allPrimeFactorsIn (n : Nat) (primes : List Nat) : Prop :=
  ∀ p, Nat.Prime p → p ∣ n → p ∈ primes

-- Precondition: n is positive, primes is non-empty, all are prime, distinct, and n is fully factorizable
def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes.length > 0 ∧
  allPrimes primes ∧
  primes.Nodup ∧
  allPrimeFactorsIn n primes

-- Postcondition:
-- 1. The result has the same length as the input primes list
-- 2. The primes in the result match the input primes in order
-- 3. For each pair (p, e) in result, e is the p-adic valuation of n
def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : Prop :=
  result.length = primes.length ∧
  firsts result = primes ∧
  (∀ i : Nat, i < result.length → (result[i]!.2 = Nat.factorization n (result[i]!.1)))
end Specs

section Impl
method findExponents (n : Nat) (primes : List Nat)
  return (result : List (Nat × Nat))
  require precondition n primes
  ensures postcondition n primes result
  do
  let mut result : List (Nat × Nat) := []
  let mut i := 0
  let primesLen := primes.length

  while i < primesLen
    -- Invariant 1: i is bounded by primesLen
    invariant "i_bounds" 0 ≤ i ∧ i ≤ primesLen
    -- Invariant 2: result length matches i
    invariant "result_length" result.length = i
    -- Invariant 3: primesLen equals primes.length
    invariant "primesLen_eq" primesLen = primes.length
    -- Invariant 4: the first components of result match the first i primes
    invariant "firsts_match" firsts result = primes.take i
    -- Invariant 5: each exponent in result is the correct p-adic valuation
    invariant "exponents_correct" ∀ j : Nat, j < result.length → (result[j]!.2 = Nat.factorization n (result[j]!.1))
    done_with i = primesLen
  do
    let p := primes[i]!
    -- Compute the p-adic valuation: count how many times p divides n
    let mut exp := 0
    let mut temp := n
    while temp % p = 0 ∧ temp > 0 ∧ p > 1
      -- Invariant: temp is positive
      invariant "temp_pos" temp > 0
      -- Invariant: p is the current prime (greater than 1)
      invariant "p_gt_1" p > 1
      -- Invariant: key relationship - n = temp * p^exp
      invariant "valuation_relation" n = temp * p ^ exp
      done_with ¬(temp % p = 0 ∧ temp > 0 ∧ p > 1)
    do
      temp := temp / p
      exp := exp + 1
    result := result ++ [(p, exp)]
    i := i + 1

  return result
end Impl

section TestCases
-- Test case 1: n = 6 with primes [2, 3] (example from problem)
def test1_n : Nat := 6
def test1_primes : List Nat := [2, 3]
def test1_Expected : List (Nat × Nat) := [(2, 1), (3, 1)]

-- Test case 2: Large number with primes [2, 3, 5]
def test2_n : Nat := 6285195213566005335561053533150026217291776
def test2_primes : List Nat := [2, 3, 5]
def test2_Expected : List (Nat × Nat) := [(2, 55), (3, 55), (5, 0)]

-- Test case 3: n = 360 with primes [2, 3, 5]
def test3_n : Nat := 360
def test3_primes : List Nat := [2, 3, 5]
def test3_Expected : List (Nat × Nat) := [(2, 3), (3, 2), (5, 1)]

-- Test case 4: n = 18903812908 with primes [2, 43, 823, 133543]
def test4_n : Nat := 18903812908
def test4_primes : List Nat := [2, 43, 823, 133543]
def test4_Expected : List (Nat × Nat) := [(2, 2), (43, 1), (823, 1), (133543, 1)]

-- Test case 5: n = 114514 with primes [2, 31, 1847]
def test5_n : Nat := 114514
def test5_primes : List Nat := [2, 31, 1847]
def test5_Expected : List (Nat × Nat) := [(2, 1), (31, 1), (1847, 1)]

-- Test case 6: n = 20241147794175 with primes [3, 5, 7, 11, 31, 47]
def test6_n : Nat := 20241147794175
def test6_primes : List Nat := [3, 5, 7, 11, 31, 47]
def test6_Expected : List (Nat × Nat) := [(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (47, 3)]

-- Test case 7: Power of a single prime n = 32 = 2^5
def test7_n : Nat := 32
def test7_primes : List Nat := [2]
def test7_Expected : List (Nat × Nat) := [(2, 5)]

-- Test case 8: n = 1 (edge case - no prime divides 1, all exponents are 0)
def test8_n : Nat := 1
def test8_primes : List Nat := [2, 3]
def test8_Expected : List (Nat × Nat) := [(2, 0), (3, 0)]

-- Recommend to validate: 1, 3, 8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findExponents test1_n test1_primes).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findExponents test2_n test2_primes).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findExponents test3_n test3_primes).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findExponents test4_n test4_primes).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findExponents test5_n test5_primes).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findExponents test6_n test6_primes).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findExponents test7_n test7_primes).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findExponents test8_n test8_primes).run), DivM.res test8_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 170, Column 0
-- Message: unsolved goals
-- case refine_2.refine_2.refine_2.refine_2
-- n : ℕ
-- primes : List ℕ
-- ⊢ Decidable (allPrimeFactorsIn n primes)
-- Line: prove_precondition_decidable_for findExponents
-- [ERROR] Line 173, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
--
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for findExponents
-- prove_precondition_decidable_for findExponents
-- prove_postcondition_decidable_for findExponents
-- derive_tester_for findExponents
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
--     let arg_1 ← Plausible.SampleableExt.interpSample (List Nat)
--     let res := findExponentsTester arg_0 arg_1
--     pure ((arg_0, arg_1), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break

end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct findExponents by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (a_2 : temp % primes[i]?.getD 0 = 0)
    (a_3 : 0 < temp)
    (a_4 : 1 < primes[i]?.getD 0)
    : 0 < primes[i]?.getD 0 ∧ primes[i]?.getD 0 ≤ temp := by
    constructor
    · omega
    · exact Nat.le_of_dvd a_3 (Nat.dvd_of_mod_eq_zero a_2)

theorem goal_1
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (a_2 : temp % primes[i]?.getD 0 = 0)
    (a_3 : 0 < temp)
    (a_4 : 1 < primes[i]?.getD 0)
    : n = temp / primes[i]?.getD 0 * primes[i]?.getD 0 ^ (exp + 1) := by
    let p := primes[i]?.getD 0
    have hp_dvd : p ∣ temp := Nat.dvd_of_mod_eq_zero a_2
    have div_mul_eq : temp / p * p = temp := Nat.div_mul_cancel hp_dvd
    have pow_expand : p ^ (exp + 1) = p * p ^ exp := Nat.pow_succ'
    calc n = temp * p ^ exp := invariant_valuation_relation
      _ = (temp / p * p) * p ^ exp := by rw [div_mul_eq]
      _ = temp / p * p * p ^ exp := by rfl
      _ = temp / p * (p * p ^ exp) := by rw [Nat.mul_assoc]
      _ = temp / p * p ^ (exp + 1) := by rw [← pow_expand]

theorem goal_2
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    : 0 < n := by
    unfold precondition at require_1
    exact require_1.1

theorem goal_3
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    : 1 < primes[i]?.getD 0 := by
    -- Extract allPrimes from precondition
    have h_allPrimes : allPrimes primes := require_1.2.2.1
    -- When i < primes.length, primes[i]? = some primes[i]
    have h_getElem : primes[i]? = some primes[i] := List.getElem?_eq_getElem if_pos
    -- So primes[i]?.getD 0 = primes[i]
    have h_getD : primes[i]?.getD 0 = primes[i] := by
      rw [h_getElem]
      exact Option.getD_some
    -- primes[i] is in primes
    have h_mem : primes[i] ∈ primes := List.getElem_mem if_pos
    -- By allPrimes, primes[i] is prime
    have h_prime : Nat.Prime primes[i] := h_allPrimes primes[i] h_mem
    -- Prime implies > 1
    rw [h_getD]
    exact Nat.Prime.one_lt h_prime

theorem goal_4
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    : firsts (result ++ [(primes[i]?.getD 0, i_1)]) = List.take (i + 1) primes := by
    unfold firsts at *
    rw [List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [invariant_firsts_match]
    rw [List.take_succ]
    congr 1
    simp only [List.getElem?_eq_getElem if_pos, Option.toList_some]
    rfl

theorem goal_5_0
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    (h_exp_eq : exp = i_1)
    : primes[i]?.getD 0 = primes[i] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_5_1
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    (h_exp_eq : exp = i_1)
    (h_p_def : primes[i]?.getD 0 = primes[i])
    (h_allPrimes : allPrimes primes)
    (h_p_mem : True)
    : Nat.Prime (primes[i]?.getD 0) := by
    rw [h_p_def]
    have h_mem : primes[i] ∈ primes := List.getElem_mem if_pos
    exact h_allPrimes primes[i] h_mem

theorem goal_5_2
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    (h_exp_eq : exp = i_1)
    (h_p_def : primes[i]?.getD 0 = primes[i])
    (h_allPrimes : allPrimes primes)
    (h_p_prime : Nat.Prime (primes[i]?.getD 0))
    (h_p_mem : True)
    : ¬primes[i]?.getD 0 ∣ temp := by
    intro h_dvd
    have h_mod_zero : temp % primes[i]?.getD 0 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
    have h_p_le_1 : primes[i]?.getD 0 ≤ 1 := done_2 h_mod_zero invariant_temp_pos
    omega

theorem goal_5_3
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    (h_exp_eq : exp = i_1)
    (h_p_def : primes[i]?.getD 0 = primes[i])
    (h_allPrimes : allPrimes primes)
    (h_p_prime : Nat.Prime (primes[i]?.getD 0))
    (h_not_dvd : ¬primes[i]?.getD 0 ∣ temp)
    (h_temp_ne_zero : ¬temp = 0)
    (h_p_pos : 0 < primes[i]?.getD 0)
    (h_p_mem : True)
    (h_n_pos : 0 < n)
    : primes[i]?.getD 0 = 0 → exp = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_5_4
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    (h_exp_eq : exp = i_1)
    (h_p_def : primes[i]?.getD 0 = primes[i])
    (h_allPrimes : allPrimes primes)
    (h_p_prime : Nat.Prime (primes[i]?.getD 0))
    (h_not_dvd : ¬primes[i]?.getD 0 ∣ temp)
    (h_temp_ne_zero : ¬temp = 0)
    (h_p_pos : 0 < primes[i]?.getD 0)
    (h_temp_fact_zero : temp.factorization (primes[i]?.getD 0) = 0)
    (h_p_mem : True)
    (h_n_pos : 0 < n)
    (h_pow_ne_zero : primes[i]?.getD 0 = 0 → exp = 0)
    : n.factorization (primes[i]?.getD 0) = exp := by
    let p := primes[i]?.getD 0
    have h_pow_ne_zero' : p ^ exp ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos h_p_pos)
    have h_temp_ne_zero' : temp ≠ 0 := h_temp_ne_zero
    rw [invariant_valuation_relation]
    rw [Nat.factorization_mul h_temp_ne_zero' h_pow_ne_zero']
    rw [Finsupp.add_apply]
    rw [h_temp_fact_zero]
    rw [Nat.Prime.factorization_pow h_p_prime]
    simp only [Finsupp.single_eq_same, Nat.zero_add]

theorem goal_5_5
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    (h_exp_eq : exp = i_1)
    (h_p_def : primes[i]?.getD 0 = primes[i])
    (h_allPrimes : allPrimes primes)
    (h_p_prime : Nat.Prime (primes[i]?.getD 0))
    (h_not_dvd : ¬primes[i]?.getD 0 ∣ temp)
    (h_temp_ne_zero : ¬temp = 0)
    (h_p_pos : 0 < primes[i]?.getD 0)
    (h_temp_fact_zero : temp.factorization (primes[i]?.getD 0) = 0)
    (h_factorization_eq : n.factorization (primes[i]?.getD 0) = exp)
    (h_p_mem : True)
    (h_n_pos : 0 < n)
    (h_pow_ne_zero : primes[i]?.getD 0 = 0 → exp = 0)
    : i_1 = n.factorization (primes[i]?.getD 0) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_5
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (if_pos : i < primes.length)
    (exp : ℕ)
    (temp : ℕ)
    (i_1 : ℕ)
    (temp_1 : ℕ)
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (invariant_temp_pos : 0 < temp)
    (invariant_p_gt_1 : 1 < primes[i]?.getD 0)
    (invariant_valuation_relation : n = temp * primes[i]?.getD 0 ^ exp)
    (done_2 : temp % primes[i]?.getD 0 = 0 → 0 < temp → primes[i]?.getD 0 ≤ 1)
    (i_2 : exp = i_1 ∧ temp = temp_1)
    : ∀ j < result.length + 1, ((result ++ [(primes[i]?.getD 0, i_1)])[j]?.getD default).2 = n.factorization ((result ++ [(primes[i]?.getD 0, i_1)])[j]?.getD default).1 := by
    have h_exp_eq : exp = i_1 := i_2.1
    have h_p_def : primes[i]?.getD 0 = primes[i] := by (try simp at *; expose_names); exact (goal_5_0 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2 h_exp_eq); done
    have h_p_mem : primes[i] ∈ primes := List.getElem_mem if_pos
    have h_allPrimes : allPrimes primes := require_1.2.2.1
    have h_p_prime : Nat.Prime (primes[i]?.getD 0) := by (try simp at *; expose_names); exact (goal_5_1 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2 h_exp_eq h_p_def h_allPrimes h_p_mem); done
    have h_not_dvd : ¬(primes[i]?.getD 0 ∣ temp) := by (try simp at *; expose_names); exact (goal_5_2 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2 h_exp_eq h_p_def h_allPrimes h_p_prime h_p_mem); done
    have h_n_pos : n > 0 := require_1.1
    have h_temp_ne_zero : temp ≠ 0 := Nat.pos_iff_ne_zero.mp invariant_temp_pos
    have h_p_pos : 0 < primes[i]?.getD 0 := by (try simp at *; expose_names); exact (Nat.zero_lt_of_lt invariant_p_gt_1); done
    have h_pow_ne_zero : primes[i]?.getD 0 ^ exp ≠ 0 := by (try simp at *; expose_names); exact (goal_5_3 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2 h_exp_eq h_p_def h_allPrimes h_p_prime h_not_dvd h_temp_ne_zero h_p_pos h_p_mem h_n_pos); done
    have h_temp_fact_zero : temp.factorization (primes[i]?.getD 0) = 0 := by (try simp at *; expose_names); exact (Nat.factorization_eq_zero_of_not_dvd h_not_dvd); done
    have h_factorization_eq : n.factorization (primes[i]?.getD 0) = exp := by (try simp at *; expose_names); exact (goal_5_4 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2 h_exp_eq h_p_def h_allPrimes h_p_prime h_not_dvd h_temp_ne_zero h_p_pos h_temp_fact_zero h_p_mem h_n_pos h_pow_ne_zero); done
    have h_new_elem_correct : i_1 = n.factorization (primes[i]?.getD 0) := by (try simp at *; expose_names); exact (goal_5_5 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2 h_exp_eq h_p_def h_allPrimes h_p_prime h_not_dvd h_temp_ne_zero h_p_pos h_temp_fact_zero h_factorization_eq h_p_mem h_n_pos h_pow_ne_zero); done
    intro j hj
    by_cases h_j_lt : j < result.length
    · have h_access_left : (result ++ [(primes[i]?.getD 0, i_1)])[j]? = result[j]? := List.getElem?_append_left h_j_lt
      simp only [h_access_left]
      exact invariant_exponents_correct j h_j_lt
    · have h_j_eq : j = result.length := by (try simp at *; expose_names); exact (Nat.eq_of_le_of_lt_succ h_j_lt hj); done
      have h_access_right : (result ++ [(primes[i]?.getD 0, i_1)])[j]? = [(primes[i]?.getD 0, i_1)][j - result.length]? := List.getElem?_append_right (by omega)
      subst h_j_eq
      simp only [Nat.sub_self] at h_access_right
      simp only [List.getElem?_singleton, ↓reduceIte] at h_access_right
      simp only [h_access_right, Option.getD_some]
      exact h_new_elem_correct

theorem goal_6
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    : firsts [] = [] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_7
    (n : ℕ)
    (primes : List ℕ)
    (require_1 : precondition n primes)
    (i : ℕ)
    (result : List (ℕ × ℕ))
    (a_1 : i ≤ primes.length)
    (invariant_result_length : result.length = i)
    (invariant_firsts_match : firsts result = List.take i primes)
    (done_1 : i = primes.length)
    (i_1 : ℕ)
    (result_1 : List (ℕ × ℕ))
    (a : True)
    (invariant_exponents_correct : ∀ j < result.length, (result[j]?.getD default).2 = n.factorization (result[j]?.getD default).1)
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition n primes result_1 := by
    unfold postcondition
    obtain ⟨hi_eq, hresult_eq⟩ := i_2
    subst hresult_eq hi_eq
    constructor
    · -- result.length = primes.length
      omega
    constructor
    · -- firsts result = primes
      rw [invariant_firsts_match, done_1, List.take_length]
    · -- ∀ i < result.length, result[i]!.2 = n.factorization result[i]!.1
      intro j hj
      have h_inv := invariant_exponents_correct j hj
      have h_valid : j < result.length := hj
      rw [invariant_result_length] at h_valid
      have h_getElem_eq : result[j]? = some result[j] := List.getElem?_eq_getElem (by omega : j < result.length)
      simp only [h_getElem_eq, Option.getD_some] at h_inv
      have h_bang_eq : result[j]! = result[j] := by
        rw [List.getElem!_of_getElem? h_getElem_eq]
      rw [h_bang_eq]
      exact h_inv


prove_correct findExponents by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation a_2 a_3 a_4)
  exact (goal_1 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation a_2 a_3 a_4)
  exact (goal_2 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos a invariant_exponents_correct)
  exact (goal_3 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos a invariant_exponents_correct)
  exact (goal_4 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2)
  exact (goal_5 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match if_pos exp temp i_1 temp_1 a invariant_exponents_correct invariant_temp_pos invariant_p_gt_1 invariant_valuation_relation done_2 i_2)
  exact (goal_6 n primes require_1)
  exact (goal_7 n primes require_1 i result a_1 invariant_result_length invariant_firsts_match done_1 i_1 result_1 a invariant_exponents_correct i_2)
end Proof
