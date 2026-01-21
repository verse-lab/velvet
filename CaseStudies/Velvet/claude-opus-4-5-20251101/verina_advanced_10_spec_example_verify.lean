import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def allPrimes (primes : List Nat) : Prop :=
  ∀ p, p ∈ primes → Nat.Prime p

def firsts (pairs : List (Nat × Nat)) : List Nat :=
  pairs.map (fun ⟨p, _⟩ => p)

def allPrimeFactorsIn (n : Nat) (primes : List Nat) : Prop :=
  ∀ p, Nat.Prime p → p ∣ n → p ∈ primes



def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes.length > 0 ∧
  allPrimes primes ∧
  primes.Nodup ∧
  allPrimeFactorsIn n primes






def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : Prop :=
  result.length = primes.length ∧
  firsts result = primes ∧
  (∀ i : Nat, i < result.length → (result[i]!.2 = Nat.factorization n (result[i]!.1)))


def test1_n : Nat := 6

def test1_primes : List Nat := [2, 3]

def test1_Expected : List (Nat × Nat) := [(2, 1), (3, 1)]

def test3_n : Nat := 360

def test3_primes : List Nat := [2, 3, 5]

def test3_Expected : List (Nat × Nat) := [(2, 3), (3, 2), (5, 1)]

def test8_n : Nat := 1

def test8_primes : List Nat := [2, 3]

def test8_Expected : List (Nat × Nat) := [(2, 0), (3, 0)]







section Proof
theorem test1_precondition :
  precondition test1_n test1_primes := by
  unfold precondition test1_n test1_primes
  constructor
  · -- 6 > 0
    decide
  constructor
  · -- [2, 3].length > 0
    decide
  constructor
  · -- allPrimes [2, 3]
    unfold allPrimes
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  constructor
  · -- [2, 3].Nodup
    rw [List.nodup_cons]
    constructor
    · simp
    · rw [List.nodup_cons]
      constructor
      · simp
      · exact List.nodup_nil
  · -- allPrimeFactorsIn 6 [2, 3]
    unfold allPrimeFactorsIn
    intro p hp hdvd
    simp
    -- p is prime and divides 6 = 2 * 3
    have h6 : (6 : Nat) = 2 * 3 := by decide
    rw [h6] at hdvd
    have := (Nat.Prime.dvd_mul hp).mp hdvd
    rcases this with h2 | h3
    · -- p divides 2
      have : p = 1 ∨ p = 2 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p h2
      rcases this with rfl | rfl
      · exact absurd hp Nat.not_prime_one
      · left; rfl
    · -- p divides 3
      have : p = 1 ∨ p = 3 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three p h3
      rcases this with rfl | rfl
      · exact absurd hp Nat.not_prime_one
      · right; rfl

theorem test1_postcondition :
  postcondition test1_n test1_primes test1_Expected := by
  unfold postcondition test1_n test1_primes test1_Expected
  constructor
  · -- result.length = primes.length
    native_decide
  constructor
  · -- firsts result = primes
    unfold firsts
    native_decide
  · -- factorization condition
    intro i hi
    simp only [List.length] at hi
    interval_cases i
    · -- i = 0: need (2, 1)[0]!.2 = Nat.factorization 6 (2, 1)[0]!.1
      native_decide
    · -- i = 1: need (3, 1)[1]!.2 = Nat.factorization 6 (3, 1)[1]!.1
      native_decide

theorem test3_precondition :
  precondition test3_n test3_primes := by
  unfold precondition test3_n test3_primes
  constructor
  · -- 360 > 0
    decide
  constructor
  · -- [2, 3, 5].length > 0
    decide
  constructor
  · -- allPrimes [2, 3, 5]
    unfold allPrimes
    intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  constructor
  · -- [2, 3, 5].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    decide
  · -- allPrimeFactorsIn 360 [2, 3, 5]
    unfold allPrimeFactorsIn
    intro p hp hdvd
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    -- 360 = 8 * 45 = 8 * 9 * 5 = 2^3 * 3^2 * 5
    have h360 : (360 : Nat) = 2^3 * 3^2 * 5 := by native_decide
    rw [h360] at hdvd
    have hdvd1 : p ∣ 2^3 * 3^2 * 5 := hdvd
    -- Use that p is prime to determine which factor it divides
    have h1 : p ∣ 2^3 * 3^2 ∨ p ∣ 5 := (Nat.Prime.dvd_mul hp).mp hdvd1
    rcases h1 with h1 | h1
    · have h2 : p ∣ 2^3 ∨ p ∣ 3^2 := (Nat.Prime.dvd_mul hp).mp h1
      rcases h2 with h2 | h2
      · have h3 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp h2
        left
        have : p = 2 := (Nat.dvd_prime Nat.prime_two).mp h3 |>.resolve_left hp.ne_one
        exact this
      · have h3 : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp h2
        right; left
        have : p = 3 := (Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left hp.ne_one
        exact this
    · right; right
      have : p = 5 := (Nat.dvd_prime Nat.prime_five).mp h1 |>.resolve_left hp.ne_one
      exact this

theorem test3_postcondition :
  postcondition test3_n test3_primes test3_Expected := by
  unfold postcondition test3_n test3_primes test3_Expected
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> native_decide

theorem test8_precondition :
  precondition test8_n test8_primes := by
  unfold precondition test8_n test8_primes
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1 > 0
    decide
  · -- [2, 3].length > 0
    decide
  · -- allPrimes [2, 3]
    unfold allPrimes
    intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    cases hp with
    | inl h => rw [h]; exact Nat.prime_two
    | inr h => rw [h]; exact Nat.prime_three
  · -- [2, 3].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
               List.nodup_nil, and_true, not_false_eq_true]
    decide
  · -- allPrimeFactorsIn 1 [2, 3]
    unfold allPrimeFactorsIn
    intro p hp hdvd
    exfalso
    exact Nat.Prime.not_dvd_one hp hdvd

theorem test8_postcondition :
  postcondition test8_n test8_primes test8_Expected := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · intro i hi
    simp only [test8_Expected, test8_n, test8_primes] at hi ⊢
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => simp only [List.length_cons, List.length_nil] at hi; omega

theorem uniqueness_0
    (n : ℕ)
    (primes : List ℕ)
    (hpre : precondition n primes)
    (ret1 : List (ℕ × ℕ))
    (ret2 : List (ℕ × ℕ))
    (hpost1 : postcondition n primes ret1)
    (hpost2 : postcondition n primes ret2)
    (hlen1 : ret1.length = primes.length)
    (hfirsts1 : firsts ret1 = primes)
    (hlen2 : ret2.length = primes.length)
    (hfirsts2 : firsts ret2 = primes)
    (hfact1 : ∀ i < ret1.length, (ret1[i]?.getD default).2 = n.factorization (ret1[i]?.getD default).1)
    (hfact2 : ∀ i < ret2.length, (ret2[i]?.getD default).2 = n.factorization (ret2[i]?.getD default).1)
    : ret1.length = ret2.length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_1
    (n : ℕ)
    (primes : List ℕ)
    (hpre : precondition n primes)
    (ret1 : List (ℕ × ℕ))
    (ret2 : List (ℕ × ℕ))
    (hpost1 : postcondition n primes ret1)
    (hpost2 : postcondition n primes ret2)
    (hlen1 : ret1.length = primes.length)
    (hfirsts1 : firsts ret1 = primes)
    (hlen2 : ret2.length = primes.length)
    (hfirsts2 : firsts ret2 = primes)
    (hlen_eq : ret1.length = ret2.length)
    (hfact1 : ∀ i < ret1.length, (ret1[i]?.getD default).2 = n.factorization (ret1[i]?.getD default).1)
    (hfact2 : ∀ i < ret2.length, (ret2[i]?.getD default).2 = n.factorization (ret2[i]?.getD default).1)
    : firsts ret1 = firsts ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2
    (n : ℕ)
    (primes : List ℕ)
    (hpre : precondition n primes)
    (ret1 : List (ℕ × ℕ))
    (ret2 : List (ℕ × ℕ))
    (hpost1 : postcondition n primes ret1)
    (hpost2 : postcondition n primes ret2)
    (hlen1 : ret1.length = primes.length)
    (hfirsts1 : firsts ret1 = primes)
    (hlen2 : ret2.length = primes.length)
    (hfirsts2 : firsts ret2 = primes)
    (hlen_eq : ret1.length = ret2.length)
    (hfirsts_eq : firsts ret1 = firsts ret2)
    (hfact1 : ∀ i < ret1.length, (ret1[i]?.getD default).2 = n.factorization (ret1[i]?.getD default).1)
    (hfact2 : ∀ i < ret2.length, (ret2[i]?.getD default).2 = n.factorization (ret2[i]?.getD default).1)
    : ∀ (i : ℕ) (h1 : i < ret1.length) (h2 : i < ret2.length), ret1[i].1 = ret2[i].1 := by
    intro i h1 h2
    -- firsts extracts first components via map
    unfold firsts at hfirsts_eq
    -- hfirsts_eq : ret1.map (fun ⟨p, _⟩ => p) = ret2.map (fun ⟨p, _⟩ => p)
    -- The mapping function is essentially Prod.fst
    have hmapped1 : (ret1.map (fun ⟨p, _⟩ => p))[i]'(by simp; exact h1) = ret1[i].1 := by
      rw [List.getElem_map]
      simp
    have hmapped2 : (ret2.map (fun ⟨p, _⟩ => p))[i]'(by simp; exact h2) = ret2[i].1 := by
      rw [List.getElem_map]
      simp
    -- From hfirsts_eq, the elements at index i are equal
    have hlen_mapped : (ret1.map (fun ⟨p, _⟩ => p)).length = (ret2.map (fun ⟨p, _⟩ => p)).length := by
      simp [hlen_eq]
    have hi_bound1 : i < (ret1.map (fun ⟨p, _⟩ => p)).length := by simp; exact h1
    have hi_bound2 : i < (ret2.map (fun ⟨p, _⟩ => p)).length := by simp; exact h2
    have heq_at_i : (ret1.map (fun ⟨p, _⟩ => p))[i]'hi_bound1 = (ret2.map (fun ⟨p, _⟩ => p))[i]'hi_bound2 := by
      have : (ret1.map (fun ⟨p, _⟩ => p))[i]'hi_bound1 = (ret2.map (fun ⟨p, _⟩ => p))[i]'(hfirsts_eq ▸ hi_bound1) := by
        exact List.getElem_of_eq hfirsts_eq hi_bound1
      convert this using 1
    rw [hmapped1, hmapped2] at heq_at_i
    exact heq_at_i

theorem uniqueness_3
    (n : ℕ)
    (primes : List ℕ)
    (hpre : precondition n primes)
    (ret1 : List (ℕ × ℕ))
    (ret2 : List (ℕ × ℕ))
    (hpost1 : postcondition n primes ret1)
    (hpost2 : postcondition n primes ret2)
    (hlen1 : ret1.length = primes.length)
    (hfirsts1 : firsts ret1 = primes)
    (hlen2 : ret2.length = primes.length)
    (hfirsts2 : firsts ret2 = primes)
    (hlen_eq : ret1.length = ret2.length)
    (hfirsts_eq : firsts ret1 = firsts ret2)
    (hfst_eq : ∀ (i : ℕ) (h1 : i < ret1.length) (h2 : i < ret2.length), ret1[i].1 = ret2[i].1)
    (hfact1 : ∀ i < ret1.length, (ret1[i]?.getD default).2 = n.factorization (ret1[i]?.getD default).1)
    (hfact2 : ∀ i < ret2.length, (ret2[i]?.getD default).2 = n.factorization (ret2[i]?.getD default).1)
    : ∀ (i : ℕ) (h1 : i < ret1.length) (h2 : i < ret2.length), ret1[i].2 = ret2[i].2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (n : Nat) (primes : List Nat):
  precondition n primes →
  (∀ ret1 ret2,
    postcondition n primes ret1 →
    postcondition n primes ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract postcondition components for ret1
  have hlen1 : ret1.length = primes.length := hpost1.1
  have hfirsts1 : firsts ret1 = primes := hpost1.2.1
  have hfact1 : ∀ i : Nat, i < ret1.length → (ret1[i]!.2 = Nat.factorization n (ret1[i]!.1)) := hpost1.2.2
  -- Extract postcondition components for ret2
  have hlen2 : ret2.length = primes.length := hpost2.1
  have hfirsts2 : firsts ret2 = primes := hpost2.2.1
  have hfact2 : ∀ i : Nat, i < ret2.length → (ret2[i]!.2 = Nat.factorization n (ret2[i]!.1)) := hpost2.2.2
  -- The two results have equal length
  have hlen_eq : ret1.length = ret2.length := by (try simp at *; expose_names); exact (uniqueness_0 n primes hpre ret1 ret2 hpost1 hpost2 hlen1 hfirsts1 hlen2 hfirsts2 hfact1 hfact2); done
  -- firsts ret1 = firsts ret2
  have hfirsts_eq : firsts ret1 = firsts ret2 := by (try simp at *; expose_names); exact (uniqueness_1 n primes hpre ret1 ret2 hpost1 hpost2 hlen1 hfirsts1 hlen2 hfirsts2 hlen_eq hfact1 hfact2); done
  -- For any index i, the first components are equal
  have hfst_eq : ∀ i (h1 : i < ret1.length) (h2 : i < ret2.length), ret1[i].1 = ret2[i].1 := by (try simp at *; expose_names); exact (uniqueness_2 n primes hpre ret1 ret2 hpost1 hpost2 hlen1 hfirsts1 hlen2 hfirsts2 hlen_eq hfirsts_eq hfact1 hfact2); done
  -- For any index i, the second components are equal
  have hsnd_eq : ∀ i (h1 : i < ret1.length) (h2 : i < ret2.length), ret1[i].2 = ret2[i].2 := by (try simp at *; expose_names); exact (uniqueness_3 n primes hpre ret1 ret2 hpost1 hpost2 hlen1 hfirsts1 hlen2 hfirsts2 hlen_eq hfirsts_eq hfst_eq hfact1 hfact2); done
  -- For any index i, the pairs are equal
  have hpair_eq : ∀ i (h1 : i < ret1.length) (h2 : i < ret2.length), ret1[i] = ret2[i] := by (try simp at *; expose_names); exact (fun i h1 h2 ↦ Prod.ext (hfst_eq i h1 h2) (hsnd_eq i h1 h2)); done
  -- Use List.ext_getElem to conclude ret1 = ret2
  exact List.ext_getElem hlen_eq hpair_eq
end Proof
