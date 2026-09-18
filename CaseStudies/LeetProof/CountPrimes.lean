module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Prime.Basic

/-!
## Program description

Count Primes: given a non-negative integer `n`, return the number of prime numbers strictly less than `n`.

The program is expected to run in O(n log log n) time and O(n) space.
-/

namespace CountPrimes

section Specs

public def primeSetBelow (n : Nat) : Finset Nat :=
  (Finset.range n).filter Nat.Prime

public def precondition (_n : Nat) : Prop :=
  True

public def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (primeSetBelow n).card ∧
  result ≤ n

end Specs

section Implementation

method countPrimes (n : Nat)
  returns (result : Nat)
  requires valid: precondition n
  ensures count_correct: postcondition n result
do
  if small: n ≤ 2 then
    return 0
  else
    let mut isPrime : Array Bool := Array.replicate n true
    isPrime := isPrime.set! 0 false
    isPrime := isPrime.set! 1 false

    let mut p : Nat := 2
    while' outer: p * p < n
      invariant cp_outer_size: isPrime.size = n
      invariant cp_outer_p_bounds: 2 ≤ p ∧ p ≤ n
      invariant cp_outer_zero_one: isPrime[0]! = false ∧ isPrime[1]! = false
      invariant cp_outer_sound: ∀ m, m < n → isPrime[m]! = false → ¬ Nat.Prime m
      invariant cp_outer_marked: ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false
      decreasing outer_remaining: n - p
      done_with outer_done: ∀ m, m < n → (isPrime[m]! = true ↔ Nat.Prime m)
    do
      if is_p_prime: isPrime[p]! then
        let mut k : Nat := p * p
        while' inner: k < n
          invariant cp_inner_size: isPrime.size = n
          invariant cp_inner_p_bounds: 2 ≤ p ∧ p ≤ n
          invariant cp_inner_k_lower: p * p ≤ k
          invariant cp_inner_k_dvd: p ∣ k
          invariant cp_inner_zero_one: isPrime[0]! = false ∧ isPrime[1]! = false
          invariant cp_inner_sound: ∀ m, m < n → isPrime[m]! = false → ¬ Nat.Prime m
          invariant cp_inner_marked_lt_p: ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false
          invariant cp_inner_marked_p: ∀ m, m < k → p * p ≤ m → p ∣ m → isPrime[m]! = false
          decreasing inner_remaining: n - k
          done_with inner_done: ∀ m, m < n → p * p ≤ m → p ∣ m → isPrime[m]! = false
        do
          isPrime := isPrime.set! k false
          k := k + p
      p := p + 1

    let mut count : Nat := 0
    let mut i : Nat := 0
    while' counting: i < n
      invariant cp_count_size: isPrime.size = n
      invariant cp_count_i_le: i ≤ n
      invariant cp_count_sieve_correct: ∀ m, m < n → (isPrime[m]! = true ↔ Nat.Prime m)
      invariant cp_count_count_eq: count = (primeSetBelow i).card
      invariant cp_count_count_le: count ≤ i
      decreasing count_remaining: n - i
      done_with count_done: i = n
    do
      if is_i_prime: isPrime[i]! then
        count := count + 1
      i := i + 1

    return count

end Implementation

section Proof

theorem primeSetBelow_empty_of_le_two (n : Nat) (hn : n ≤ 2) : primeSetBelow n = ∅ := by
  unfold primeSetBelow
  rw [Finset.filter_eq_empty_iff]
  intro x hx
  rw [Finset.mem_range] at hx
  intro hxprime
  have : 2 ≤ x := hxprime.two_le
  omega

theorem postcondition_of_le_two (n : Nat) (hn : n ≤ 2) : postcondition n 0 := by
  unfold postcondition
  rw [primeSetBelow_empty_of_le_two n hn, Finset.card_empty]
  exact ⟨rfl, Nat.zero_le n⟩

theorem primeSetBelow_card_le (i : Nat) : (primeSetBelow i).card ≤ i := by
  unfold primeSetBelow
  have h := Finset.card_filter_le (Finset.range i) Nat.Prime
  simpa using h

theorem init_sound (n : Nat) :
    ∀ m, m < n → (((Array.replicate n true).set! 0 false).set! 1 false)[m]! = false → ¬ Nat.Prime m := by
  intro m _hm hfalse
  by_cases hm0 : m = 0
  · subst hm0
    exact Nat.not_prime_zero
  · by_cases hm1 : m = 1
    · subst hm1
      exact Nat.not_prime_one
    · have h0 : m ≠ 0 := hm0
      have h1 : m ≠ 1 := hm1
      have htrue : (((Array.replicate n true).set! 0 false).set! 1 false)[m]! = true := by
        rw [Array.getElem!_set!_ne _ 1 m false (Ne.symm h1)]
        rw [Array.getElem!_set!_ne _ 0 m false (Ne.symm h0)]
        rw [getElem!_pos (Array.replicate n true) m (by simpa)]
        simp
      rw [htrue] at hfalse
      contradiction

theorem init_marked (n : Nat) :
    ∀ d m, Nat.Prime d → d < 2 → m < n → d * d ≤ m → d ∣ m →
      (((Array.replicate n true).set! 0 false).set! 1 false)[m]! = false := by
  intro d _m hdPrime hdlt2 _ _ _
  have : 2 ≤ d := hdPrime.two_le
  omega

theorem inner_step_sound (isPrime : Array Bool) (p k : Nat) (_hp2 : 2 ≤ p)
    (hk_lower : p * p ≤ k) (hk_dvd : p ∣ k)
    (hsound : ∀ m, m < isPrime.size → isPrime[m]! = false → ¬ Nat.Prime m) :
    ∀ m, m < isPrime.size → (isPrime.set! k false)[m]! = false → ¬ Nat.Prime m := by
  intro m hm hfalse
  by_cases hmk : m = k
  · subst m
    intro hkPrime
    have hp1 : 1 < p := by omega
    have hp_lt_pp : p < p * p := by
      have : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp1 (by omega)
      simpa using this
    have hp_lt_k : p < k := lt_of_lt_of_le hp_lt_pp hk_lower
    have hdiv := Nat.Prime.eq_one_or_self_of_dvd hkPrime p hk_dvd
    rcases hdiv with h1 | hself
    · omega
    · omega
  · have hne : k ≠ m := Ne.symm hmk
    rw [Array.getElem!_set!_ne isPrime k m false hne] at hfalse
    exact hsound m hm hfalse

theorem inner_step_marked_p (isPrime : Array Bool) (p k : Nat)
    (hk_bound : k < isPrime.size) (hk_dvd : p ∣ k)
    (hmarked : ∀ m, m < k → p * p ≤ m → p ∣ m → isPrime[m]! = false) :
    ∀ m, m < k + p → p * p ≤ m → p ∣ m → (isPrime.set! k false)[m]! = false := by
  intro m hm hm_lower hm_dvd
  by_cases hmk : m < k
  · have hfalse : isPrime[m]! = false := hmarked m hmk hm_lower hm_dvd
    have hne : k ≠ m := Nat.ne_of_gt hmk
    rw [Array.getElem!_set!_ne isPrime k m false hne]
    exact hfalse
  · have hkm : k ≤ m := by omega
    have hsub_lt : m - k < p := by omega
    have hdiff_dvd : p ∣ m - k := Nat.dvd_sub hm_dvd hk_dvd
    have hdiff0 : m - k = 0 := Nat.eq_zero_of_dvd_of_lt hdiff_dvd hsub_lt
    have hmeq : m = k := by omega
    rw [hmeq]
    exact Array.getElem!_set!_self isPrime k false hk_bound

theorem outer_step_marked_of_not_prime (isPrime : Array Bool) (n p : Nat)
    (_hp_sq : p * p < n)
    (hsound : ∀ m, m < n → isPrime[m]! = false → ¬ Nat.Prime m)
    (hmarked : ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false)
    (hp_false : isPrime[p]! = false) :
    ∀ d m, Nat.Prime d → d < p + 1 → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false := by
  intro d m hdPrime hdlt hm hdd hdvd
  have hdle : d ≤ p := by omega
  by_cases hdp : d < p
  · exact hmarked d m hdPrime hdp hm hdd hdvd
  · have hdeq : d = p := by omega
    subst d
    have hp_lt_n : p < n := by
      have : p ≤ p * p := Nat.le_mul_self p
      omega
    have hnprime : ¬ Nat.Prime p := hsound p hp_lt_n hp_false
    exact absurd hdPrime hnprime

theorem outer_step_marked_of_inner_done (isPrime : Array Bool) (n p : Nat)
    (hmarked_lt : ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false)
    (hmarked_p : ∀ m, m < n → p * p ≤ m → p ∣ m → isPrime[m]! = false) :
    ∀ d m, Nat.Prime d → d < p + 1 → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false := by
  intro d m hdPrime hdlt hm hdd hdvd
  have hdle : d ≤ p := by omega
  by_cases hdp : d < p
  · exact hmarked_lt d m hdPrime hdp hm hdd hdvd
  · have hdeq : d = p := by omega
    subst hdeq
    exact hmarked_p m hm hdd hdvd

theorem outer_done_sieve_correct (isPrime : Array Bool) (n p : Nat)
    (hzero : isPrime[0]! = false) (hone : isPrime[1]! = false)
    (hsound : ∀ m, m < n → isPrime[m]! = false → ¬ Nat.Prime m)
    (hmarked : ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false)
    (_hp_sq : n ≤ p * p) :
    ∀ m, m < n → (isPrime[m]! = true ↔ Nat.Prime m) := by
  intro m hm
  cases m with
  | zero =>
    simp [hzero, Nat.not_prime_zero]
  | succ m =>
    cases m with
    | zero =>
      simp [hone, Nat.not_prime_one]
    | succ m =>
      let x := m + 2
      constructor
      · intro ht
        by_contra hnprime
        have hx_pos : 0 < x := by omega
        have hx_ne1 : x ≠ 1 := by omega
        let d := Nat.minFac x
        have hdprime : Nat.Prime d := Nat.minFac_prime hx_ne1
        have hdvd : d ∣ x := Nat.minFac_dvd x
        have hdd_sq : d ^ 2 ≤ x := Nat.minFac_sq_le_self hx_pos hnprime
        have hdd : d * d ≤ x := by
          have : d ^ 2 = d * d := sq d
          omega
        have hdd_lt : d * d < p * p := lt_of_le_of_lt hdd (by omega)
        have hdlt : d < p := by
          by_contra hge
          have hp_le_d : p ≤ d := by omega
          have hp2_le_d2 : p * p ≤ d * d := Nat.mul_le_mul hp_le_d hp_le_d
          omega
        have hmark : isPrime[x]! = false := hmarked d x hdprime hdlt hm hdd hdvd
        rw [hmark] at ht
        contradiction
      · intro hprime
        by_contra _hf
        have hfalse : isPrime[x]! = false := by
          cases hget : isPrime[x]!
          · rfl
          · contradiction
        have hnprime := hsound x hm hfalse
        exact hnprime hprime

theorem count_step_prime (i : Nat) (hprime : Nat.Prime i) :
    (primeSetBelow i).card + 1 = (primeSetBelow (i + 1)).card := by
  unfold primeSetBelow
  have hnotmem : i ∉ (Finset.range i).filter Nat.Prime := by
    simp [Finset.mem_filter, Finset.mem_range]
  have hfilter : (Finset.range (i + 1)).filter Nat.Prime =
      insert i ((Finset.range i).filter Nat.Prime) := by
    rw [Finset.range_add_one, Finset.filter_insert]
    simp [hprime]
  rw [hfilter, Finset.card_insert_of_notMem hnotmem]

theorem count_step_not_prime (i : Nat) (hnot : ¬ Nat.Prime i) :
    (primeSetBelow i).card = (primeSetBelow (i + 1)).card := by
  unfold primeSetBelow
  rw [Finset.range_add_one, Finset.filter_insert]
  simp [hnot]

prove_correct countPrimes by
  velvet_vcgen [countPrimes, postcondition] with try finish
  all_goals try exact postcondition_of_le_two _ small
  all_goals try exact init_sound _
  all_goals try exact init_marked _
  all_goals try {
    simp
  }
  all_goals try exact outer_done_sieve_correct isPrime _ p cp_outer_zero_one.1 cp_outer_zero_one.2 cp_outer_sound cp_outer_marked (by omega)
  all_goals try {
    have hk_bound : k < isPrime.size := by omega
    exact inner_step_marked_p isPrime p k hk_bound cp_inner_k_dvd cp_inner_marked_p
  }
  all_goals try {
    have : p ≤ p * p := Nat.le_mul_self p
    omega
  }
  all_goals try exact outer_step_marked_of_not_prime isPrime _ p outer cp_outer_sound cp_outer_marked (Bool.eq_false_of_not_eq_true is_p_prime)
  all_goals try {
    have hiprime : Nat.Prime i := (cp_count_sieve_correct i counting).1 is_i_prime
    rw [cp_count_count_eq]
    exact count_step_prime i hiprime
  }
  all_goals try {
    have hinot : ¬ Nat.Prime i := fun hp => by
      have ht := (cp_count_sieve_correct i counting).2 hp
      exact is_i_prime ht
    rw [cp_count_count_eq]
    exact count_step_not_prime i hinot
  }
  all_goals try {
    unfold postcondition
    subst count_done
    exact ⟨cp_count_count_eq, cp_count_count_le⟩
  }
  all_goals try simp [primeSetBelow]
  all_goals try exact cp_inner_k_dvd
  case cp_inner_sound =>
    intro m hm hfalse
    change (isPrime.set! k false)[m]! = false at hfalse
    by_cases hmk : m = k
    · subst m
      intro hkPrime
      have hp_lt_k : p < k := by
        have hp1 : 1 < p := by omega
        have hp_lt_pp : p < p * p := by
          have h := Nat.mul_lt_mul_of_pos_left hp1 (by omega : 0 < p)
          simpa using h
        exact lt_of_lt_of_le hp_lt_pp cp_inner_k_lower
      rcases hkPrime.eq_one_or_self_of_dvd p cp_inner_k_dvd with h | h
      · omega
      · omega
    · have hne : k ≠ m := Ne.symm hmk
      rw [Array.getElem!_set!_ne isPrime k m false hne] at hfalse
      exact cp_inner_sound m hm hfalse

end Proof

end CountPrimes
