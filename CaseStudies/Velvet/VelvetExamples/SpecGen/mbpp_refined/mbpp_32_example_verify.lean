import Lean
import Mathlib.Tactic

-- Helper Functions

def isFactor (d: Nat) (n: Nat) : Prop :=
  d > 0 ∧ n % d = 0
-- Helper definition for prime factors
-- A prime factor of n is a number that is both prime and a factor of n

def isPrimeFactor (p: Nat) (n: Nat) : Prop :=
  Nat.Prime p ∧ isFactor p n

def require1 (n : Nat) :=
  n > 1  -- Ensures at least one prime factor exists

-- Postcondition clauses

def ensures1 (n : Nat) (result : Nat) :=
  isPrimeFactor result n  -- Result is a prime factor of n
def ensures2 (n : Nat) (result : Nat) :=
  ∀ p, isPrimeFactor p n → p ≤ result  -- Result is the largest prime factor

def precondition (n: Nat) :=
  require1 n

def postcondition (n: Nat) (result: Nat) :=
  ensures1 n result ∧ ensures2 n result

-- Test Cases
def test1_n : Nat := 2

def test1_Expected : Nat := 2

def test3_n : Nat := 15

def test3_Expected : Nat := 5

def test6_n : Nat := 30

def test6_Expected : Nat := 5

def test10_n : Nat := 221

def test10_Expected : Nat := 17

def test14_n : Nat := 997

def test14_Expected : Nat := 997

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_n := by
  -- For the test case where n is 2, we need to show that 2 > 1.
  simp [precondition, require1];
  -- Since `test1_n` is defined as 2, we can directly show that 1 < 2.
  norm_num [test1_n]

lemma test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition test1_n test1_Expected; aesop;
  · -- We need to show that 2 is a prime factor of 2.
    unfold ensures1 isPrimeFactor Nat.Prime isFactor
    simp;
    native_decide;
  · intro p hp
    obtain ⟨hp_prime, hp_factor⟩ := hp;
    linarith [ hp_factor.2, Nat.le_of_dvd ( by decide ) ( Nat.dvd_of_mod_eq_zero hp_factor.2 ) ]

-- test3
lemma test3_precondition :
  precondition test3_n := by
  exact Nat.le_add_left _ _

lemma test3_postcondition :
  postcondition test3_n test3_Expected := by
  -- Check that 5 is a prime factor of 15.
  have h_prime : Nat.Prime 5 := by
    unfold Nat.Prime; native_decide;
  -- Show that 5 is the largest prime factor of 15.
  have h_largest : ∀ p, isPrimeFactor p test3_n → p ≤ 5 := by
    -- The prime factors of 15 are 3 and 5. Therefore, any prime factor p of 15 must be either 3 or 5.
    intro p hp
    have h_factors : p = 3 ∨ p = 5 := by
      -- Since 15 is 3 times 5, its prime factors are exactly 3 and 5. Therefore, any prime factor p of 15 must divide 15.
      have h_div : p ∣ 15 := by
        exact Nat.dvd_of_mod_eq_zero hp.2.2;
      have := Nat.le_of_dvd ( by decide ) h_div; interval_cases p <;> simp +decide at h_div hp ⊢;
      · cases hp.1;
        contradiction;
      · cases hp ; simp_all +decide [ Nat.Prime ];
    rcases h_factors with ( rfl | rfl ) <;> decide;
  exact ⟨ ⟨ h_prime, ⟨ by decide, by decide ⟩ ⟩, h_largest ⟩

-- test6
lemma test6_precondition :
  precondition test6_n := by
  exact Nat.le_add_left _ _

lemma test6_postcondition :
  postcondition test6_n test6_Expected := by
  -- Verify that 5 is a prime factor of 30.
  have h_prime_factor : isPrimeFactor 5 30 := by
    constructor;
    · -- We can prove that 5 is prime by showing it has exactly two divisors: 1 and 5.
      decide
    · exact ⟨ by decide, by decide ⟩;
  -- Now, we need to show that there are no prime factors of 30 larger than 5.
  have h_no_larger_prime_factors : ∀ p, isPrimeFactor p 30 → p ≤ 5 := by
    intros p hp
    rcases hp with ⟨h_prime, h_factor⟩;
    rcases h_factor with ⟨ h_factor₁, h_factor₂ ⟩ ;
    have := Nat.le_of_dvd ( by decide ) ( Nat.dvd_of_mod_eq_zero h_factor₂ ) ;
    aesop;
    interval_cases p <;> trivial;
  -- Combine the facts that 5 is a prime factor and that there are no larger prime factors to conclude the proof.
  apply And.intro h_prime_factor h_no_larger_prime_factors

-- test10
lemma test10_precondition :
  precondition test10_n := by
  exact Nat.le_add_left _ _

lemma test10_postcondition :
  postcondition test10_n test10_Expected := by
  -- We need to show that 17 is a prime factor of 221 and that it is the largest such prime factor.
  apply And.intro;
  · constructor;
    · decide
    · exact ⟨ by decide, by decide ⟩;
  · -- We need to show that 17 is the largest prime factor of 221.
    intro p hp
    have h_div : p ∣ 221 := by
      -- By definition of isFactor, if p is a factor of 221, then p divides 221.
      apply Nat.dvd_of_mod_eq_zero; exact hp.right.right;
    have := Nat.le_of_dvd ( by decide ) h_div; interval_cases p <;> norm_num at *;
    · decide +revert;
    · decide;
    · decide +revert;
    · exact absurd hp.1 ( by native_decide )

-- test14
lemma test14_precondition :
  precondition test14_n := by
  exact Nat.lt_succ_of_le ( Nat.le_add_left _ _ )

lemma test14_postcondition :
  postcondition test14_n test14_Expected := by
  -- Since 997 is prime, it is a prime factor of itself.
  have h_prime : Nat.Prime 997 := by
    native_decide
  -- Since 997 is prime, it is a prime factor of itself and there are no larger prime factors.
  have h_prime_factor : isPrimeFactor 997 997 := by
    exact ⟨ h_prime, ⟨ by norm_num, by norm_num ⟩ ⟩;
  -- Since 997 is prime, it is the largest prime factor of itself.
  apply And.intro h_prime_factor;
  intro p hp;
  exact Nat.le_of_dvd ( by decide ) ( Nat.dvd_of_mod_eq_zero hp.2.2 )

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  -- If ret1 and ret2 are both prime factors of n and both are the largest, then they must be equal.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  have h_le : ret1 ≤ ret2 ∧ ret2 ≤ ret1 := by
    exact ⟨ h_ret2.2 _ h_ret1.1, h_ret1.2 _ h_ret2.1 ⟩;
  linarith
