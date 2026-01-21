import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def isUgly (m : Nat) : Prop :=
  m > 0 ∧ ∀ p : Nat, Nat.Prime p → p ∣ m → p = 2 ∨ p = 3 ∨ p = 5



def require1 (n : Nat) := n ≥ 1


def ensures1 (n : Nat) (result : Nat) := isUgly result



def ensures2 (n : Nat) (result : Nat) := 
  Nat.card { x : Nat | isUgly x ∧ x < result } = n - 1

def precondition (n : Nat) := require1 n

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result ∧ ensures2 n result


def test1_n : Nat := 1

def test1_Expected : Nat := 1

def test2_n : Nat := 10

def test2_Expected : Nat := 12

def test4_n : Nat := 5

def test4_Expected : Nat := 5







section Proof
theorem test1_precondition :
  precondition test1_n := by
  unfold precondition require1 test1_n
  decide

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_n test1_Expected
  constructor
  · -- Prove isUgly 1
    unfold isUgly
    constructor
    · -- 1 > 0
      omega
    · -- ∀ p, Prime p → p ∣ 1 → p = 2 ∨ p = 3 ∨ p = 5
      intro p hp hdiv
      have h1 : p ≤ 1 := Nat.le_of_dvd (by omega) hdiv
      have h2 : p ≥ 2 := hp.two_le
      omega
  · -- Prove Nat.card { x : Nat | isUgly x ∧ x < 1 } = 0
    simp only [Nat.sub_self]
    have hempty : IsEmpty { x : Nat | isUgly x ∧ x < 1 } := by
      constructor
      intro ⟨x, hugly, hlt⟩
      unfold isUgly at hugly
      have hx0 : x = 0 := by omega
      rw [hx0] at hugly
      omega
    exact Nat.card_of_isEmpty

theorem test2_precondition :
  precondition test2_n := by
  unfold precondition require1 test2_n
  omega

theorem test2_postcondition_0
    (h12_pos : True)
    : ∀ (p : ℕ), Nat.Prime p → p ∣ 12 → p = 2 ∨ p = 3 ∨ p = 5 := by
    intro p hp hdiv
    have h_le : p ≤ 12 := Nat.le_of_dvd (by norm_num : 0 < 12) hdiv
    interval_cases p
    · -- p = 0: not prime
      exact absurd hp (by decide)
    · -- p = 1: not prime
      exact absurd hp (by decide)
    · -- p = 2
      left; rfl
    · -- p = 3
      right; left; rfl
    · -- p = 4: not prime
      exact absurd hp (by decide)
    · -- p = 5: doesn't divide 12
      exfalso
      have : ¬(5 ∣ 12) := by decide
      exact this hdiv
    · -- p = 6: not prime
      exact absurd hp (by decide)
    · -- p = 7: doesn't divide 12
      exfalso
      have : ¬(7 ∣ 12) := by decide
      exact this hdiv
    · -- p = 8: not prime
      exact absurd hp (by decide)
    · -- p = 9: not prime
      exact absurd hp (by decide)
    · -- p = 10: not prime
      exact absurd hp (by decide)
    · -- p = 11: doesn't divide 12
      exfalso
      have : ¬(11 ∣ 12) := by decide
      exact this hdiv
    · -- p = 12: not prime
      exact absurd hp (by decide)

theorem test2_postcondition_1
    (h_eq : True)
    : {x | isUgly x ∧ x < 12}.Finite := by
    apply Set.Finite.subset (Set.finite_Iio 12)
    intro x hx
    exact hx.2

theorem test2_postcondition_2
    (h_finite : {x | isUgly x ∧ x < 12}.Finite)
    (h_eq : True)
    : {x | isUgly x ∧ x < 12} = {1, 2, 3, 4, 5, 6, 8, 9, 10} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · intro ⟨⟨hpos, hdiv⟩, hlt⟩
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · omega  -- x = 0
    · left; rfl  -- x = 1
    · right; left; rfl  -- x = 2
    · right; right; left; rfl  -- x = 3
    · right; right; right; left; rfl  -- x = 4
    · right; right; right; right; left; rfl  -- x = 5
    · right; right; right; right; right; left; rfl  -- x = 6
    · -- x = 7
      exfalso
      have h7 : Nat.Prime 7 := by decide
      have hdvd7 : 7 ∣ 7 := dvd_refl 7
      have := hdiv 7 h7 hdvd7
      rcases this with h | h | h <;> omega
    · right; right; right; right; right; right; left; rfl  -- x = 8
    · right; right; right; right; right; right; right; left; rfl  -- x = 9
    · right; right; right; right; right; right; right; right; rfl  -- x = 10
    · -- x = 11
      exfalso
      have h11 : Nat.Prime 11 := by decide
      have hdvd11 : 11 ∣ 11 := dvd_refl 11
      have := hdiv 11 h11 hdvd11
      rcases this with h | h | h <;> omega
    · omega  -- x ≥ 12
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (constructor; constructor)
    · omega
    · intro p hp hdvd; exact (Nat.Prime.not_dvd_one hp hdvd).elim
    · omega
    · omega
    · intro p hp hdvd
      have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hdvd
      left; exact this
    · omega
    · omega
    · intro p hp hdvd
      have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hdvd
      right; left; exact this
    · omega
    · omega
    · intro p hp hdvd
      have h4eq : (4 : Nat) = 2 ^ 2 := by norm_num
      rw [h4eq] at hdvd
      have : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hdvd
      have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp this
      left; exact this
    · omega
    · omega
    · intro p hp hdvd
      have : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hdvd
      right; right; exact this
    · omega
    · omega
    · intro p hp hdvd
      have h6 : (6 : Nat) = 2 * 3 := by norm_num
      rw [h6] at hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h
    · omega
    · omega
    · intro p hp hdvd
      have h8eq : (8 : Nat) = 2 ^ 3 := by norm_num
      rw [h8eq] at hdvd
      have : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hdvd
      have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp this
      left; exact this
    · omega
    · omega
    · intro p hp hdvd
      have h9eq : (9 : Nat) = 3 ^ 2 := by norm_num
      rw [h9eq] at hdvd
      have : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp hdvd
      have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp this
      right; left; exact this
    · omega
    · omega
    · intro p hp hdvd
      have h10 : (10 : Nat) = 2 * 5 := by norm_num
      rw [h10] at hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h
      · right; right; exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h
    · omega
end Proof
