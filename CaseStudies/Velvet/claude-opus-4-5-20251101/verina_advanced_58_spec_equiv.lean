/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bbdfbc4b-f173-43cc-a064-571bbfa469cf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.nthUglyNumber_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.nthUglyNumber_precond n):
  VerinaSpec.nthUglyNumber_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def nthUglyNumber_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0

-- !benchmark @end precond

def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')

def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1  -- n > 0
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)  -- 1 < p, so 2 ≤ p
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1

def nthUglyNumber_postcond (n : Nat) (result: Nat) (h_precond : nthUglyNumber_precond (n)) : Prop :=
  -- !benchmark @start postcond
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Property-based definition of ugly number (no recursion needed)
-- A number m is ugly iff m > 0 and every prime factor of m is 2, 3, or 5
def isUgly (m : Nat) : Prop :=
  m > 0 ∧ ∀ p : Nat, Nat.Prime p → p ∣ m → p = 2 ∨ p = 3 ∨ p = 5

-- Precondition: n must be at least 1 (1-indexed)
def require1 (n : Nat) := n ≥ 1

-- Postcondition clause 1: the result is positive and only has prime factors 2, 3, 5
def ensures1 (n : Nat) (result : Nat) := isUgly result

-- Postcondition clause 2: there are exactly n-1 ugly numbers strictly less than result
-- This ensures result is the nth smallest ugly number
def ensures2 (n : Nat) (result : Nat) := 
  Nat.card { x : Nat | isUgly x ∧ x < result } = n - 1

def precondition (n : Nat) := require1 n

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result ∧ ensures2 n result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.nthUglyNumber_precond n ↔ LeetProofSpec.precondition n := by
  exact?

noncomputable section AristotleLemmas

/-
`divideOut n p` removes all factors of `p` from `n` if `p` is prime.
-/
theorem VerinaSpec.divideOut_eq_of_prime (n p : Nat) (hp : Nat.Prime p) :
  VerinaSpec.divideOut n p = n / (p ^ n.factorization p) := by
    induction' n using Nat.strong_induction_on with n ih generalizing p;
    by_cases hn : n = 0;
    · unfold VerinaSpec.divideOut; aesop;
    · by_cases h : n % p = 0;
      · -- Since $p$ divides $n$, we can write $n = p * m$ for some $m$.
        obtain ⟨m, hm⟩ : ∃ m, n = p * m := Nat.dvd_of_mod_eq_zero h;
        rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.factorization_mul ];
        convert ih m ( by nlinarith [ Nat.pos_of_ne_zero hn ] ) ( p + 1 + 1 ) hp using 1;
        · rw [ VerinaSpec.divideOut ] ; aesop;
        · rw [ pow_add, pow_one, Nat.mul_div_mul_left _ _ ( Nat.succ_pos _ ) ];
      · unfold VerinaSpec.divideOut;
        simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero ]

/-
`VerinaSpec.isUgly` is equivalent to `LeetProofSpec.isUgly`.
-/
theorem VerinaSpec.isUgly_iff_leet (n : Nat) : VerinaSpec.isUgly n = true ↔ LeetProofSpec.isUgly n := by
  constructor;
  · intro hn
    have h_factorization : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) * 5 ^ (n.factorization 5) := by
      unfold VerinaSpec.isUgly at hn;
      have h_divisors : VerinaSpec.divideOut n 2 = n / (2 ^ (n.factorization 2)) ∧ VerinaSpec.divideOut (n / (2 ^ (n.factorization 2))) 3 = (n / (2 ^ (n.factorization 2))) / (3 ^ ((n / (2 ^ (n.factorization 2))).factorization 3)) ∧ VerinaSpec.divideOut ((n / (2 ^ (n.factorization 2))) / (3 ^ ((n / (2 ^ (n.factorization 2))).factorization 3))) 5 = ((n / (2 ^ (n.factorization 2))) / (3 ^ ((n / (2 ^ (n.factorization 2))).factorization 3))) / (5 ^ (((n / (2 ^ (n.factorization 2))) / (3 ^ ((n / (2 ^ (n.factorization 2))).factorization 3))).factorization 5)) := by
        exact ⟨ VerinaSpec.divideOut_eq_of_prime _ _ ( by norm_num ), VerinaSpec.divideOut_eq_of_prime _ _ ( by norm_num ), VerinaSpec.divideOut_eq_of_prime _ _ ( by norm_num ) ⟩;
      split_ifs at hn ; simp_all +decide [ Nat.factorization_div ];
      rw [ Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul ] at hn;
      rw [ Nat.div_eq_iff_eq_mul_left ] at hn;
      · rw [ Nat.factorization_div ] at hn <;> norm_num at *;
        · rw [ Nat.div_div_eq_div_mul, Nat.factorization_div ] at hn <;> norm_num at *;
          · linarith;
          · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by { exact Nat.Coprime.pow _ _ <| by decide } ) ( Nat.ordProj_dvd _ _ ) ( Nat.ordProj_dvd _ _ );
        · exact Nat.ordProj_dvd _ _;
      · positivity;
      · refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
        · exact Nat.Coprime.mul_right ( Nat.Coprime.pow _ _ <| by decide ) ( Nat.Coprime.pow _ _ <| by decide );
        · exact Nat.ordProj_dvd _ _;
        · refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
          · apply_rules [ Nat.Coprime.pow ];
          · exact Nat.dvd_trans ( Nat.ordProj_dvd _ _ ) ( Nat.div_dvd_of_dvd ( Nat.ordProj_dvd _ _ ) );
          · refine' Nat.dvd_trans ( Nat.ordProj_dvd _ _ ) _;
            refine' Nat.dvd_trans ( Nat.div_dvd_of_dvd _ ) ( Nat.div_dvd_of_dvd _ );
            · exact Nat.ordProj_dvd _ _;
            · exact Nat.ordProj_dvd _ _;
    refine' ⟨ Nat.pos_of_ne_zero _, fun p pp dp => _ ⟩;
    · rintro rfl; contradiction;
    · rw [ h_factorization ] at dp; simp +decide [ Nat.Prime.dvd_mul pp ] at dp;
      rcases dp with ( ( dp | dp ) | dp ) <;> have := Nat.Prime.dvd_of_dvd_pow pp dp <;> ( have := Nat.le_of_dvd ( by decide ) this; interval_cases p <;> trivial; );
  · unfold LeetProofSpec.isUgly VerinaSpec.isUgly;
    field_simp;
    intro hn
    have h_factorization : n = 2 ^ (Nat.factorization n 2) * 3 ^ (Nat.factorization n 3) * 5 ^ (Nat.factorization n 5) := by
      conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self hn.1.ne' ];
      rw [ Finsupp.prod_of_support_subset ];
      case s => exact { 2, 3, 5 };
      · simp +decide [ mul_assoc ];
      · intro p hp; specialize hn; aesop;
      · norm_num;
    rw [ h_factorization, VerinaSpec.divideOut_eq_of_prime, VerinaSpec.divideOut_eq_of_prime, VerinaSpec.divideOut_eq_of_prime ] <;> norm_num;
    norm_num [ Nat.mul_div_assoc, Nat.mul_assoc, Nat.pow_succ' ]

end AristotleLemmas

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.nthUglyNumber_precond n):
  VerinaSpec.nthUglyNumber_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  rw [ VerinaSpec.nthUglyNumber_postcond, LeetProofSpec.postcondition ];
  have h_list_eq_set : (List.filter (fun i => VerinaSpec.isUgly i) (List.range result)).length = Nat.card { x : ℕ | LeetProofSpec.isUgly x ∧ x < result } := by
    rw [ show { x : ℕ | LeetProofSpec.isUgly x ∧ x < result } = ( List.toFinset ( List.filter ( fun x => VerinaSpec.isUgly x ) ( List.range result ) ) ) from ?_ ];
    · rw [ Nat.card_eq_fintype_card, Fintype.card_ofFinset ];
      · rw [ List.toFinset_card_of_nodup ];
        refine' List.Nodup.filter _ _;
        exact?;
      · aesop;
    · ext x aesop;
      simp +zetaDelta at *;
      rw [ ← VerinaSpec.isUgly_iff_leet ] ; aesop;
  have := @VerinaSpec.isUgly_iff_leet result; aesop;