/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 699b7320-d00e-49e9-999e-d8a8cd5d1051

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.isArmstrong_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) (h_precond : VerinaSpec.isArmstrong_precond n):
  VerinaSpec.isArmstrong_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  -- !benchmark @start postcond
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Number of digits in base 10 (mathematically defined)
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)

-- Get digit at position i (0-indexed from right)
def digitAt (n : Nat) (i : Nat) : Nat :=
  (n / (10 ^ i)) % 10

-- Armstrong sum: sum of (digit at position i)^k for i from 0 to k-1
def armstrongSumAux (n : Nat) (k : Nat) (i : Nat) : Nat :=
  if i = 0 then 0
  else armstrongSumAux n k (i - 1) + (digitAt n (i - 1)) ^ k

def armstrongSum (n : Nat) : Nat :=
  let k := numDigits n
  armstrongSumAux n k k

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ armstrongSum n = n

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.isArmstrong_precond n ↔ LeetProofSpec.precondition n := by
  exact iff_of_true trivial trivial

noncomputable section AristotleLemmas

/-
VerinaSpec.countDigits and LeetProofSpec.numDigits are equivalent. Both compute the number of digits in base 10. VerinaSpec uses a tail-recursive accumulator, while LeetProofSpec uses direct recursion. They both handle 0 as having 1 digit.
-/
theorem VerinaSpec_countDigits_eq_Leet_numDigits (n : Nat) :
  VerinaSpec.countDigits n = LeetProofSpec.numDigits n := by
    -- The goal follows from the fact that if the sums of the digits are equal, then the count of digits is equal.
    simp [VerinaSpec.countDigits];
    -- By definition of countDigits.go, it correctly counts the number of digits in n by repeatedly dividing by 10 and incrementing the accumulator.
    have h_countDigits_go : ∀ n acc, VerinaSpec.countDigits.go n acc = acc + if n = 0 then 0 else 1 + VerinaSpec.countDigits.go (n / 10) 0 := by
      intro n acc;
      induction' n using Nat.strong_induction_on with n ih generalizing acc;
      unfold VerinaSpec.countDigits.go;
      grind;
    -- By definition of `LeetProofSpec.numDigits`, we have `LeetProofSpec.numDigits n = if n < 10 then 1 else 1 + LeetProofSpec.numDigits (n / 10)`.
    have h_numDigits : ∀ n, LeetProofSpec.numDigits n = if n < 10 then 1 else 1 + LeetProofSpec.numDigits (n / 10) := by
      exact?;
    induction' n using Nat.strong_induction_on with n ih;
    grind

/-
LeetProofSpec.armstrongSum is the sum of digits (from Nat.digits) raised to the power of numDigits.
Note that Nat.digits returns digits in little-endian order, but the sum is commutative.
Also handles the n=0 case where Nat.digits is empty but armstrongSum sums 0^1 = 0.
-/
theorem LeetProofSpec_armstrongSum_eq_digits_sum (n : Nat) :
  LeetProofSpec.armstrongSum n = List.sum ((Nat.digits 10 n).map (fun d => d ^ LeetProofSpec.numDigits n)) := by
    -- By definition of `LeetProofSpec.digitAt`, we can rewrite the sum of the digits raised to the power of `k` using the digits of `n`.
    have h_digitAt : ∀ i, LeetProofSpec.digitAt n i = (Nat.digits 10 n).get! i := by
      unfold LeetProofSpec.digitAt;
      intro i;
      induction' i with i ih generalizing n;
      · cases n <;> simp +decide;
      · cases n <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
    -- By definition of `armstrongSumAux`, we can rewrite the sum as the sum of the digits of `n` raised to the power of `k`.
    have h_armstrongSumAux : ∀ k, LeetProofSpec.armstrongSumAux n (LeetProofSpec.numDigits n) k = List.sum (List.map (fun i => (Nat.digits 10 n).get! i ^ LeetProofSpec.numDigits n) (List.range k)) := by
      intro k; induction' k with k ih <;> simp_all +decide [ List.range_succ ] ;
      · unfold LeetProofSpec.armstrongSumAux; aesop;
      · unfold LeetProofSpec.armstrongSumAux; aesop;
    cases n <;> simp_all +decide [ List.sum_range_succ ];
    · native_decide +revert;
    · convert h_armstrongSumAux ( LeetProofSpec.numDigits ( ‹_› + 1 ) ) using 1;
      -- By definition of `numDigits`, we know that `numDigits (‹_› + 1)` is the length of the digits of `‹_› + 1`.
      have h_numDigits : LeetProofSpec.numDigits (‹_› + 1) = List.length (Nat.digits 10 (‹_› + 1)) := by
        -- By definition of `numDigits`, we know that `numDigits (‹_› + 1)` is equal to the length of the digits of `‹_› + 1` in base 10.
        have h_numDigits : ∀ n : ℕ, n ≠ 0 → LeetProofSpec.numDigits n = List.length (Nat.digits 10 n) := by
          intro n hn; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide;
          all_goals unfold LeetProofSpec.numDigits; simp +arith +decide [ * ];
          rw [ ih _ ( by omega ) ( Nat.ne_of_gt ( Nat.div_pos ( by omega ) ( by decide ) ) ) ] ; simp +arith +decide [ Nat.div_div_eq_div_mul ];
        exact h_numDigits _ ( Nat.succ_ne_zero _ );
      cases h : Nat.digits 10 ( ‹_› + 1 ) <;> simp_all +decide [ List.range_succ_eq_map ];
      congr! 1;
      refine' List.ext_get _ _ <;> aesop

/-
For a single digit `n < 10`, `Nat.repr n` is the string containing that digit.
-/
theorem Nat_repr_digit (n : Nat) (h : n < 10) : Nat.repr n = String.singleton (Char.ofNat (n + '0'.toNat)) := by
  interval_cases n <;> native_decide

/-
For `n ≠ 0`, `Nat.repr n` corresponds to the digits of `n` (from `Nat.digits 10 n`) reversed and converted to characters.
This connects the string representation used by `VerinaSpec` to the numerical digits used by `LeetProofSpec`.
-/
theorem Nat_repr_eq_digits_reverse (n : Nat) (h : n ≠ 0) :
  Nat.repr n = String.mk ((Nat.digits 10 n).reverse.map (fun d => Char.ofNat (d + 48))) := by
    induction' n using Nat.strong_induction_on with n ih;
    rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp +arith +decide [ Nat.repr ] at *;
    specialize ih ( ( n + 11 ) / 10 ) ( by omega ) ( Nat.ne_of_gt ( Nat.div_pos ( by omega ) ( by decide ) ) );
    simp_all +decide [ Nat.toDigits, List.asString ];
    convert congr_arg ( fun l => l ++ [ Char.ofNat ( ( n + 11 ) % 10 + 48 ) ] ) ih using 1;
    · rw [ Nat.toDigitsCore ];
      rw [ show Nat.toDigitsCore 10 ( n + 11 ) ( ( n + 11 ) / 10 ) [ ( ( n + 11 ) % 10 ).digitChar ] = Nat.toDigitsCore 10 ( ( n + 11 ) / 10 + 1 ) ( ( n + 11 ) / 10 ) [] ++ [ ( ( n + 11 ) % 10 ).digitChar ] from ?_ ];
      · have := Nat.mod_lt ( n + 11 ) ( by decide : 0 < 10 ) ; interval_cases ( n + 11 ) % 10 <;> trivial;
      · have h_digits_eq : ∀ (m n : ℕ) (l : List Char), m > n → Nat.toDigitsCore 10 m n l = Nat.toDigitsCore 10 (n + 1) n [] ++ l := by
          intros m n l hmn;
          induction' m using Nat.strong_induction_on with m ih generalizing n l;
          rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.toDigitsCore ];
          grind;
        grind;
    · simp +decide [ List.append_assoc ]

/-
We prove that the sum computed by `VerinaSpec` is equal to the sum of digits raised to the power of `countDigits`.
Case 1: `n = 0`.
`toString 0 = "0"`, so `digits = [0]`. `countDigits 0 = 1`.
LHS: `foldl` sums `0^1 = 0`.
RHS: `Nat.digits 10 0 = []`, so sum is `0`.
They are equal.

Case 2: `n ≠ 0`.
By `Nat_repr_eq_digits_reverse`, `toString n` corresponds to `(Nat.digits 10 n).reverse`.
Thus `digits` is exactly `(Nat.digits 10 n).reverse`.
LHS is `foldl` summing elements of `digits` raised to power `k`.
This is equivalent to `List.sum (digits.map (^k))`.
Since `digits` is the reverse of `Nat.digits 10 n`, and sum is commutative (or rather, sum of reverse is sum), the sums are equal.
We use `List.foldl_map`, `List.foldl_add`, and `List.sum_reverse`.
-/
theorem VerinaSpec_sum_eq_digits_sum (n : Nat) :
  let digits := List.map (fun c => c.toNat - '0'.toNat) (toString n).toList
  List.foldl (fun acc d => acc + d ^ VerinaSpec.countDigits n) 0 digits =
  List.sum ((Nat.digits 10 n).map (fun d => d ^ VerinaSpec.countDigits n)) := by
    by_cases hn : n = 0;
    · simp +decide [ hn, VerinaSpec.countDigits ];
      native_decide +revert;
    · -- By definition of `Nat.repr`, we can rewrite the left-hand side of the equation in terms of the digits of `n`.
      have h_digits : (Nat.repr n).toList.map (fun c => c.toNat - '0'.toNat) = (Nat.digits 10 n).reverse.map (fun d => d) := by
        have := Nat_repr_eq_digits_reverse n hn;
        simp_all +decide [ String.toList ];
        erw [ List.map_congr_left ];
        exact?;
        intro d hd; have := Nat.digits_lt_base' hd; interval_cases d <;> trivial;
      convert congr_arg ( fun l => List.foldl ( fun acc d => acc + d ^ VerinaSpec.countDigits n ) 0 l ) h_digits using 1;
      induction ( Nat.digits 10 n ) <;> simp +arith +decide [ * ]

end AristotleLemmas

theorem postcondition_equiv (n : Nat) (result : Bool) (h_precond : VerinaSpec.isArmstrong_precond n):
  VerinaSpec.isArmstrong_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of `isArmstrong_postcond` and `postcondition`, we can rewrite them using the sums computed by `VerinaSpec` and `LeetProofSpec`.
  simp [VerinaSpec.isArmstrong_postcond, LeetProofSpec.postcondition] at *;
  -- By definition of `VerinaSpec.sum_eq_digits_sum`, we know that the sum computed by `VerinaSpec` is equal to the sum computed by `LeetProofSpec`.
  have h_sum_eq : List.foldl (fun (acc d : ℕ) => acc + d ^ VerinaSpec.countDigits n) 0 (List.map (fun (c : Char) => c.toNat - 48) (ToString.toString n).data) = LeetProofSpec.armstrongSum n := by
    -- Apply the theorem that states the sum computed by VerinaSpec is equal to the sum computed by LeetProofSpec.
    apply Eq.symm; exact (by
    convert VerinaSpec_sum_eq_digits_sum n |> Eq.symm;
    rw [ LeetProofSpec_armstrongSum_eq_digits_sum, VerinaSpec_countDigits_eq_Leet_numDigits ]);
  grind