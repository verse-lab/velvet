/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3ae6193c-1b9c-46ad-badc-d3642d1e7b03

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfDigits_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfDigits_precond n):
  VerinaSpec.sumOfDigits_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def sumOfDigits_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  -- !benchmark @start postcond
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: n is a natural number (always satisfied for Nat type)
def precondition (n : Nat) :=
  True

-- Postcondition: result equals the sum of the decimal digits of n
-- Using the mathematical property that digit sum equals the sum of digits in base 10
-- Nat.digits 10 n gives the list of digits, and List.sum computes their sum
-- This is the standard mathematical definition of digit sum
def postcondition (n : Nat) (result : Nat) :=
  result = (Nat.digits 10 n).sum

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.sumOfDigits_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are defined as True, the equivalence is trivially true.
  simp [VerinaSpec.sumOfDigits_precond, LeetProofSpec.precondition]

noncomputable section AristotleLemmas

/-
Appending a list `l` to the result of `Nat.toDigitsCore` with accumulator `acc` is the same as calling `Nat.toDigitsCore` with accumulator `acc ++ l`.
-/
theorem toDigitsCore_append (b fuel n : Nat) (acc l : List Char) :
  Nat.toDigitsCore b fuel n acc ++ l = Nat.toDigitsCore b fuel n (acc ++ l) := by
    induction' fuel with fuel ih generalizing n acc l <;> simp_all +decide [ Nat.toDigitsCore ];
    grind

/-
`Nat.toDigitsCore` accumulates the digits of `n` in base `b` (reversed and converted to characters) into `acc`, for `n > 0`.
-/
theorem toDigitsCore_eq_digits_reverse_of_pos (b fuel n : Nat) (acc : List Char)
  (hb : b > 1) (hn : n > 0) (h_fuel : n < fuel) :
  Nat.toDigitsCore b fuel n acc = (Nat.digits b n).reverse.map Nat.digitChar ++ acc := by
    -- We'll use induction on `fuel`.
    induction' fuel with k ih generalizing n acc;
    · contradiction;
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.toDigitsCore ];
      · rcases b with ( _ | _ | b ) <;> trivial;
      · split_ifs with h;
        · cases h <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        · rw [ ih ];
          · rcases b with ( _ | _ | b ) <;> simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
          · exact Nat.div_pos ( by omega ) hb.le;
          · exact Nat.div_lt_of_lt_mul <| by nlinarith;

/-
For `n > 0`, `Nat.toDigits 10 n` corresponds to the reverse of `Nat.digits 10 n`.
-/
theorem toDigits_eq_digits_reverse (n : Nat) (h : n > 0) :
  (Nat.toDigits 10 n).map (fun c => c.toNat - 48) = (Nat.digits 10 n).reverse := by
    have := @toDigitsCore_eq_digits_reverse_of_pos 10 ( n + 1 ) n [ ];
    simp_all +decide [ Nat.toDigits ];
    congr! 1;
    · rw [ List.map_congr_left ];
      rotate_right;
      use fun x => x;
      · norm_num;
      · intro a ha; have := Nat.digits_lt_base' ha; interval_cases a <;> trivial;
    · have := Nat.mod_lt n ( by decide : 0 < 10 ) ; interval_cases n % 10 <;> trivial;

end AristotleLemmas

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.sumOfDigits_precond n):
  VerinaSpec.sumOfDigits_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  unfold VerinaSpec.sumOfDigits_postcond LeetProofSpec.postcondition;
  by_cases hn : n = 0;
  · aesop;
  · rw [ show ( Nat.repr n |> String.toList ).map ( fun c => c.toNat - '0'.toNat ) = ( Nat.digits 10 n |> List.reverse ) from ?_ ];
    · rw [ List.sum_reverse ] ; omega;
    · convert toDigits_eq_digits_reverse n ( Nat.pos_of_ne_zero hn ) using 1