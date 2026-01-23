/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 23bbc68f-d86c-4b23-bc22-0e6a84684580

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (l : List Int) (n : Nat):
  VerinaSpec.rotateRight_precond l n ↔ LeetProofSpec.precondition l n

- theorem postcondition_equiv (l : List Int) (n : Nat) (result : List Int) (h_precond : VerinaSpec.rotateRight_precond l n):
  VerinaSpec.rotateRight_postcond l n result h_precond ↔ LeetProofSpec.postcondition l n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def rotateRight_postcond (l : List Int) (n : Nat) (result: List Int) (h_precond : rotateRight_precond (l) (n)) :=
  -- !benchmark @start postcond
  result.length = l.length ∧
  (∀ i : Nat, i < l.length →
    let len := l.length
    let rotated_index := Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
    result[i]? = l[rotated_index]?)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: n is a natural number (always non-negative by type)
def precondition (l : List Int) (n : Nat) :=
  True

-- Postcondition: specifies the rotation relationship
-- For right rotation by n:
-- - The result has the same length as input
-- - Each element at position i in result comes from position (i - n) mod length in l
--   which is equivalent to: l[i] goes to position (i + n) mod length in result
def postcondition (l : List Int) (n : Nat) (result : List Int) :=
  result.length = l.length ∧
  (l.length = 0 → result = []) ∧
  (l.length > 0 →
    ∀ i : Nat, i < l.length →
      result[(i + n) % l.length]! = l[i]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (l : List Int) (n : Nat):
  VerinaSpec.rotateRight_precond l n ↔ LeetProofSpec.precondition l n := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (l : List Int) (n : Nat) (result : List Int) (h_precond : VerinaSpec.rotateRight_precond l n):
  VerinaSpec.rotateRight_postcond l n result h_precond ↔ LeetProofSpec.postcondition l n result := by
  constructor;
  · rintro ⟨ h₁, h₂ ⟩;
    -- For any i < len, we need to show that result[(i + n) % len] = l[i].
    have h_eq : ∀ i < l.length, result[(i + n) % l.length]! = l[i]! := by
      intro i hi
      specialize h₂ ((i + n) % l.length) (Nat.mod_lt _ (by
      linarith));
      simp_all +decide [ Int.emod_eq_of_lt, Int.toNat_of_nonneg ];
    constructor <;> aesop;
  · intro h;
    unfold LeetProofSpec.postcondition at h;
    -- By definition of postcondition, we need to show that for any i < l.length, result[i]? = l[rotated_index]?.
    have h_postcondition : ∀ i < l.length, result[i]? = l[(i + l.length - n % l.length) % l.length]? := by
      intro i hi;
      have := h.2.2 ( List.length_pos_iff.mpr ( by aesop ) ) ( ( i + l.length - n % l.length ) % l.length ) ( Nat.mod_lt _ ( List.length_pos_iff.mpr ( by aesop ) ) ) ; simp_all +decide [ Nat.sub_add_cancel ( show n % l.length ≤ i + l.length from le_trans ( Nat.le_of_lt ( Nat.mod_lt _ ( List.length_pos_iff.mpr ( by aesop ) ) ) ) ( Nat.le_add_left _ _ ) ) ] ;
      convert congr_arg ( fun x : ℤ => Option.some x ) this using 1;
      · rw [ show ( i + l.length - n % l.length + n ) % l.length = i from ?_ ];
        · grind;
        · rw [ Nat.modEq_of_dvd ];
          exact Nat.mod_eq_of_lt hi;
          exact ⟨ - ( n / l.length ) - 1, by rw [ Nat.cast_add, Nat.cast_sub ( by linarith [ Nat.zero_le ( n % l.length ), Nat.mod_lt n ( by linarith : 0 < l.length ) ] ) ] ; push_cast; linarith [ Nat.mod_add_div n l.length ] ⟩;
      · rw [ List.getElem?_eq_getElem ];
        rw [ Option.getD_some ];
        exact Nat.mod_lt _ ( by linarith );
    refine' ⟨ h.1, fun i hi => _ ⟩;
    convert h_postcondition i hi using 2;
    simp +decide [ ← Int.natCast_inj, Nat.cast_sub ( show n % l.length ≤ i + l.length from le_trans ( Nat.mod_lt _ ( by linarith ) |> Nat.le_of_lt ) ( by linarith ) ) ];
    rw [ max_eq_left ( Int.emod_nonneg _ ( by norm_cast; linarith ) ) ] ; simp +decide [ sub_eq_add_neg, Int.add_emod ]