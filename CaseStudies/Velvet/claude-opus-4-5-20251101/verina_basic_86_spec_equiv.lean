/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 220efe0a-0890-43ec-a9e3-6468b099ca17

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (offset : Int):
  VerinaSpec.rotate_precond a offset ↔ LeetProofSpec.precondition a offset

- theorem postcondition_equiv (a : Array Int) (offset : Int) (result : Array Int) (h_precond : VerinaSpec.rotate_precond a offset):
  VerinaSpec.rotate_postcond a offset result h_precond ↔ LeetProofSpec.postcondition a offset result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  -- !benchmark @start precond
  offset ≥ 0

-- !benchmark @end precond

def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b

def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) (h_precond : rotate_precond (a) (offset)) :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: offset must be non-negative
def precondition (a : Array Int) (offset : Int) :=
  offset ≥ 0

-- Postcondition: result has same size and elements are rotated according to modular index formula
def postcondition (a : Array Int) (offset : Int) (result : Array Int) :=
  result.size = a.size ∧
  (∀ i : Nat, i < result.size →
    result[i]! = a[(i + offset.toNat) % a.size]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (offset : Int):
  VerinaSpec.rotate_precond a offset ↔ LeetProofSpec.precondition a offset := by
  rfl

theorem postcondition_equiv (a : Array Int) (offset : Int) (result : Array Int) (h_precond : VerinaSpec.rotate_precond a offset):
  VerinaSpec.rotate_postcond a offset result h_precond ↔ LeetProofSpec.postcondition a offset result := by
  -- The two postconditions are equivalent because the rotation function's implementation ensures that the elements are rotated correctly.
  simp [VerinaSpec.rotate_postcond, LeetProofSpec.postcondition];
  -- Since the arrays have the same size, the indices are the same in both cases.
  intro h_size
  simp [h_size];
  -- Since `offset` is non-negative, `offset.toNat` is equal to `offset`.
  have h_offset_toNat : offset.toNat = offset := by
    exact Int.toNat_of_nonneg h_precond;
  congr!;
  norm_num [ ← Int.natCast_inj, Int.toNat_of_nonneg, h_offset_toNat ];
  exact Int.emod_nonneg _ ( by linarith )