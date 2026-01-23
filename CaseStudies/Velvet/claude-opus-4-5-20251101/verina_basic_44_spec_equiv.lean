/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ef99e99a-7c8b-4891-a7bd-efcd22b4122a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.isOddAtIndexOdd_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.isOddAtIndexOdd_precond a):
  VerinaSpec.isOddAtIndexOdd_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isOdd (n : Int) : Bool :=
  n % 2 == 1

def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  -- !benchmark @start postcond
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to check if an integer is odd
-- Using the standard definition: odd means not even (not divisible by 2)
def isOddInt (n : Int) : Prop := Odd n

-- Property: all odd indices in the array contain odd integers
def allOddIndicesHaveOddValues (a : Array Int) : Prop :=
  ∀ i : Nat, i < a.size → Odd i → Odd (a[i]!)

-- Postcondition: result is true iff all odd indices contain odd values
def ensures1 (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ allOddIndicesHaveOddValues a

def precondition (a : Array Int) : Prop :=
  True

-- no preconditions

def postcondition (a : Array Int) (result : Bool) : Prop :=
  ensures1 a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.isOddAtIndexOdd_precond a ↔ LeetProofSpec.precondition a := by
  exact?

theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.isOddAtIndexOdd_precond a):
  VerinaSpec.isOddAtIndexOdd_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  simp +decide [ VerinaSpec.isOddAtIndexOdd_postcond, LeetProofSpec.postcondition ];
  simp +decide [ VerinaSpec.isOdd, LeetProofSpec.ensures1 ];
  simp +decide [ Int.odd_iff, LeetProofSpec.allOddIndicesHaveOddValues ];
  grind