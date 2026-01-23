/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 82ac5614-86e5-4765-a13e-b07dd1e1de27

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int) (y : Int):
  VerinaSpec.myMin_precond x y ↔ LeetProofSpec.precondition x y

- theorem postcondition_equiv (x : Int) (y : Int) (result : Int) (h_precond : VerinaSpec.myMin_precond x y):
  VerinaSpec.myMin_postcond x y result h_precond ↔ LeetProofSpec.postcondition x y result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def myMin_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  -- !benchmark @start postcond
  (x ≤ y → result = x) ∧ (x > y → result = y)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on inputs
def precondition (x : Int) (y : Int) : Prop :=
  True

-- Postcondition: Result is the minimum of x and y
-- Property 1: Result is less than or equal to both inputs
-- Property 2: Result equals one of the inputs
-- Property 3: Result equals min x y (using Lean's built-in min)
def postcondition (x : Int) (y : Int) (result : Int) : Prop :=
  result ≤ x ∧ result ≤ y ∧ (result = x ∨ result = y)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : Int) (y : Int):
  VerinaSpec.myMin_precond x y ↔ LeetProofSpec.precondition x y := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (x : Int) (y : Int) (result : Int) (h_precond : VerinaSpec.myMin_precond x y):
  VerinaSpec.myMin_postcond x y result h_precond ↔ LeetProofSpec.postcondition x y result := by
  -- To prove the equivalence, we split into cases based on whether $x \leq y$ or $x > y$.
  by_cases hxy : x ≤ y;
  · -- If $result = x$, then obviously $result \leq x$ and $result \leq y$ since $x \leq y$.
    apply Iff.intro;
    · intro h_result
      cases' h_result with hxy h_eq;
      constructor <;> aesop;
    · -- If $result = x$, then since $x \leq y$, we have $result \leq x$ and $result \leq y$.
      intro h_postcond
      cases' h_postcond with h_le_x h_le_y h_eq;
      -- Since $x \leq y$, we have $result \leq x$ and $result \leq y$. Also, $result = x$ or $result = y$.
      cases' h_le_y with h_le_y h_eq;
      cases h_eq <;> simp_all +decide [ VerinaSpec.myMin_postcond ];
      linarith;
  · -- Since $x > y$, we have $result = y$ by the definition of `myMin_postcond`.
    simp [VerinaSpec.myMin_postcond, LeetProofSpec.postcondition, hxy];
    grind