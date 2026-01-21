/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cadec62e-a012-4c05-89ff-d5c462c2b34b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.increasingTriplet_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Bool) (h_precond : VerinaSpec.increasingTriplet_precond nums):
  VerinaSpec.increasingTriplet_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def increasingTriplet_postcond (nums : List Int) (result: Bool) (h_precond : increasingTriplet_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper predicate: there exists a strictly increasing triplet
def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!

-- Postcondition: result is true iff such a triplet exists
def ensures1 (nums : List Int) (result : Bool) :=
  result = true ↔ hasIncreasingTriplet nums

def precondition (nums : List Int) :=
  True

-- no preconditions

def postcondition (nums : List Int) (result : Bool) :=
  ensures1 nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.increasingTriplet_precond nums ↔ LeetProofSpec.precondition nums := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.increasingTriplet_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Bool) (h_precond : VerinaSpec.increasingTriplet_precond nums):
  VerinaSpec.increasingTriplet_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- By definition of `VerinaSpec.increasingTriplet_postcond` and `LeetProofSpec.postcondition`, we can show that they are equivalent by substituting ` nums'` with `nums` in the conditions.
  simp [VerinaSpec.increasingTriplet_postcond, LeetProofSpec.postcondition];
  -- To prove the equivalence, we can split into cases based on the value of `result`.
  cases result <;> simp [LeetProofSpec.ensures1];
  · -- To prove the equivalence, we can split into two implications.
    apply Iff.intro;
    · intro h;
      -- Apply the hypothesis `h` to the triplet `(i, j, k)` and use the fact that `h` implies that such a triplet cannot exist.
      intros h_triplet; obtain ⟨i, j, k, hij, hjk, hlt, hlt'⟩ := h_triplet; (
      contrapose! h;
      -- Since $i$, $j$, and $k$ are within the bounds of the list, the elements at these indices are indeed in the zipIdx list.
      have h_zipIdx : ∀ (n : ℕ), n < nums.length → (nums[n]!, n) ∈ nums.zipIdx := by
        grind;
      exact ⟨ _, _, h_zipIdx _ ( by linarith ), _, _, h_zipIdx _ ( by linarith ), _, _, h_zipIdx _ ( by linarith ), hij, hjk, hlt'.1, hlt'.2 ⟩);
    · contrapose!;
      rintro ⟨ a, b, hab, c, d, hcd, e, f, hef, h₁, h₂, h₃, h₄ ⟩;
      use b, d, f;
      grind;
  · constructor <;> intro h;
    · obtain ⟨ a, b, h₁, c, d, h₂, e, f, h₃, h₄, h₅, h₆, h₇ ⟩ := h;
      use b, d, f;
      grind;
    · rcases h with ⟨ i, j, k, hij, hjk, hk, h ⟩;
      -- Since $i$, $j$, and $k$ are valid indices into the list $nums$, the pairs $(nums[i]!, i)$, $(nums[j]!, j)$, and $(nums[k]!, k)$ are all elements of the zipped list.
      have h_zip : (nums[i]!, i) ∈ nums.zipIdx ∧ (nums[j]!, j) ∈ nums.zipIdx ∧ (nums[k]!, k) ∈ nums.zipIdx := by
        grind;
      exact ⟨ _, _, h_zip.1, _, _, h_zip.2.1, _, _, h_zip.2.2, hij, hjk, h ⟩