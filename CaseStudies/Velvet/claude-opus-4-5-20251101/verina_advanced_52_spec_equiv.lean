/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 09b72bd0-1d3e-4762-965e-db25feb0bd11

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Nat) (k : Nat):
  VerinaSpec.minOperations_precond nums k ↔ LeetProofSpec.precondition nums k

- theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) (h_precond : VerinaSpec.minOperations_precond nums k):
  VerinaSpec.minOperations_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  -- !benchmark @start precond
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)

-- !benchmark @end precond

def minOperations_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : minOperations_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  -- define the list of elements processed after `result` operations
  let processed := (nums.reverse).take result
  -- define the target numbers to collect (1 to k)
  let target_nums := (List.range k).map (· + 1)

  -- condition 1: All target numbers must be present in the processed elements
  let collected_all := target_nums.all (fun n => List.elem n processed)

  -- condition 2: `result` must be the minimum number of operations.
  -- This means either result is 0 (which implies k must be 0 as target_nums would be empty)
  -- or result > 0, and taking one less operation (result - 1) is not sufficient
  let is_minimal :=
    if result > 0 then
      -- if one fewer element is taken, not all target numbers should be present
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      -- if result is 0, it can only be minimal if k is 0 (no targets required)
      -- So if k=0, `collected_all` is true. If result=0, this condition `k==0` ensures minimality.
      k == 0

  -- overall specification:
  collected_all ∧ is_minimal

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if all integers from 1 to k are present in a list
def containsAllUpToK (collected : List Nat) (k : Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i ∧ i ≤ k → i ∈ collected

-- Helper: Get the suffix of length n from a list (last n elements)
def listSuffix (l : List Nat) (n : Nat) : List Nat :=
  l.drop (l.length - n)

-- Precondition: nums contains all integers from 1 to k
def require1 (nums : List Nat) (k : Nat) :=
  containsAllUpToK nums k

def precondition (nums : List Nat) (k : Nat) :=
  require1 nums k

-- Postcondition clauses
-- The result is at most the length of the list
def ensures1 (nums : List Nat) (k : Nat) (result : Nat) :=
  result ≤ nums.length

-- The suffix of length result contains all integers from 1 to k
def ensures2 (nums : List Nat) (k : Nat) (result : Nat) :=
  containsAllUpToK (listSuffix nums result) k

-- The result is minimal: no smaller suffix contains all integers from 1 to k
def ensures3 (nums : List Nat) (k : Nat) (result : Nat) :=
  ∀ m : Nat, m < result → ¬containsAllUpToK (listSuffix nums m) k

def postcondition (nums : List Nat) (k : Nat) (result : Nat) :=
  ensures1 nums k result ∧
  ensures2 nums k result ∧
  ensures3 nums k result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Nat) (k : Nat):
  VerinaSpec.minOperations_precond nums k ↔ LeetProofSpec.precondition nums k := by
  unfold VerinaSpec.minOperations_precond LeetProofSpec.precondition;
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · intro i hi; induction hi.1 <;> aesop;
  · simp +zetaDelta at *;
    exact fun x hx => h _ ⟨ Nat.succ_pos _, Nat.succ_le_of_lt hx ⟩

theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) (h_precond : VerinaSpec.minOperations_precond nums k):
  VerinaSpec.minOperations_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result := by
  -- By definition of `minOperations_postcond`, we know that the result is the minimal number of operations required to collect all numbers from 1 to k.
  unfold VerinaSpec.minOperations_postcond LeetProofSpec.postcondition;
  -- By definition of `take` and `drop`, we can show that the suffix of length `result` is the same as the processed elements in `minOperations_postcond`.
  have h_suffix_eq : ∀ (l : List ℕ) (n : ℕ), List.take n (List.reverse l) = List.reverse (List.drop (List.length l - n) l) := by
    exact?;
  constructor <;> intro h <;> simp_all +decide [ List.mem_map, List.mem_range ];
  · -- By definition of `ensures1`, we know that `result ≤ nums.length`.
    have h_ensures1 : result ≤ nums.length := by
      grind;
    -- By definition of `ensures2`, we know that the suffix of length `result` contains all numbers from 1 to k.
    have h_ensures2 : ∀ i : ℕ, 1 ≤ i ∧ i ≤ k → i ∈ List.drop (nums.length - result) nums := by
      intro i hi; specialize h; rcases hi with ⟨ hi1, hi2 ⟩ ; specialize h; rcases i with ( _ | i ) <;> aesop;
    -- By definition of `ensures3`, we know that no smaller suffix contains all numbers from 1 to k.
    have h_ensures3 : ∀ m : ℕ, m < result → ¬(∀ i : ℕ, 1 ≤ i ∧ i ≤ k → i ∈ List.drop (nums.length - m) nums) := by
      intro m hm_lt hm_all
      have h_contra : ∀ i : ℕ, 1 ≤ i ∧ i ≤ k → i ∈ List.drop (nums.length - (result - 1)) nums := by
        -- Since $m < \text{result}$, we have $m \leq \text{result} - 1$. Therefore, the drop of $m$ elements is a subset of the drop of $(\text{result} - 1)$ elements.
        have h_subset : List.drop (nums.length - m) nums ⊆ List.drop (nums.length - (result - 1)) nums := by
          grind;
        exact fun i hi => h_subset <| hm_all i hi;
      grind;
    exact ⟨ h_ensures1, h_ensures2, h_ensures3 ⟩;
  · -- By definition of `ensures2`, we know that the suffix of length `result` contains all numbers from 1 to k.
    have h_suffix : ∀ x < k, x + 1 ∈ List.drop (List.length nums - result) nums := by
      exact fun x hx => h.2.1 ( x + 1 ) ⟨ by linarith, by linarith ⟩;
    split_ifs <;> simp_all +decide [ List.mem_reverse ];
    · contrapose! h;
      intro h1 h2 h3; specialize h3 ( result - 1 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ; simp_all +decide [ LeetProofSpec.containsAllUpToK ] ;
      obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h3; specialize h ( x - 1 ) ; rcases x with ( _ | x ) <;> simp_all +decide ;
      exact?;
    · linarith [ h_suffix 0 ]