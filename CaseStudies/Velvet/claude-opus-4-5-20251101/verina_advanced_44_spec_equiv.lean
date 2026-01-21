/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 56793fff-edd8-42f2-8c39-9f93a0fc2c10

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (k : Int):
  VerinaSpec.maxSubarraySumDivisibleByK_precond arr k ↔ LeetProofSpec.precondition arr k
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  k > 0

-- !benchmark @end precond

@[reducible]
def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  -- !benchmark @start postcond
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k.toNat = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.toList.sum)
  -- No valid subarrays -> result is 0
  (subarraySums.length = 0 → result = 0) ∧
  -- Valid subarrays exist -> result is the maximum sum
  (subarraySums.length > 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: compute sum of array elements from index start to stop (exclusive)
def subarraySum (arr : Array Int) (start : Nat) (stop : Nat) : Int :=
  if stop ≤ start then 0
  else if stop > arr.size then 0
  else (arr.toList.drop start).take (stop - start) |>.foldl (· + ·) 0

-- Helper: check if a subarray is valid (has length divisible by k)
def isValidSubarray (arr : Array Int) (k : Int) (start : Nat) (stop : Nat) : Bool :=
  start ≤ stop ∧ stop ≤ arr.size ∧ k > 0 ∧ (stop - start) % k.toNat = 0

-- Helper: predicate for a valid subarray with a specific sum
def validSubarrayWithSum (arr : Array Int) (k : Int) (s : Int) : Prop :=
  ∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧
    (stop - start) % k.toNat = 0 ∧ subarraySum arr start stop = s

-- Precondition: k must be at least 1
def precondition (arr : Array Int) (k : Int) : Prop :=
  k ≥ 1

-- Postcondition: result is the maximum sum of a valid subarray, or 0 if none exists
def postcondition (arr : Array Int) (k : Int) (result : Int) : Prop :=
  -- Case 1: No valid subarray exists (with positive length) → result is 0
  ((¬∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0) → result = 0) ∧
  -- Case 2: Valid subarrays exist → result is the maximum sum, or 0 if all sums are negative
  ((∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0) →
    -- result is either 0 (if all valid subarray sums are ≤ 0) or the maximum valid subarray sum
    ((result = 0 ∧ ∀ start stop : Nat, start < stop → stop ≤ arr.size →
      (stop - start) % k.toNat = 0 → subarraySum arr start stop ≤ 0) ∨
     (result > 0 ∧ validSubarrayWithSum arr k result ∧
      ∀ start stop : Nat, start < stop → stop ≤ arr.size →
        (stop - start) % k.toNat = 0 → subarraySum arr start stop ≤ result)))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (k : Int):
  VerinaSpec.maxSubarraySumDivisibleByK_precond arr k ↔ LeetProofSpec.precondition arr k := by
  exact iff_of_eq rfl

theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Int):
  VerinaSpec.maxSubarraySumDivisibleByK_postcond arr k result ↔ LeetProofSpec.postcondition arr k result := by
  sorry
