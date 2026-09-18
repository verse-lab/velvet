module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an integer array `nums`, return `true` if any value appears at least twice
in the array, and return `false` if every element is distinct.

The program is expected to run in O(n^2) time and O(1) extra space.
-/

namespace ContainsDuplicate

section Specs

public def HasDuplicate (nums : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat), i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!

public def precondition (_nums : Array Int) : Prop :=
  True

public def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasDuplicate nums) ∧
  (result = false ↔ ¬ HasDuplicate nums)

end Specs

section Implementation

method containsDuplicate (nums : Array Int)
  returns (result : Bool)
  requires valid: precondition nums
  ensures has_duplicate: postcondition nums result
do
  let mut i : Nat := 0
  let mut found : Bool := false
  while' outer_scan: i < nums.size ∧ found = false
    invariant outer_bounds: i ≤ nums.size
    invariant outer_sound: found = true → HasDuplicate nums
    invariant outer_prefix: found = false →
      ∀ a b : Nat, a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!
    decreasing outer_remaining: nums.size - i
    done_with outer_done: i = nums.size ∨ found = true
  do
    let mut j : Nat := i + 1
    while' inner_scan: j < nums.size ∧ found = false
      invariant inner_i_bound: i < nums.size
      invariant inner_j_bound: i + 1 ≤ j ∧ j ≤ nums.size
      invariant inner_sound: found = true → HasDuplicate nums
      invariant inner_prefix: found = false →
        ∀ a b : Nat, a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!
      invariant inner_scan_bound: found = false →
        ∀ b : Nat, i < b → b < j → nums[i]! ≠ nums[b]!
      decreasing inner_remaining: nums.size - j
      done_with inner_done: j = nums.size ∨ found = true
    do
      if eq_elem: nums[i]! = nums[j]! then
        found := true
      j := j + 1
    i := i + 1
  return found

end Implementation

section Proof

theorem outer_exit_postcondition (nums : Array Int) (found : Bool) (i : Nat)
    (hsound : found = true → HasDuplicate nums)
    (hprefix : found = false → ∀ a b : Nat, a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!)
    (hdone : i = nums.size ∨ found = true) :
    postcondition nums found := by
  unfold postcondition
  cases found with
  | false =>
      have hi : i = nums.size := by
        cases hdone with
        | inl h => exact h
        | inr h => contradiction
      have hno : ¬ HasDuplicate nums := by
        intro ⟨a, b, hab, hb, heq⟩
        have ha : a < i := by omega
        exact hprefix rfl a b hab hb ha heq
      simp [hno]
  | true =>
      have hd := hsound rfl
      simp [hd]

prove_correct containsDuplicate by
  velvet_vcgen [containsDuplicate, postcondition] with try finish
  case has_duplicate =>
    rename_i nums
    exact outer_exit_postcondition nums found i outer_sound outer_prefix outer_done
  case inner_sound =>
    intro _
    refine ⟨i, j, by omega, inner_scan.1, eq_elem⟩

end Proof

end ContainsDuplicate
