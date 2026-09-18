module

public import Velvet
public meta import Velvet

/-!
## Program description

An array is monotonic if it is either monotone increasing or monotone
decreasing.

An array `nums` is monotone increasing if for all `i <= j`, `nums[i] <= nums[j]`.
An array `nums` is monotone decreasing if for all `i <= j`, `nums[i] >= nums[j]`.

Given an integer array `nums`, return `true` if the given array is monotonic, or
`false` otherwise.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace MonotonicArray

section Specs

public def monotoneIncreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≤ nums[j]!

public def monotoneDecreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≥ nums[j]!

public def monotonic (nums : Array Int) : Prop :=
  monotoneIncreasing nums ∨ monotoneDecreasing nums

public def precondition (_nums : Array Int) : Prop :=
  True

public def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ monotonic nums) ∧
  (result = false ↔ ¬ monotonic nums)

end Specs

section Implementation

method isMonotonic (nums : Array Int)
  returns (result : Bool)
  requires valid: precondition nums
  ensures is_monotonic: postcondition nums result
do
  if small: nums.size ≤ 1 then
    return true
  else
    let mut inc : Bool := true
    let mut dec : Bool := true
    let mut i : Nat := 1
    while' scanning: i < nums.size
      invariant bounds: 1 ≤ i ∧ i ≤ nums.size
      invariant inc_prefix: inc = true → ∀ a b : Nat, a < i → b < i → a ≤ b → nums[a]! ≤ nums[b]!
      invariant dec_prefix: dec = true → ∀ a b : Nat, a < i → b < i → a ≤ b → nums[a]! ≥ nums[b]!
      invariant global_inc: monotoneIncreasing nums → inc = true
      invariant global_dec: monotoneDecreasing nums → dec = true
      decreasing remaining: nums.size - i
      done_with done: i = nums.size
    do
      let prev := nums[i - 1]!
      let cur := nums[i]!
      if prev_lt_cur: prev < cur then
        dec := false
      else if prev_gt_cur: prev > cur then
        inc := false
      i := i + 1
    return (inc || dec)

end Implementation

section Proof

theorem small_is_monotonic (nums : Array Int) (h : nums.size ≤ 1) :
    monotoneIncreasing nums := by
  intro i j hi hj _
  have : i = j := by omega
  subst this
  omega

theorem small_postcondition (nums : Array Int) (h : nums.size ≤ 1) :
    postcondition nums true := by
  have hm : monotonic nums := Or.inl (small_is_monotonic nums h)
  simp [postcondition, hm]

theorem exit_postcondition (nums : Array Int) (inc dec : Bool) (i : Nat)
    (hinc : inc = true → ∀ a b : Nat, a < i → b < i → a ≤ b → nums[a]! ≤ nums[b]!)
    (hdec : dec = true → ∀ a b : Nat, a < i → b < i → a ≤ b → nums[a]! ≥ nums[b]!)
    (ginc : monotoneIncreasing nums → inc = true)
    (gdec : monotoneDecreasing nums → dec = true)
    (hdone : i = nums.size) :
    postcondition nums (inc || dec) := by
  unfold postcondition monotonic
  cases h_inc : inc <;> cases h_dec : dec
  · simp
    constructor
    · intro h
      have := ginc h
      simp_all
    · intro h
      have := gdec h
      simp_all
  · simp
    have hd : monotoneDecreasing nums := by
      intro a b ha hb hab
      rw [← hdone] at ha hb
      exact hdec h_dec a b ha hb hab
    simp [hd]
  · simp
    have hi : monotoneIncreasing nums := by
      intro a b ha hb hab
      rw [← hdone] at ha hb
      exact hinc h_inc a b ha hb hab
    simp [hi]
  · simp
    have hi : monotoneIncreasing nums := by
      intro a b ha hb hab
      rw [← hdone] at ha hb
      exact hinc h_inc a b ha hb hab
    simp [hi]

prove_correct isMonotonic by
  velvet_vcgen [isMonotonic, postcondition] with try finish
  case is_monotonic =>
    exact small_postcondition _ small
  case is_monotonic =>
    rename_i nums
    exact exit_postcondition nums inc dec i inc_prefix dec_prefix global_inc global_dec done
  case global_dec =>
    rename_i nums
    intro hdec
    have hbound1 : i - 1 < nums.size := by omega
    have hbound2 : i < nums.size := scanning
    have hle : nums[i - 1]! ≥ nums[i]! := hdec (i - 1) i hbound1 hbound2 (by omega)
    omega
  case global_inc =>
    rename_i nums
    intro hinc
    have hbound1 : i - 1 < nums.size := by omega
    have hbound2 : i < nums.size := scanning
    have hle : nums[i - 1]! ≤ nums[i]! := hinc (i - 1) i hbound1 hbound2 (by omega)
    omega

end Proof

end MonotonicArray
