module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
## Program description

Product of Array Except Self: for each index `i`, return the product of all
input elements except the one at `i`.

1. Input is an array of integers `nums`.
2. Output is an array `answer` of the same length as `nums`.
3. For every valid index `i`, `answer[i]` equals the product of all `nums[j]` with `j ≠ i`.
4. The relative order of indices is preserved: output position `i` corresponds to input position `i`.
5. Multiplication uses the integer multiplicative identity 1 for the excluded element.
6. Edge cases:
   - If the array is empty, the output is empty.
   - If the array has one element, the only output value is 1 (product over an empty set).
   - Zeros and negative values must be handled correctly.
7. The problem statement guarantees that any prefix or suffix product fits in a 32-bit signed integer; we capture this as an input precondition.
8. The algorithmic requirement "no division" is an implementation constraint; the mathematical result is uniquely determined by the product definition.

The program is expected to run in O(n) time and O(1) extra space, excluding the returned array.
-/

namespace ProductOfArrayExceptSelf

section Specs

public def int32Min : Int := (-2147483648)
public def int32Max : Int := (2147483647)

public def InInt32 (z : Int) : Prop := int32Min ≤ z ∧ z ≤ int32Max

-- Product of the first k elements (a prefix), where k is intended to satisfy k ≤ nums.size.
public def prefixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range k).prod (fun (j : Nat) => nums[j]!)

-- Product of the suffix starting at index k, where k is intended to satisfy k ≤ nums.size.
public def suffixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range (nums.size - k)).prod (fun (t : Nat) => nums[k + t]!)

-- Product of all elements except the element at index i.
public def prodExcept (nums : Array Int) (i : Nat) : Int :=
  (Finset.range nums.size).prod (fun (j : Nat) => if j = i then (1 : Int) else nums[j]!)

-- Preconditions
-- We encode the stated 32-bit safety guarantee for any prefix and suffix product.
public def precondition (nums : Array Int) : Prop :=
  (∀ (k : Nat), k ≤ nums.size → InInt32 (prefixProd nums k)) ∧
  (∀ (k : Nat), k ≤ nums.size → InInt32 (suffixProd nums k))

-- Postconditions
-- 1) Output length matches input length.
-- 2) For each valid index i, result[i] is the product of all input elements except nums[i].
public def postcondition (nums : Array Int) (answer : Array Int) : Prop :=
  answer.size = nums.size ∧
  (∀ (i : Nat), i < nums.size → answer[i]! = prodExcept nums i)

end Specs

section Implementation

method productOfArrayExceptSelf (nums : Array Int)
  returns (answer : Array Int)
  requires valid_bounds: precondition nums
  ensures correct_products: postcondition nums answer
do
  let n := nums.size
  let mut ans : Array Int := Array.replicate n 1
  let mut i : Nat := 0
  let mut pref : Int := 1
  while prefix_pass: i < n
    invariant ans_size: ans.size = n
    invariant i_bounds: i ≤ n
    invariant pref_val: pref = prefixProd nums i
    invariant ans_prefix: ∀ k : Nat, k < i → ans[k]! = prefixProd nums k
    decreasing i_remaining: n - i
    done_with prefix_done: i = n
  do
    ans := ans.set! i pref
    pref := pref * nums[i]!
    i := i + 1

  let mut j : Nat := n
  let mut suff : Int := 1
  while suffix_pass: j > 0
    invariant ans_size2: ans.size = n
    invariant j_bounds: j ≤ n
    invariant suff_val: suff = suffixProd nums j
    invariant ans_prefix2: ∀ k : Nat, k < j → ans[k]! = prefixProd nums k
    invariant ans_done: ∀ k : Nat, j ≤ k ∧ k < n → ans[k]! = prodExcept nums k
    decreasing j_remaining: j
    done_with suffix_done: j = 0
  do
    j := j - 1
    ans := ans.set! j (ans[j]! * suff)
    suff := suff * nums[j]!

  return ans

end Implementation

section Proof

@[simp] theorem prefixProd_zero (nums : Array Int) : prefixProd nums 0 = 1 := by
  simp [prefixProd]

theorem prefixProd_succ (nums : Array Int) (i : Nat) :
    prefixProd nums (i + 1) = prefixProd nums i * nums[i]! := by
  simp [prefixProd, Finset.prod_range_succ]

@[simp] theorem suffixProd_self (nums : Array Int) : suffixProd nums nums.size = 1 := by
  simp [suffixProd]

theorem suffixProd_step (nums : Array Int) (j : Nat) (hj : 0 < j) (hjn : j ≤ nums.size) :
    suffixProd nums (j - 1) = suffixProd nums j * nums[j - 1]! := by
  unfold suffixProd
  have hlen : nums.size - (j - 1) = (nums.size - j) + 1 := by omega
  rw [hlen]
  have hsucc := (Finset.prod_range_succ' (fun t => nums[j - 1 + t]!) (nums.size - j))
  have heq : (fun t => nums[j - 1 + (t + 1)]!) = (fun t => nums[j + t]!) := by
    funext t
    congr 1
    omega
  rw [heq] at hsucc
  have hzero : nums[j - 1 + 0]! = nums[j - 1]! := by simp
  rw [hsucc, hzero]

theorem prodExcept_eq_prefix_mul_suffix (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    prodExcept nums i = prefixProd nums i * suffixProd nums (i + 1) := by
  unfold prodExcept prefixProd suffixProd
  let f : Nat → Int := fun j => if j = i then 1 else nums[j]!
  have hsplit : (Finset.range nums.size).prod f =
      (Finset.range i).prod f * (Finset.range (nums.size - i)).prod (fun x => f (i + x)) := by
    have h := Finset.prod_range_add f i (nums.size - i)
    have heq : i + (nums.size - i) = nums.size := by omega
    rw [heq] at h
    exact h
  have hfirst : (Finset.range i).prod f = (Finset.range i).prod (fun j => nums[j]!) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hx_lt : x < i := Finset.mem_range.mp hx
    have hx_ne : x ≠ i := by omega
    simp [f, hx_ne]
  have hsecond : (Finset.range (nums.size - i)).prod (fun x => f (i + x)) =
      (Finset.range (nums.size - (i + 1))).prod (fun t => nums[i + 1 + t]!) := by
    have hlen : nums.size - i = (nums.size - (i + 1)) + 1 := by omega
    rw [hlen]
    have hsucc := Finset.prod_range_succ' (fun x => f (i + x)) (nums.size - (i + 1))
    have hf0 : f (i + 0) = 1 := by
      simp [f]
    have hf_step : (fun t => f (i + (t + 1))) = (fun t => nums[i + 1 + t]!) := by
      funext t
      have hne : i + (t + 1) ≠ i := by omega
      have heq2 : i + (t + 1) = i + 1 + t := by omega
      have hne' : i + 1 + t ≠ i := by omega
      simp [f, heq2, hne']
    rw [hf_step] at hsucc
    rw [hsucc, hf0, mul_one]
  rw [hsplit, hfirst, hsecond]

prove_correct productOfArrayExceptSelf by
  velvet_vcgen [productOfArrayExceptSelf, postcondition]
  all_goals try simp_all [prefixProd_zero, suffixProd_self]
  all_goals try omega
  all_goals expose_names
  case correct_products =>
    unfold postcondition
    refine ⟨ans_size2, ?_⟩
    intro k hk
    simpa [getElem!_pos ans k (by omega)] using ans_done k hk
  case suff_val =>
    exact (suffixProd_step nums j suffix_pass j_bounds).symm
  case ans_prefix2 =>
    intro k hk
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne (by omega : j - 1 ≠ k)]
    simpa only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] using
      ans_prefix2 k (by omega)
  case ans_done =>
    intro k hp hq
    by_cases hki : k = j - 1
    · subst k
      have hbound : j - 1 < ans.size := by omega
      rw [Array.getElem_setIfInBounds_self]
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using
        (prodExcept_eq_prefix_mul_suffix nums (j - 1) (by omega)).symm
    · rw [Array.getElem_setIfInBounds_ne (by omega) (Ne.symm hki)]
      exact ans_done k (by omega) hq
  case pref_val =>
    simpa [getElem!_pos nums i prefix_pass] using (prefixProd_succ nums i).symm
  case ans_prefix =>
    intro k hk
    by_cases hki : k = i
    · subst k
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt (by omega : i < ans.size), Option.getD_some]
    · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne (Ne.symm hki)]
      simpa only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] using
        ans_prefix k (by omega)

end Proof

end ProductOfArrayExceptSelf
