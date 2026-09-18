module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an array of integers `nums`, calculate the pivot index of this array.

The pivot index is the index where the sum of all the numbers strictly to the
left of the index is equal to the sum of all the numbers strictly to the index's
right.

If the index is on the left edge of the array, then the left sum is `0` because
there are no elements to the left. This also applies to the right edge of the
array.

Return the leftmost pivot index. If no such index exists, return `-1`.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace FindPivotIndex

section Specs

public def arraySum (a : Array Int) : Int :=
  a.foldl (fun acc x => acc + x) 0

public def arraySumRange (a : Array Int) (start : Nat) (stop : Nat) : Int :=
  (a.extract start stop).foldl (fun acc x => acc + x) 0

public def isPivotIndex (nums : Array Int) (i : Nat) : Prop :=
  i < nums.size ∧
  arraySumRange nums 0 i = arraySumRange nums (i + 1) nums.size

public def precondition (_nums : Array Int) : Prop :=
  True

public def postcondition (nums : Array Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ i : Nat, i < nums.size → ¬ isPivotIndex nums i)) ∨
  (∃ i : Nat,
      i < nums.size ∧
      result = Int.ofNat i ∧
      isPivotIndex nums i ∧
      (∀ j : Nat, j < i → ¬ isPivotIndex nums j))

end Specs

section Implementation

method pivotIndex (nums : Array Int)
  returns (result : Int)
  requires valid: precondition nums
  ensures pivot: postcondition nums result
do
  let total : Int := arraySum nums
  let mut left : Int := 0
  let mut i : Nat := 0
  let mut ans : Int := (-1)
  let mut found : Bool := false
  while' scanning: i < nums.size ∧ found = false
    invariant bounds: i ≤ nums.size
    invariant left_sum: left = arraySumRange nums 0 i
    invariant ans_neg_one: found = false → ans = -1
    invariant no_pivot_before: found = false → ∀ j : Nat, j < i → ¬ isPivotIndex nums j
    invariant found_pivot: found = true →
      i < nums.size ∧
      ans = Int.ofNat i ∧
      isPivotIndex nums i ∧
      (∀ j : Nat, j < i → ¬ isPivotIndex nums j)
    decreasing remaining: if found then 0 else nums.size - i
    done_with done: i = nums.size ∨ found = true
  do
    let x := nums[i]!
    let right := total - left - x
    if is_pivot: left = right then
      ans := Int.ofNat i
      found := true
    else
      left := left + x
      i := i + 1
  return ans

end Implementation

section Proof

theorem arraySumRange_toList (nums : Array Int) (start stop : Nat) :
    arraySumRange nums start stop =
      (nums.toList.extract start stop).foldl (fun acc x => acc + x) 0 := by
  unfold arraySumRange
  calc
    (nums.extract start stop).foldl (fun acc x => acc + x) 0 =
        (nums.extract start stop).toList.foldl (fun acc x => acc + x) 0 := by
      simpa using (Array.foldl_toList (xs := nums.extract start stop)
        (f := fun acc x => acc + x) (init := (0 : Int))).symm
    _ = _ := by simp [Array.toList_extract]

theorem arraySum_toList (nums : Array Int) :
    arraySum nums = nums.toList.foldl (fun acc x => acc + x) 0 := by
  unfold arraySum
  simp [Array.foldl_toList]

@[simp] theorem arraySumRange_zero_zero (nums : Array Int) :
    arraySumRange nums 0 0 = 0 := by
  rw [arraySumRange_toList]
  simp [List.extract]

theorem list_foldl_add (l : List Int) (c : Int) :
    l.foldl (fun acc x => acc + x) c = c + l.foldl (fun acc x => acc + x) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons x xs ih =>
    have h1 := ih (c + x)
    have h2 := ih x
    have h0 : (0 : Int) + x = x := by omega
    simp only [List.foldl_cons, h0]
    rw [h1, h2]
    omega

theorem list_foldl_append (l1 l2 : List Int) :
    (l1 ++ l2).foldl (fun acc x => acc + x) 0 =
      l1.foldl (fun acc x => acc + x) 0 + l2.foldl (fun acc x => acc + x) 0 := by
  rw [List.foldl_append, list_foldl_add]

theorem toList_take_succ (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    nums.toList.take (i + 1) = nums.toList.take i ++ [nums[i]!] := by
  rw [List.take_add_one]
  have hi_len : i < nums.toList.length := by simpa using hi
  have h_get : nums.toList[i]? = some nums[i]! := by
    rw [List.getElem?_eq_getElem hi_len]
    congr 1
    rw [Array.getElem_toList]
    exact (getElem!_pos nums i hi).symm
  rw [h_get]
  rfl

theorem arraySumRange_succ (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    arraySumRange nums 0 (i + 1) = arraySumRange nums 0 i + nums[i]! := by
  rw [arraySumRange_toList, arraySumRange_toList]
  have h1 : nums.toList.extract 0 (i + 1) = nums.toList.take (i + 1) := by
    simp [List.extract]
  have h2 : nums.toList.extract 0 i = nums.toList.take i := by
    simp [List.extract]
  rw [h1, h2, toList_take_succ nums i hi, list_foldl_append]
  simp

theorem right_sum_eq (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    arraySum nums - arraySumRange nums 0 i - nums[i]! = arraySumRange nums (i + 1) nums.size := by
  have h1 : nums.toList.extract 0 i = nums.toList.take i := by simp [List.extract]
  have h2 : nums.toList.extract (i + 1) nums.size = nums.toList.drop (i + 1) := by
    unfold List.extract
    have hlen : nums.size - (i + 1) = (nums.toList.drop (i + 1)).length := by simp [nums.length_toList]
    rw [hlen, List.take_length]
  have hdecomp : nums.toList = nums.toList.take i ++ [nums[i]!] ++ nums.toList.drop (i + 1) := by
    have ht := toList_take_succ nums i hi
    have hd := (List.take_append_drop (i + 1) nums.toList).symm
    rw [ht] at hd
    exact hd
  have hsplit : arraySum nums = arraySumRange nums 0 i + nums[i]! + arraySumRange nums (i + 1) nums.size := by
    rw [arraySum_toList, arraySumRange_toList, arraySumRange_toList, h1, h2]
    have hfold : nums.toList.foldl (fun acc x => acc + x) 0 =
        (nums.toList.take i ++ [nums[i]!] ++ nums.toList.drop (i + 1)).foldl (fun acc x => acc + x) 0 := by
      rw [← hdecomp]
    rw [hfold, list_foldl_append, list_foldl_append]
    simp
  omega

theorem exit_postcondition (nums : Array Int) (ans : Int) (i : Nat) (found : Bool)
    (ans_neg_one : found = false → ans = -1)
    (no_pivot_before : found = false → ∀ j, j < i → ¬isPivotIndex nums j)
    (found_pivot : found = true → i < nums.size ∧ ans = Int.ofNat i ∧ isPivotIndex nums i ∧ ∀ j, j < i → ¬isPivotIndex nums j)
    (done : i = nums.size ∨ found = true) :
    postcondition nums ans := by
  unfold postcondition
  cases found with
  | false =>
    have hi : i = nums.size := by
      cases done with
      | inl h => exact h
      | inr h => contradiction
    have hans : ans = -1 := ans_neg_one rfl
    have hno : ∀ j < nums.size, ¬isPivotIndex nums j := by
      intro j hj
      have hj_i : j < i := by omega
      exact no_pivot_before rfl j hj_i
    left
    exact ⟨hans, hno⟩
  | true =>
    obtain ⟨hi, hans, hpiv, hno⟩ := found_pivot rfl
    right
    exact ⟨i, hi, hans, hpiv, hno⟩

theorem step_found_pivot (nums : Array Int) (left : Int) (i : Nat) (found : Bool)
    (hi : i < nums.size)
    (hfound : found = false)
    (left_sum : left = arraySumRange nums 0 i)
    (no_pivot_before : found = false → ∀ j, j < i → ¬isPivotIndex nums j)
    (is_pivot : left = arraySum nums - left - nums[i]!) :
    i < nums.size ∧ Int.ofNat i = Int.ofNat i ∧ isPivotIndex nums i ∧ ∀ j, j < i → ¬isPivotIndex nums j := by
  have hright : arraySum nums - left - nums[i]! = arraySumRange nums (i + 1) nums.size := by
    rw [left_sum]
    exact right_sum_eq nums i hi
  have hpivot : arraySumRange nums 0 i = arraySumRange nums (i + 1) nums.size := by
    omega
  have his_pivot : isPivotIndex nums i := ⟨hi, hpivot⟩
  have hno : ∀ j, j < i → ¬isPivotIndex nums j := no_pivot_before hfound
  exact ⟨hi, rfl, his_pivot, hno⟩

theorem step_left_sum (nums : Array Int) (left : Int) (i : Nat)
    (hi : i < nums.size)
    (left_sum : left = arraySumRange nums 0 i) :
    left + nums[i]! = arraySumRange nums 0 (i + 1) := by
  have h_succ := arraySumRange_succ nums i hi
  rw [left_sum, h_succ]

theorem step_no_pivot_before (nums : Array Int) (left : Int) (i : Nat) (found : Bool)
    (hi : i < nums.size)
    (hfound : found = false)
    (left_sum : left = arraySumRange nums 0 i)
    (no_pivot_before : found = false → ∀ j, j < i → ¬isPivotIndex nums j)
    (is_pivot : ¬left = arraySum nums - left - nums[i]!) :
    ∀ j, j < i + 1 → ¬isPivotIndex nums j := by
  intro j hj
  have hj_cases : j < i ∨ j = i := by omega
  cases hj_cases with
  | inl hj_lt => exact no_pivot_before hfound j hj_lt
  | inr hj_eq =>
    subst j
    intro ⟨_, h_piv⟩
    have hright : arraySum nums - left - nums[i]! = arraySumRange nums (i + 1) nums.size := by
      rw [left_sum]
      exact right_sum_eq nums i hi
    exact is_pivot (by omega)

prove_correct pivotIndex by
  velvet_vcgen [pivotIndex, precondition, postcondition] with try finish
  case left_sum =>
    exact (arraySumRange_zero_zero _).symm
  case pivot =>
    rename_i nums
    exact exit_postcondition nums ans i found ans_neg_one no_pivot_before found_pivot done
  case found_pivot =>
    rename_i nums
    intro _
    exact step_found_pivot nums left i found scanning.1 scanning.2 left_sum no_pivot_before is_pivot
  case left_sum =>
    rename_i nums
    exact step_left_sum nums left i scanning.1 left_sum
  case no_pivot_before =>
    rename_i nums
    intro _
    exact step_no_pivot_before nums left i found scanning.1 scanning.2 left_sum no_pivot_before is_pivot

end Proof

end FindPivotIndex
