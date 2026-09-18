module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

/-!
## Program description

Given an array `nums` of integers, return `true` if the array was originally
sorted in non-decreasing order, then rotated some number of positions (including
zero). Otherwise, return `false`.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace CheckIfArrayIsSortedAndRotated

section Specs

public def isDrop (nums : Array Int) (i : Nat) : Prop :=
  nums.size > 0 ∧ i < nums.size ∧ nums[(i + 1) % nums.size]! < nums[i]!

public def rotSortedProp (nums : Array Int) : Prop :=
  nums.size ≤ 1 ∨ (∀ (i : Nat) (j : Nat), isDrop nums i → isDrop nums j → i = j)

public def precondition (_nums : Array Int) : Prop :=
  True

public def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ rotSortedProp nums) ∧
  (result = false ↔ ¬ rotSortedProp nums)

end Specs

section Implementation

method check (nums : Array Int)
  returns (result : Bool)
  requires valid: precondition nums
  ensures sorted_and_rotated: postcondition nums result
do
  let n := nums.size
  if small: n ≤ 1 then
    return true
  else
    let mut drops : Nat := 0
    let mut i : Nat := 0
    while scanning: i < n
      invariant bounds: i ≤ n
      invariant drops_count: drops = (Finset.filter (fun k : Nat => nums[(k + 1) % n]! < nums[k]!) (Finset.range i)).card
      decreasing remaining: n - i
      done_with done: i = n
    do
      let a := nums[i]!
      let b := nums[(i + 1) % n]!
      if drop: b < a then
        drops := drops + 1
      i := i + 1
    if small_drops: drops ≤ 1 then
      return true
    else
      return false

end Implementation

section Proof

theorem drop_add_one (nums : Array Int) (i : Nat)
    (hdrop : nums[(i + 1) % nums.size]! < nums[i]!) :
    (Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range i)).card + 1 =
      (Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range (i + 1))).card := by
  classical
  let P : Nat → Prop := fun k => nums[(k + 1) % nums.size]! < nums[k]!
  have hPi : P i := hdrop
  have hi_not : i ∉ Finset.filter P (Finset.range i) := by
    simp [Finset.mem_range]
  simp [P, Finset.range_add_one, Finset.filter_insert, hPi, hi_not, Finset.card_insert_of_notMem]

theorem no_drop_add_one (nums : Array Int) (i : Nat)
    (hndrop : ¬ nums[(i + 1) % nums.size]! < nums[i]!) :
    (Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range i)).card =
      (Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range (i + 1))).card := by
  classical
  let P : Nat → Prop := fun k => nums[(k + 1) % nums.size]! < nums[k]!
  have hPi : ¬ P i := hndrop
  simp [P, Finset.range_add_one, Finset.filter_insert, hPi]

theorem postcondition_true_of_drops_le_one (nums : Array Int) (i : Nat)
    (_hbound : i ≤ nums.size) (hdone : i = nums.size)
    (hcard : (Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range i)).card ≤ 1) :
    postcondition nums true := by
  classical
  subst hdone
  have hrot : rotSortedProp nums := by
    right
    intro j1 j2 hj1 hj2
    rcases hj1 with ⟨_, hj1_lt, hj1_drop⟩
    rcases hj2 with ⟨_, hj2_lt, hj2_drop⟩
    have huniq : ∀ {a b : Nat},
        a ∈ Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range nums.size) →
        b ∈ Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range nums.size) →
        a = b :=
      Finset.card_le_one_iff.mp hcard
    have hj1_mem : j1 ∈ Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range nums.size) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hj1_lt, hj1_drop⟩
    have hj2_mem : j2 ∈ Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range nums.size) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hj2_lt, hj2_drop⟩
    exact huniq hj1_mem hj2_mem
  unfold postcondition
  simp [hrot]

theorem postcondition_false_of_drops_gt_one (nums : Array Int) (i : Nat)
    (_hbound : i ≤ nums.size) (hdone : i = nums.size)
    (hcard : 1 < (Finset.filter (fun k => nums[(k + 1) % nums.size]! < nums[k]!) (Finset.range i)).card) :
    postcondition nums false := by
  classical
  subst hdone
  rcases Finset.one_lt_card.mp hcard with ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_filter, Finset.mem_range] at ha hb
  have ha_drop : isDrop nums a := ⟨by omega, ha.1, ha.2⟩
  have hb_drop : isDrop nums b := ⟨by omega, hb.1, hb.2⟩
  have hnot : ¬ rotSortedProp nums := by
    intro hrot
    rcases hrot with hle1 | hunique
    · have h1 : a < nums.size := ha.1
      omega
    · exact hab (hunique a b ha_drop hb_drop)
  unfold postcondition
  simp [hnot]

prove_correct check by
  velvet_vcgen [check, postcondition] with try finish
  case sorted_and_rotated =>
    unfold postcondition rotSortedProp
    simp [small]
  case drops_count =>
    rename_i nums
    rw [← drop_add_one]
    · omega
    · exact drop
  case drops_count =>
    rename_i nums
    rw [← no_drop_add_one]
    · omega
    · exact drop
  case sorted_and_rotated =>
    rename_i nums
    exact postcondition_true_of_drops_le_one nums i bounds done (by omega)
  case sorted_and_rotated =>
    rename_i nums
    exact postcondition_false_of_drops_gt_one nums i bounds done (by omega)

end Proof

end CheckIfArrayIsSortedAndRotated
