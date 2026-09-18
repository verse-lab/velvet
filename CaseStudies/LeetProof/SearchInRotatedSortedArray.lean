module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.List.Rotate
public import Mathlib.Order.Basic

/-!
## Program description

Return the unique index of `target` in a nonempty, possibly rotated,
strictly-increasing integer array, or `-1` if it is absent. The implementation
performs binary search directly on the input array. The program is expected to
run in O(log n) time and O(1) extra space.
-/

namespace SearchInRotatedSortedArray

section Specs

public def isStrictSorted (nums : Array Int) : Prop :=
  nums.toList.Pairwise (· < ·)

public def isRotationOfStrictSorted (nums : Array Int) : Prop :=
  ∃ base : Array Int,
    isStrictSorted base ∧ base.toList.Nodup ∧ base.toList.IsRotated nums.toList

public def inArray (nums : Array Int) (x : Int) : Prop :=
  x ∈ nums

public def precondition (nums : Array Int) (_target : Int) : Prop :=
  nums.size > 0 ∧ nums.toList.Nodup ∧ isRotationOfStrictSorted nums

public def postcondition (nums : Array Int) (target result : Int) : Prop :=
  (result = -1 ∧ ¬inArray nums target) ∨
  (∃ i,
    i < nums.size ∧
    nums[i]? = some target ∧
    result = Int.ofNat i ∧
    ∀ j, j < nums.size → nums[j]? = some target → j = i)

end Specs

section Implementation

method search (nums : Array Int) (target : Int)
  returns (result : Int)
  requires input_shape: precondition nums target
  ensures found_or_absent: postcondition nums target result
do
  let mut lo : Nat := 0
  let mut hi : Nat := nums.size
  let mut found : Option Nat := none
  while' active: lo < hi ∧ found = none
    invariant bounds: lo ≤ hi ∧ hi ≤ nums.size
    invariant found_valid:
      ∀ i, found = some i → i < nums.size ∧ nums[i]! = target
    invariant candidates: found = none →
      ∀ i, i < nums.size → nums[i]! = target → lo ≤ i ∧ i < hi
    decreasing width: hi - lo
    done_with exhausted: lo = hi ∨ found ≠ none
  do
    let mid := lo + (hi - lo) / 2
    if at_mid: nums[mid]! = target then
      found := some mid
      hi := lo
    else
      if left_sorted: nums[lo]! ≤ nums[mid]! then
        if target_in_left: nums[lo]! ≤ target ∧ target < nums[mid]! then
          hi := mid
        else
          lo := mid + 1
      else
        if target_in_right: nums[mid]! < target ∧ target ≤ nums[hi - 1]! then
          lo := mid + 1
        else
          hi := mid
  match found with
  | some i => return Int.ofNat i
  | none => return -1

end Implementation

section Proof

theorem rotation_order_model (nums : Array Int) (hpos : 0 < nums.size)
    (hrot : isRotationOfStrictSorted nums) :
    ∃ p, p ≤ nums.size ∧
      ∀ a b, a < nums.size → b < nums.size →
        (nums[a]! ≤ nums[b]! ↔
          (a + p) % nums.size ≤ (b + p) % nums.size) := by
  rcases hrot with ⟨base, hsorted, _hnodup, hrotation⟩
  rcases List.isRotated_iff_mod.mp hrotation with ⟨p, hp, hrotate⟩
  have hlen : base.size = nums.size := by
    have := congrArg List.length hrotate
    simpa using this
  have hlenList : base.toList.length = nums.toList.length := by simp [hlen]
  refine ⟨p, by simpa [hlen] using hp, ?_⟩
  intro a b ha hb
  have hbase : base.toList.Pairwise (· < ·) := hsorted
  rw [List.pairwise_iff_getElem] at hbase
  let ra := (a + p) % nums.size
  let rb := (b + p) % nums.size
  have hra : ra < base.toList.length := by
    simp [ra, hlen]
    exact Nat.mod_lt _ hpos
  have hrb : rb < base.toList.length := by
    simp [rb, hlen]
    exact Nat.mod_lt _ hpos
  have hva : nums[a]! = base.toList[ra] := by
    have haBase : a < base.toList.length := by
      change a < base.size
      rw [hlen]
      exact ha
    have hg := List.getElem?_rotate (l := base.toList) (n := p) (m := a) haBase
    have heq := congrArg (fun l : List Int => l[a]?) hrotate
    rw [hg] at heq
    rw [getElem!_pos nums a ha]
    rw [hlenList] at heq
    change base.toList[ra]? = nums.toList[a]? at heq
    rw [List.getElem?_eq_getElem hra,
      List.getElem?_eq_getElem (by simpa using ha)] at heq
    exact Option.some.inj heq.symm
  have hvb : nums[b]! = base.toList[rb] := by
    have hbBase : b < base.toList.length := by
      change b < base.size
      rw [hlen]
      exact hb
    have hg := List.getElem?_rotate (l := base.toList) (n := p) (m := b) hbBase
    have heq := congrArg (fun l : List Int => l[b]?) hrotate
    rw [hg] at heq
    rw [getElem!_pos nums b hb]
    rw [hlenList] at heq
    change base.toList[rb]? = nums.toList[b]? at heq
    rw [List.getElem?_eq_getElem hrb,
      List.getElem?_eq_getElem (by simpa using hb)] at heq
    exact Option.some.inj heq.symm
  rw [hva, hvb]
  constructor
  · intro hab
    by_contra hn
    have hr : rb < ra := by omega
    have hv := hbase rb ra hrb hra hr
    omega
  · intro hr
    rcases lt_or_eq_of_le hr with hr | hr
    · exact (hbase ra rb hra hrb hr).le
    · have hr' : ra = rb := by simpa [ra, rb] using hr
      have hop := congrArg (fun k => base.toList[k]?) hr'
      rw [List.getElem?_eq_getElem hra, List.getElem?_eq_getElem hrb] at hop
      exact le_of_eq (Option.some.inj hop)

theorem rotated_index (n p k : Nat) (hp : p ≤ n) (hk : k < n) :
    (k + p) % n = if k < n - p then k + p else k - (n - p) := by
  split
  · apply Nat.mod_eq_of_lt
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt]
    · omega
    · omega

theorem rotated_search_partition (nums : Array Int)
    (hpos : 0 < nums.size) (hrot : isRotationOfStrictSorted nums)
    (lo mid hi i : Nat)
    (hlo : lo < nums.size) (hmid : mid < nums.size)
    (hh : hi - 1 < nums.size) (hiIdx : i < nums.size)
    (hlm : lo ≤ mid) (hmh : mid < hi) (hli : lo ≤ i) (hih : i < hi)
    (hne : nums[mid]! ≠ nums[i]!) :
    ((nums[lo]! ≤ nums[mid]! ∧
        nums[lo]! ≤ nums[i]! ∧ nums[i]! < nums[mid]!) → i < mid) ∧
    ((nums[lo]! ≤ nums[mid]! ∧
        ¬(nums[lo]! ≤ nums[i]! ∧ nums[i]! < nums[mid]!)) → mid < i) ∧
    ((¬nums[lo]! ≤ nums[mid]! ∧
        nums[mid]! < nums[i]! ∧ nums[i]! ≤ nums[hi - 1]!) → mid < i) ∧
    ((¬nums[lo]! ≤ nums[mid]! ∧
        ¬(nums[mid]! < nums[i]! ∧ nums[i]! ≤ nums[hi - 1]!)) → i < mid) := by
  rcases rotation_order_model nums hpos hrot with ⟨p, hp, hord⟩
  have hpq : p + (nums.size - p) = nums.size := Nat.add_sub_of_le hp
  let r : Nat → Nat := fun k => (k + p) % nums.size
  have hle (a b : Nat) (ha : a < nums.size) (hb : b < nums.size) :
      nums[a]! ≤ nums[b]! ↔ r a ≤ r b := by
    simpa [r] using hord a b ha hb
  have hlt (a b : Nat) (ha : a < nums.size) (hb : b < nums.size) :
      nums[a]! < nums[b]! ↔ r a < r b := by
    rw [lt_iff_not_ge, lt_iff_not_ge, hle b a hb ha]
  have hr (k : Nat) (hk : k < nums.size) :
      r k = if k < nums.size - p then k + p else k - (nums.size - p) := by
    exact rotated_index nums.size p k hp hk
  have hmi : mid ≠ i := by
    intro heq
    subst i
    exact hne rfl
  clear hne
  constructor
  · rintro ⟨hleft, hlow, hupp⟩
    rw [hle lo mid hlo hmid] at hleft
    rw [hle lo i hlo hiIdx] at hlow
    rw [hlt i mid hiIdx hmid] at hupp
    rw [hr lo hlo, hr mid hmid] at hleft
    rw [hr lo hlo, hr i hiIdx] at hlow
    rw [hr i hiIdx, hr mid hmid] at hupp
    by_cases hloq : lo < nums.size - p <;>
      by_cases hmidq : mid < nums.size - p <;>
      by_cases hiq : i < nums.size - p <;>
      simp [hloq, hmidq, hiq] at hleft hlow hupp <;> omega
  constructor
  · rintro ⟨hleft, hnrange⟩
    rw [hle lo mid hlo hmid] at hleft
    simp only [not_and_or] at hnrange
    rw [hle lo i hlo hiIdx] at hnrange
    rw [hlt i mid hiIdx hmid] at hnrange
    rw [hr lo hlo, hr mid hmid] at hleft
    rw [hr lo hlo, hr mid hmid, hr i hiIdx] at hnrange
    by_cases hloq : lo < nums.size - p <;>
      by_cases hmidq : mid < nums.size - p <;>
      by_cases hiq : i < nums.size - p <;>
      simp [hloq, hmidq, hiq] at hleft hnrange <;> omega
  constructor
  · rintro ⟨hleft, hlow, hupp⟩
    rw [hle lo mid hlo hmid] at hleft
    rw [hlt mid i hmid hiIdx] at hlow
    rw [hle i (hi - 1) hiIdx hh] at hupp
    rw [hr lo hlo, hr mid hmid] at hleft
    rw [hr mid hmid, hr i hiIdx] at hlow
    rw [hr i hiIdx, hr (hi - 1) hh] at hupp
    by_cases hloq : lo < nums.size - p <;>
      by_cases hmidq : mid < nums.size - p <;>
      by_cases hiq : i < nums.size - p <;>
      by_cases hhq : hi - 1 < nums.size - p <;>
      simp [hloq, hmidq, hiq, hhq] at hleft hlow hupp <;> omega
  · rintro ⟨hleft, hnrange⟩
    rw [hle lo mid hlo hmid] at hleft
    simp only [not_and_or] at hnrange
    rw [hlt mid i hmid hiIdx] at hnrange
    rw [hle i (hi - 1) hiIdx hh] at hnrange
    rw [hr lo hlo, hr mid hmid] at hleft
    rw [hr mid hmid, hr i hiIdx, hr (hi - 1) hh] at hnrange
    by_cases hloq : lo < nums.size - p <;>
      by_cases hmidq : mid < nums.size - p <;>
      by_cases hiq : i < nums.size - p <;>
      by_cases hhq : hi - 1 < nums.size - p <;>
      simp [hloq, hmidq, hiq, hhq] at hleft hnrange <;> omega

prove_correct search by
  velvet_vcgen [search, precondition, postcondition] with try finish
  case found_or_absent =>
    rename_i nums target
    right
    have hv := found_valid _ h_some
    have hget : _ = some _ := Array.getElem?_eq_some_getElem! _ _ hv.1
    rw [hv.2] at hget
    refine ⟨_, hv.1, hget, rfl, ?_⟩
    intro j hj htarget
    apply (List.Nodup.getElem?_inj (xs := nums.toList) hj input_shape.2.1).mp
    simpa only [Array.getElem?_toList] using htarget.trans hget.symm
  case found_or_absent =>
    rename_i nums target
    left
    refine ⟨rfl, ?_⟩
    intro hmem
    rcases Array.mem_iff_getElem.mp hmem with ⟨i, hi_i, htarget⟩
    have htarget' : nums[i]! = target := by
      simpa [getElem!_pos nums i hi_i] using htarget
    have hc := candidates h_none i hi_i htarget'
    rcases exhausted with hmeet | hfound
    · omega
    · exact absurd h_none hfound
  case candidates =>
    rename_i nums target
    intro _ i hi_i htarget
    let mid := lo + (hi - lo) / 2
    have hc := candidates active.2 i hi_i htarget
    refine ⟨hc.1, ?_⟩
    have hne : nums[mid]! ≠ nums[i]! := by
      intro heq
      exact at_mid (heq.trans htarget)
    have law := rotated_search_partition nums input_shape.1 input_shape.2.2
      lo mid hi i (by omega) (by omega) (by omega) hi_i
      (by omega) (by omega) hc.1 hc.2 hne
    apply law.1
    rw [htarget]
    exact ⟨left_sorted, target_in_left⟩
  case candidates =>
    rename_i nums target
    intro _ i hi_i htarget
    let mid := lo + (hi - lo) / 2
    have hc := candidates active.2 i hi_i htarget
    refine ⟨?_, hc.2⟩
    have hne : nums[mid]! ≠ nums[i]! := by
      intro heq
      exact at_mid (heq.trans htarget)
    have law := rotated_search_partition nums input_shape.1 input_shape.2.2
      lo mid hi i (by omega) (by omega) (by omega) hi_i
      (by omega) (by omega) hc.1 hc.2 hne
    have hm := law.2.1 ⟨left_sorted, by simpa [htarget] using target_in_left⟩
    omega
  case candidates =>
    rename_i nums target
    intro _ i hi_i htarget
    let mid := lo + (hi - lo) / 2
    have hc := candidates active.2 i hi_i htarget
    refine ⟨?_, hc.2⟩
    have hne : nums[mid]! ≠ nums[i]! := by
      intro heq
      exact at_mid (heq.trans htarget)
    have law := rotated_search_partition nums input_shape.1 input_shape.2.2
      lo mid hi i (by omega) (by omega) (by omega) hi_i
      (by omega) (by omega) hc.1 hc.2 hne
    have hm := law.2.2.1 ⟨left_sorted, by simpa [htarget] using target_in_right⟩
    omega
  case candidates =>
    rename_i nums target
    intro _ i hi_i htarget
    let mid := lo + (hi - lo) / 2
    have hc := candidates active.2 i hi_i htarget
    refine ⟨hc.1, ?_⟩
    have hne : nums[mid]! ≠ nums[i]! := by
      intro heq
      exact at_mid (heq.trans htarget)
    have law := rotated_search_partition nums input_shape.1 input_shape.2.2
      lo mid hi i (by omega) (by omega) (by omega) hi_i
      (by omega) (by omega) hc.1 hc.2 hne
    exact law.2.2.2 ⟨left_sorted, by simpa [htarget] using target_in_right⟩

end Proof

end SearchInRotatedSortedArray
