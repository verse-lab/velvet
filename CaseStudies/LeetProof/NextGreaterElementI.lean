module

public import Velvet
public meta import Velvet

set_option maxHeartbeats 10000000

/-!
## Program description

For each element of `nums1`, find its next greater element in `nums2`.

The next greater element of some element `x` in an array is the first greater
element that is to the right of `x` in the same array.

You are given two distinct 0-indexed integer arrays `nums1` and `nums2`, where
`nums1` is a subset of `nums2`.

For each `0 ≤ i < nums1.length`, find the index `j` such that `nums1[i] == nums2[j]`
and determine the next greater element of `nums2[j]` in `nums2`. If there is no
next greater element, then the answer for this query is `-1`.

Return an array `ans` of length `nums1.length` such that `ans[i]` is the next
greater element as described above.

The implementation uses the original monotonic-stack strategy. Because the
verified port represents the value-to-answer map as an association list and
therefore performs linear lookup for each query, it runs in O(n + m * n) time
and O(n) extra space, excluding the returned array.
-/

namespace NextGreaterElementI

section Specs

public def DistinctArray (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i ≠ j → a[i]! ≠ a[j]!

public def IsSubsetArray (small : Array Int) (big : Array Int) : Prop :=
  ∀ (i : Nat), i < small.size → ∃ (j : Nat), j < big.size ∧ big[j]! = small[i]!

-- x occurs in array a at index j.
public def OccursAt (a : Array Int) (x : Int) (j : Nat) : Prop :=
  j < a.size ∧ a[j]! = x

-- k is the (index of the) next greater element for position j in a.
-- This means:
-- * it is to the right (j < k)
-- * it is strictly greater
-- * no earlier index between j and k is strictly greater (k is the first such index)
public def NextGreaterIndex (a : Array Int) (j : Nat) (k : Nat) : Prop :=
  j < k ∧
  k < a.size ∧
  a[k]! > a[j]! ∧
  (∀ (t : Nat), j < t → t < k → a[t]! ≤ a[j]!)

public def HasNextGreater (a : Array Int) (j : Nat) : Prop :=
  ∃ (k : Nat), NextGreaterIndex a j k

-- v is the next-greater value for index j; v = -1 iff no next-greater exists.
public def NextGreaterValue (a : Array Int) (j : Nat) (v : Int) : Prop :=
  (v = (-1) ∧ ¬ HasNextGreater a j) ∨
  (∃ (k : Nat), NextGreaterIndex a j k ∧ v = a[k]!)

-- Preconditions

public def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  DistinctArray nums1 ∧
  DistinctArray nums2 ∧
  IsSubsetArray nums1 nums2

-- Postconditions

public def postcondition (nums1 : Array Int) (nums2 : Array Int) (ans : Array Int) : Prop :=
  ans.size = nums1.size ∧
  (∀ (i : Nat), i < nums1.size →
    ∃ (j : Nat), OccursAt nums2 nums1[i]! j ∧ NextGreaterValue nums2 j ans[i]!)

end Specs

section Implementation

public def stackMonotone (nums : Array Int) : List Nat → Prop
  | [] => True
  | x :: xs =>
    (∀ y ∈ xs, nums[x]! ≤ nums[y]!) ∧ stackMonotone nums xs

public def canPop (nums : Array Int) (i : Nat) : List Nat → Bool
  | [] => false
  | x :: _ => decide (nums[x]! < nums[i]!)

method nextGreaterElementI (nums1 : Array Int) (nums2 : Array Int)
  returns (ans : Array Int)
  requires valid: precondition nums1 nums2
  ensures correct: postcondition nums1 nums2 ans
do
  let mut stack : List Nat := []
  let mut mp : List (Int × Int) := []
  let mut i : Nat := 0
  while scanning: i < nums2.size
    invariant i_bound: i ≤ nums2.size
    invariant stack_lt_i: ∀ p ∈ stack, p < i
    invariant stack_monotone: stackMonotone nums2 stack
    invariant stack_no_greater: ∀ p ∈ stack, ∀ t,
      p < t → t < i → nums2[t]! ≤ nums2[p]!
    invariant scanned_partition: ∀ j, j < i →
      (∃ kv ∈ mp, kv.1 = nums2[j]!) ∨ j ∈ stack
    invariant mp_sound: ∀ kv ∈ mp, ∃ j,
      OccursAt nums2 kv.1 j ∧ NextGreaterValue nums2 j kv.2
    decreasing scan_remaining: nums2.size - i
    done_with scanned: i = nums2.size
  do
    let cur := nums2[i]!
    while popping: canPop nums2 i stack
      invariant pop_stack_lt_i: ∀ p ∈ stack, p < i
      invariant pop_stack_monotone: stackMonotone nums2 stack
      invariant pop_stack_no_greater: ∀ p ∈ stack, ∀ t,
        p < t → t < i → nums2[t]! ≤ nums2[p]!
      invariant pop_partition: ∀ j, j < i →
        (∃ kv ∈ mp, kv.1 = nums2[j]!) ∨ j ∈ stack
      invariant pop_mp_sound: ∀ kv ∈ mp, ∃ j,
        OccursAt nums2 kv.1 j ∧ NextGreaterValue nums2 j kv.2
      decreasing pop_remaining: stack.length
      done_with popped:
        stack = [] ∨ ∃ top rest, stack = top :: rest ∧ cur ≤ nums2[top]!
    do
      match stack with
      | [] => pure ()
      | top :: rest =>
        mp := (nums2[top]!, cur) :: mp
        stack := rest
    stack := i :: stack
    i := i + 1

  while finishing: stack ≠ []
    invariant final_stack_bounds: ∀ p ∈ stack, p < nums2.size
    invariant final_no_greater: ∀ p ∈ stack, ∀ t,
      p < t → t < nums2.size → nums2[t]! ≤ nums2[p]!
    invariant final_partition: ∀ j, j < nums2.size →
      (∃ kv ∈ mp, kv.1 = nums2[j]!) ∨ j ∈ stack
    invariant final_mp_sound: ∀ kv ∈ mp, ∃ j,
      OccursAt nums2 kv.1 j ∧ NextGreaterValue nums2 j kv.2
    decreasing finish_remaining: stack.length
    done_with finished: stack = []
  do
    match stack with
    | [] => pure ()
    | top :: rest =>
      mp := (nums2[top]!, -1) :: mp
      stack := rest

  let mut ans : Array Int := #[]
  let mut a : Nat := 0
  while answering: a < nums1.size
    invariant a_bound: a ≤ nums1.size
    invariant ans_size: ans.size = a
    invariant ans_correct: ∀ u, u < a → ∃ j,
      OccursAt nums2 nums1[u]! j ∧ NextGreaterValue nums2 j ans[u]!
    decreasing answer_remaining: nums1.size - a
    done_with answered: a = nums1.size
  do
    let x := nums1[a]!
    let mut search := mp
    let mut found : Bool := false
    let mut value : Int := -1
    while lookup: search ≠ [] ∧ found = false
      invariant lookup_exists:
        found = true ∨ ∃ kv ∈ search, kv.1 = x
      invariant found_sound: found = true → ∃ kv ∈ mp,
        kv.1 = x ∧ value = kv.2
      invariant search_subset: ∀ kv ∈ search, kv ∈ mp
      decreasing lookup_remaining: search.length
      done_with looked_up: found = true
    do
      match search with
      | [] => pure ()
      | kv :: rest =>
        if match_value: kv.1 = x then
          value := kv.2
          found := true
        search := rest
    ans := ans.push value
    a := a + 1

  return ans

end Implementation

section Proof

theorem getElem!_push_lt (a : Array Int) (x : Int) (u : Nat) (hu : u < a.size) :
    (a.push x)[u]! = a[u]! := by
  rw [getElem!_pos (a.push x) u (by simp; omega), getElem!_pos a u hu]
  exact Array.getElem_push_lt hu

theorem getElem!_push_self (a : Array Int) (x : Int) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  exact Array.getElem_push_eq

theorem no_next_greater_value (a : Array Int) (j : Nat)
    (h : ∀ t, j < t → t < a.size → a[t]! ≤ a[j]!) :
    NextGreaterValue a j (-1) := by
  left
  refine ⟨rfl, ?_⟩
  rintro ⟨k, hjk, hk, hgt, _⟩
  have hle := h k hjk hk
  omega

theorem found_next_greater_value (a : Array Int) (j k : Nat)
    (hjk : j < k) (hk : k < a.size) (hgt : a[j]! < a[k]!)
    (hbetween : ∀ t, j < t → t < k → a[t]! ≤ a[j]!) :
    NextGreaterValue a j a[k]! := by
  right
  exact ⟨k, ⟨hjk, hk, hgt, hbetween⟩, rfl⟩

theorem stackMonotone_tail (nums : Array Int) (x : Nat) (xs : List Nat)
    (h : stackMonotone nums (x :: xs)) : stackMonotone nums xs :=
  h.2

theorem stackMonotone_head_le (nums : Array Int) (x y : Nat) (xs : List Nat)
    (h : stackMonotone nums (x :: xs)) (hy : y ∈ xs) :
    nums[x]! ≤ nums[y]! :=
  h.1 y hy

theorem stack_all_ge_current (nums : Array Int) (i : Nat) (stack : List Nat)
    (hmono : stackMonotone nums stack)
    (hstop : stack = [] ∨ ∃ top rest, stack = top :: rest ∧ nums[i]! ≤ nums[top]!) :
    ∀ y ∈ stack, nums[i]! ≤ nums[y]! := by
  intro y hy
  rcases hstop with rfl | ⟨top, rest, rfl, htop⟩
  · contradiction
  · simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact htop
    · exact Int.le_trans htop (stackMonotone_head_le nums top y rest hmono hy)

prove_correct nextGreaterElementI by
  velvet_vcgen [nextGreaterElementI, postcondition] with try finish
  case stack_monotone =>
    trivial
  case correct =>
    constructor
    · omega
    · intro u hu
      exact ans_correct u (by omega)
  case lookup_exists =>
    obtain ⟨j, hj, heq⟩ := valid.2.2 a answering
    rcases final_partition j hj with hmap | hstack
    · rcases hmap with ⟨kv, hmem, hkey⟩
      exact Or.inr ⟨kv, hmem, by simpa [heq] using hkey⟩
    · rw [finished] at hstack
      contradiction
  case final_partition =>
    rename_i arr1 arr2 initialStack initialMp
    intro q hq
    rcases final_partition q hq with hmap | hstack
    · rcases hmap with ⟨kv, hmem, hkey⟩
      exact Or.inl ⟨kv, by simp [hmem], hkey⟩
    · rw [h_cons] at hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | htail
      · exact Or.inl ⟨(arr2[q]!, -1), by simp, rfl⟩
      · exact Or.inr htail
  case final_mp_sound =>
    rename_i arr1 arr2 initialStack initialMp
    intro kv hab
    obtain ⟨a, b⟩ := kv
    simp only [List.mem_cons] at hab
    rcases hab with hab | hab
    · have heq : (a, b) = (arr2[top]!, -1) := hab
      injection heq with ha hb
      subst a
      subst b
      refine ⟨top, ⟨final_stack_bounds top (by rw [h_cons]; simp), rfl⟩, ?_⟩
      exact no_next_greater_value _ _
        (final_no_greater top (by rw [h_cons]; simp))
    · exact final_mp_sound (a, b) hab
  case stack_monotone =>
    rename_i arr1 arr2 initialStack initialMp
    change (∀ y ∈ stack, arr2[i]! ≤ arr2[y]!) ∧ stackMonotone arr2 stack
    exact ⟨stack_all_ge_current _ _ _ pop_stack_monotone popped, pop_stack_monotone⟩
  case stack_no_greater =>
    intro p hp t hpt hti
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · omega
    · by_cases ht : t < i
      · exact pop_stack_no_greater p hp t hpt ht
      · have hteq : t = i := by omega
        subst t
        exact stack_all_ge_current _ _ _ pop_stack_monotone popped p hp
  case pop_remaining =>
    rw [h_nil] at popping
    simp [canPop] at popping
  case pop_stack_monotone =>
    rw [h_cons] at pop_stack_monotone
    exact pop_stack_monotone.2
  case pop_partition =>
    rename_i arr1 arr2 initialStack initialMp
    intro q hq
    rcases pop_partition q hq with hmap | hstack
    · rcases hmap with ⟨kv, hmem, hkey⟩
      exact Or.inl ⟨kv, by simp [hmem], hkey⟩
    · rw [h_cons] at hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | htail
      · exact Or.inl ⟨(arr2[q]!, arr2[i]!), by simp, rfl⟩
      · exact Or.inr htail
  case pop_mp_sound =>
    rename_i arr1 arr2 initialStack initialMp
    intro kv hab
    obtain ⟨a, b⟩ := kv
    simp only [List.mem_cons] at hab
    rcases hab with hab | hab
    · have heq : (a, b) = (arr2[top]!, arr2[i]!) := hab
      injection heq with ha hb
      subst a
      subst b
      have hxlt : top < i := pop_stack_lt_i top (by simp [h_cons])
      have hgt : arr2[top]! < arr2[i]! := by
        simpa [canPop, h_cons] using popping
      refine ⟨top, ⟨by omega, rfl⟩, ?_⟩
      exact found_next_greater_value _ top i hxlt scanning hgt
        (pop_stack_no_greater top (by simp [h_cons]))
    · exact pop_mp_sound (a, b) hab
  case popped =>
    rename_i arr1 arr2 initialStack initialMp
    cases stack with
    | nil => exact Or.inl rfl
    | cons top rest =>
      right
      refine ⟨top, rest, rfl, ?_⟩
      have hnot : ¬arr2[top]! < arr2[i]! := by
        simpa [canPop] using popping
      omega

end Proof

end NextGreaterElementI
