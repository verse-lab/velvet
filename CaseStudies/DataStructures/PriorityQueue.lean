module

public import Velvet
public meta import Velvet

open Lean.Order

namespace VelvetLib.DataStructure

/-!
# Array-backed priority queue

This module contains the executable representation and verified operations.
The queue stores its backing array; operation contracts state the heap invariant
required and preserved by each operation.
-/

/-! ## 1. Queue definition -/

/-- The unchecked representation of an array-backed priority queue. -/
public structure PriorityQueue (α : Type) where
  data : Array α
deriving Repr

namespace PriorityQueue

/-! ## 2. Heap invariant -/

/-- Heap edges whose parent is at least `start` are ordered.
Floyd's algorithm extends this region toward the root. -/
@[expose]
public def HeapFrom [Inhabited α] [LE α] (data : Array α) (start : Nat) : Prop :=
  ∀ child, 0 < child → child < data.size → start ≤ (child - 1) / 2 →
    data[child]! ≤ data[(child - 1) / 2]!

/-- The ordinary zero-based binary max-heap parent/child condition. -/
@[expose]
public def IsMaxHeap [Inhabited α] [LE α] (queue : PriorityQueue α) : Prop :=
  HeapFrom queue.data 0

/-- The heap invariant required and preserved by queue operations. -/
public structure Inv [Inhabited α] [LE α] (queue : PriorityQueue α) : Prop where
  heap : queue.IsMaxHeap

/-! ## 3. Definitions for method contracts -/

/-- Permutation preserves all entries, including multiplicities, without requiring equality. -/
@[simp, expose]
public def SameElements (queue : PriorityQueue α) (values : Array α) : Prop :=
  queue.data.Perm values

/-- During sift-down, only the edges below `hole` may be unordered in the active
region. Its children fit below its parent whenever the hole has moved. -/
public structure SiftState [Inhabited α] [LE α]
    (data : Array α) (start hole : Nat) : Prop where
  lower : start ≤ hole
  bounded : hole < data.size
  heap : ∀ child, 0 < child → child < data.size → start ≤ (child - 1) / 2 →
    (child - 1) / 2 ≠ hole → data[child]! ≤ data[(child - 1) / 2]!
  upper : start < hole → ∀ child, 0 < child → child < data.size →
    (child - 1) / 2 = hole → data[child]! ≤ data[(hole - 1) / 2]!

/-- During sift-up, only the edge into `hole` may be unordered. The hole's
children fit below its parent, allowing that parent to move down into the hole. -/
public structure SiftUpState [Inhabited α] [LE α]
    (data : Array α) (hole : Nat) : Prop where
  bounded : hole < data.size
  heap : ∀ child, 0 < child → child < data.size → child ≠ hole →
    data[child]! ≤ data[(child - 1) / 2]!
  lower : ∀ child, 0 < child → child < data.size → (child - 1) / 2 = hole →
    data[child]! ≤ data[(hole - 1) / 2]!

/-! ### Implementation helpers and methods -/

/-- Select the greater of the existing children of `hole`. -/
public def maxChildIndex [Inhabited α] [LE α] [DecidableLE α]
    (data : Array α) (hole : Nat) : Nat :=
  let left := 2 * hole + 1
  let right := left + 1
  if right < data.size ∧ data[left]! ≤ data[right]! then right else left

/-- Replace the root with the last entry and remove the old root. -/
public def removeRoot [Inhabited α] (data : Array α) : Array α :=
  (data.swapIfInBounds 0 (data.size - 1)).pop

/-- Repair the heap at `start`, assuming all larger parent indices are ordered.
Each iteration descends one tree level, taking `O(log n)` time at the root. -/
method siftDown {α : Type} [Inhabited α] [LE α] [DecidableLE α]
    [Std.IsLinearOrder α] (input : Array α) (start : Nat)
  returns (result : Array α) in Id
  requires bounded: start < input.size
  requires heap: HeapFrom input (start + 1)
  ensures heap: HeapFrom result start
  ensures elements: result.Perm input
do
  let mut data := input
  let mut hole := start
  while' has_left: 2 * hole + 1 < data.size
    invariant state: SiftState data start hole
    invariant elements: data.Perm input
    decreasing remaining: data.size - hole
    done_with heap_done: HeapFrom data start
  do
    let largest := maxChildIndex data hole
    if data[largest]! ≤ data[hole]! then
      break
    data := data.swapIfInBounds hole largest
    hole := largest
  return data

/-- Floyd's bottom-up heap construction in `O(n)` time.
Only internal nodes are sifted, in reverse order. The sum of their heights is
at most `n`, so the total sift-down work is linear. -/
method build {α : Type} [Inhabited α] [LE α] [DecidableLE α]
    [Std.IsLinearOrder α] (values : Array α)
  returns (queue : PriorityQueue α) in Id
  ensures wellformed: queue.Inv
  ensures elements: SameElements queue values
do
  let mut data := values
  let mut next := data.size / 2
  while' pending: 0 < next
    invariant bounded: next ≤ data.size / 2
    invariant heap: HeapFrom data next
    invariant elements: data.Perm values
    decreasing remaining: next
  do
    next := next - 1
    data ← siftDown data next
  return ⟨data⟩

/-- Inspect the root of a nonempty max heap without changing the queue.
The input is immutable and the operation runs in `Id`, so no queue state can be
modified. The postcondition also retains the input's heap invariant. -/
method peek {α : Type} [Inhabited α] [LE α] [Std.IsPreorder α]
    (queue : PriorityQueue α)
  returns (result : α) in Id
  requires nonempty: 0 < queue.data.size
  requires wellformed: queue.Inv
  ensures wellformed: queue.Inv
  ensures stored_at_root: result = queue.data[0]!
  ensures maximum: ∀ i, i < queue.data.size → queue.data[i]! ≤ result
do
  return queue.data[0]!

/-- Return the maximum entry and the remaining max heap in `O(log n)`. -/
method pop {α : Type} [Inhabited α] [LE α] [DecidableLE α]
    [Std.IsLinearOrder α]
    (queue : PriorityQueue α)
  returns (result : α × PriorityQueue α) in Id
  requires nonempty: 0 < queue.data.size
  requires wellformed: queue.Inv
  ensures stored_at_root: result.1 = queue.data[0]!
  ensures maximum: ∀ i, i < queue.data.size → queue.data[i]! ≤ result.1
  ensures elements: (result.2.data.push result.1).Perm queue.data
  ensures wellformed: result.2.Inv
do
  let value := queue.data[0]!
  if queue.data.size = 1 then
    return (value, ⟨#[]⟩)
  let data := removeRoot queue.data
  let data ← siftDown data 0
  return (value, ⟨data⟩)

/-- Insert an entry by appending it and sifting it upward in `O(log n)` time. -/
method push {α : Type} [Inhabited α] [LE α] [DecidableLE α]
    [Std.IsLinearOrder α] (queue : PriorityQueue α) (value : α)
  returns (result : PriorityQueue α) in Id
  requires wellformed: queue.Inv
  ensures elements: SameElements result (queue.data.push value)
  ensures wellformed: result.Inv
do
  let mut data := queue.data.push value
  let mut hole := queue.data.size
  while' not_root: 0 < hole
    invariant state: SiftUpState data hole
    invariant elements: data.Perm (queue.data.push value)
    decreasing remaining: hole
    done_with heap_done: IsMaxHeap ⟨data⟩
  do
    let parent := (hole - 1) / 2
    if data[hole]! ≤ data[parent]! then
      break
    data := data.swapIfInBounds hole parent
    hole := parent
  return ⟨data⟩

/-! ## 4. Proof helpers and lemmas -/

/-- `largest` is a direct child of `hole` that dominates its sibling. -/
public def IsMaxChild [Inhabited α] [LE α]
    (data : Array α) (hole largest : Nat) : Prop :=
  0 < largest ∧ largest < data.size ∧ (largest - 1) / 2 = hole ∧
    ∀ child, 0 < child → child < data.size → (child - 1) / 2 = hole →
      data[child]! ≤ data[largest]!

public theorem child_eq_left_or_right (child parent : Nat) (positive : 0 < child)
    (isChild : (child - 1) / 2 = parent) :
    child = 2 * parent + 1 ∨ child = 2 * parent + 2 := by
  omega

/-- A swap preserves the array's entries, including when an index is out of bounds. -/
public theorem perm_swapIfInBounds (data : Array α) (i j : Nat) :
    (data.swapIfInBounds i j).Perm data := by
  unfold Array.swapIfInBounds
  split
  · split
    · exact Array.swap_perm _ _
    · exact .rfl
  · exact .rfl

/-- A `getElem!` view of the standard library's in-bounds swap theorem. -/
public theorem getElem!_swapIfInBounds [Inhabited α]
    (data : Array α) (i j k : Nat) (hi : i < data.size) (hj : j < data.size)
    (hne : i ≠ j) :
    (data.swapIfInBounds i j)[k]! =
      if k = j then data[i]! else if k = i then data[j]! else data[k]! := by
  by_cases hk : k < data.size
  · rw [getElem!_pos _ k (by simpa using hk), Array.getElem_swapIfInBounds]
    grind only [getElem!_pos]
  · rw [getElem!_neg data k hk, getElem!_neg _ k (by simpa using hk)]
    simp only [ite_eq_right (by omega : k ≠ j), ite_eq_right (by omega : k ≠ i)]

public theorem maxChildIndex_spec [Inhabited α] [LE α] [DecidableLE α]
    [Std.IsLinearOrder α] (data : Array α) (hole : Nat)
    (hasLeft : 2 * hole + 1 < data.size) :
    IsMaxChild data hole (maxChildIndex data hole) := by
  simp only [maxChildIndex]
  split
  case isTrue selectedRight =>
    rcases selectedRight with ⟨rightBounded, left_le_right⟩
    refine ⟨by omega, rightBounded, by omega, ?_⟩
    intro child childPositive childBounded direct
    rcases child_eq_left_or_right child hole childPositive direct with left | right
    · subst child
      exact left_le_right
    · subst child
      exact Std.IsPreorder.le_refl _
  case isFalse selectedLeft =>
    refine ⟨by omega, hasLeft, by omega, ?_⟩
    intro child childPositive childBounded direct
    rcases child_eq_left_or_right child hole childPositive direct with left | right
    · subst child
      exact Std.IsPreorder.le_refl _
    · subst child
      have notLeftLeRight : ¬data[2 * hole + 1]! ≤ data[2 * hole + 1 + 1]! := by
        intro leftLeRight
        exact selectedLeft ⟨by omega, leftLeRight⟩
      exact Lean.Grind.Order.le_of_not_le notLeftLeRight

@[simp]
public theorem size_removeRoot [Inhabited α] (data : Array α) :
    (removeRoot data).size = data.size - 1 := by
  simp [removeRoot]

public theorem getElem!_removeRoot [Inhabited α] (data : Array α) (k : Nat)
    (nonempty : 0 < data.size) (bounded : k < (removeRoot data).size) :
    (removeRoot data)[k]! = if k = 0 then data[data.size - 1]! else data[k]! := by
  unfold removeRoot at bounded ⊢
  have lastBounded : data.size - 1 < data.size := by omega
  have beforeLast : k < data.size - 1 := by
    rw [Array.size_pop, Array.size_swapIfInBounds] at bounded
    exact bounded
  have swapBounded : k < (data.swapIfInBounds 0 (data.size - 1)).size := by
    rw [Array.size_swapIfInBounds]
    rw [Array.size_pop, Array.size_swapIfInBounds] at bounded
    omega
  rw [getElem!_pos _ k bounded]
  rw [Array.getElem_pop]
  rw [← getElem!_pos (data.swapIfInBounds 0 (data.size - 1)) k swapBounded]
  rw [getElem!_swapIfInBounds data 0 (data.size - 1) k (by omega) lastBounded
    (by omega)]
  simp only [ite_eq_right (by omega : k ≠ data.size - 1)]

/-- The root of every nonempty max heap dominates all entries. -/
public theorem root_is_maximum [Inhabited α] [LE α] [Std.IsPreorder α]
    (queue : PriorityQueue α) (heap : queue.IsMaxHeap)
    (i : Nat) (bounded : i < queue.data.size) :
    queue.data[i]! ≤ queue.data[0]! := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases root : i = 0
    · subst i
      exact Std.IsPreorder.le_refl _
    · have positive : 0 < i := by omega
      have parent_lt : (i - 1) / 2 < i := by omega
      have parent_bounded : (i - 1) / 2 < queue.data.size := by omega
      exact Std.IsPreorder.le_trans _ _ _
        (heap i positive bounded (Nat.zero_le _))
        (ih ((i - 1) / 2) parent_lt parent_bounded)

public theorem Inv.root_is_maximum [Inhabited α] [LE α] [Std.IsPreorder α]
    {queue : PriorityQueue α} (wf : queue.Inv) (i : Nat) (bounded : i < queue.data.size) :
    queue.data[i]! ≤ queue.data[0]! :=
  PriorityQueue.root_is_maximum queue wf.heap i bounded

/-- Leaves already satisfy the heap condition. -/
public theorem heapFrom_leaves [Inhabited α] [LE α] (data : Array α) :
    HeapFrom data (data.size / 2) := by
  intro child positive bounded parent
  omega

public theorem siftState_initial [Inhabited α] [LE α]
    {data : Array α} {start : Nat} (bounded : start < data.size)
    (heap : HeapFrom data (start + 1)) : SiftState data start start := by
  refine ⟨Nat.le_refl _, bounded, ?_, ?_⟩
  · intro child positive bounded lower different
    exact heap child positive bounded (by omega)
  · intro impossible
    omega

public theorem SiftState.heapFrom_of_dominates [Inhabited α] [LE α]
    {data : Array α} {start hole : Nat} (state : SiftState data start hole)
    (dominates : ∀ child, 0 < child → child < data.size → (child - 1) / 2 = hole →
      data[child]! ≤ data[hole]!) : HeapFrom data start := by
  intro child positive bounded lower
  by_cases direct : (child - 1) / 2 = hole
  · rw [direct]
    exact dominates child positive bounded direct
  · exact state.heap child positive bounded lower direct

public theorem SiftState.heapFrom_of_no_left [Inhabited α] [LE α]
    {data : Array α} {start hole : Nat} (state : SiftState data start hole)
    (noLeft : ¬2 * hole + 1 < data.size) : HeapFrom data start := by
  apply state.heapFrom_of_dominates
  intro child positive bounded direct
  omega

public theorem SiftState.heapFrom_of_maxChild [Inhabited α] [LE α]
    [Std.IsPreorder α] {data : Array α} {start hole largest : Nat}
    (state : SiftState data start hole) (maxChild : IsMaxChild data hole largest)
    (dominates : data[largest]! ≤ data[hole]!) : HeapFrom data start := by
  apply state.heapFrom_of_dominates
  intro child positive bounded direct
  exact Std.IsPreorder.le_trans _ _ _
    (maxChild.2.2.2 child positive bounded direct) dominates

public theorem SiftState.swap [Inhabited α] [LE α] [Std.IsLinearOrder α]
    {data : Array α} {start hole largest : Nat}
    (state : SiftState data start hole) (maxChild : IsMaxChild data hole largest)
    (moveDown : ¬data[largest]! ≤ data[hole]!) :
    SiftState (data.swapIfInBounds hole largest) start largest := by
  have holeBounded := state.bounded
  have largestPositive := maxChild.1
  have largestBounded := maxChild.2.1
  have direct := maxChild.2.2.1
  have lower := state.lower
  have hole_lt_largest : hole < largest := by omega
  have hole_le_largest : data[hole]! ≤ data[largest]! := Lean.Grind.Order.le_of_not_le moveDown
  have swapped (index : Nat) :
      (data.swapIfInBounds hole largest)[index]! =
        if index = largest then data[hole]!
        else if index = hole then data[largest]!
        else data[index]! :=
    getElem!_swapIfInBounds data hole largest index holeBounded largestBounded
      (by omega)
  refine ⟨by omega, by simpa using largestBounded, ?_, ?_⟩
  · intro child positive bounded parentLower parent_ne
    rw [Array.size_swapIfInBounds] at bounded
    rw [swapped child, swapped ((child - 1) / 2)]
    grind only [IsMaxChild, upper, heap]
  · intro moved child positive bounded child_direct
    rw [Array.size_swapIfInBounds] at bounded
    rw [swapped child, swapped ((largest - 1) / 2)]
    grind only [heap]

/-- Removing the root leaves every edge with a non-root parent ordered. -/
public theorem removeRoot_heapFrom [Inhabited α] [LE α]
    (queue : PriorityQueue α) (nonempty : 0 < queue.data.size) (heap : queue.IsMaxHeap) :
    HeapFrom (removeRoot queue.data) 1 := by
  intro child positive bounded parentLower
  rw [getElem!_removeRoot queue.data child nonempty bounded,
    getElem!_removeRoot queue.data ((child - 1) / 2) nonempty (by
      rw [size_removeRoot] at bounded ⊢
      omega)]
  simp only [ite_eq_right (by omega : child ≠ 0),
    ite_eq_right (by omega : (child - 1) / 2 ≠ 0)]
  exact heap child positive (by rw [size_removeRoot] at bounded; omega) (Nat.zero_le _)

/-- Adding back the removed root recovers exactly the input entries. -/
public theorem perm_removeRoot [Inhabited α] (data : Array α)
    (nonempty : 0 < data.size) :
    ((removeRoot data).push data[0]!).Perm data := by
  have last : (data.swapIfInBounds 0 (data.size - 1)).back! = data[0]! := by
    unfold Array.back!
    rw [Array.size_swapIfInBounds,
      getElem!_pos _ (data.size - 1) (by simp; omega),
      Array.getElem_swapIfInBounds_right (by omega),
      ← getElem!_pos data 0 nonempty]
  have restored : (removeRoot data).push data[0]! =
      data.swapIfInBounds 0 (data.size - 1) := by
    simpa only [removeRoot, last] using
      (Array.eq_push_pop_back!_of_size_ne_zero
        (xs := data.swapIfInBounds 0 (data.size - 1))
        (by simp only [Array.size_swapIfInBounds]; omega)).symm
  rw [restored]
  exact perm_swapIfInBounds data 0 (data.size - 1)

public theorem siftUpState_initial [Inhabited α] [LE α]
    (queue : PriorityQueue α) (value : α) (heap : queue.IsMaxHeap) :
    SiftUpState (queue.data.push value) queue.data.size := by
  have pushed (i : Nat) (bounded : i < queue.data.size) :
      (queue.data.push value)[i]! = queue.data[i]! := by
    rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt bounded,
      ← getElem!_pos queue.data i bounded]
  refine ⟨by simp, ?_, ?_⟩
  · intro child positive bounded different
    have oldBounded : child < queue.data.size := by simp at bounded; omega
    rw [pushed child oldBounded, pushed ((child - 1) / 2) (by omega)]
    exact heap child positive oldBounded (Nat.zero_le _)
  · intro child positive bounded direct
    simp at bounded
    omega

public theorem SiftUpState.isMaxHeap_of_dominates [Inhabited α] [LE α]
    {data : Array α} {hole : Nat} (state : SiftUpState data hole)
    (dominates : data[hole]! ≤ data[(hole - 1) / 2]!) : IsMaxHeap ⟨data⟩ := by
  intro child positive bounded _
  by_cases atHole : child = hole
  · simpa only [atHole] using dominates
  · exact state.heap child positive bounded atHole

public theorem SiftUpState.isMaxHeap_of_root [Inhabited α] [LE α]
    {data : Array α} {hole : Nat} (state : SiftUpState data hole)
    (root : ¬0 < hole) : IsMaxHeap ⟨data⟩ := by
  intro child positive bounded _
  exact state.heap child positive bounded (by omega)

public theorem SiftUpState.swap [Inhabited α] [LE α] [Std.IsLinearOrder α]
    {data : Array α} {hole : Nat} (state : SiftUpState data hole)
    (positive : 0 < hole) (moveUp : ¬data[hole]! ≤ data[(hole - 1) / 2]!) :
    SiftUpState (data.swapIfInBounds hole ((hole - 1) / 2)) ((hole - 1) / 2) := by
  have holeBounded := state.bounded
  have parentBounded : (hole - 1) / 2 < data.size := by omega
  have parent_lt_hole : (hole - 1) / 2 < hole := by omega
  have parent_le_hole : data[(hole - 1) / 2]! ≤ data[hole]! :=
    Lean.Grind.Order.le_of_not_le moveUp
  have swapped (index : Nat) :
      (data.swapIfInBounds hole ((hole - 1) / 2))[index]! =
        if index = (hole - 1) / 2 then data[hole]!
        else if index = hole then data[(hole - 1) / 2]!
        else data[index]! :=
    getElem!_swapIfInBounds data hole ((hole - 1) / 2) index
      holeBounded parentBounded (by omega)
  refine ⟨by simpa using parentBounded, ?_, ?_⟩
  · intro child childPositive bounded different
    rw [Array.size_swapIfInBounds] at bounded
    rw [swapped child, swapped ((child - 1) / 2)]
    have edge := state.heap child childPositive bounded
    have below := state.lower child childPositive bounded
    grind only
  · intro child childPositive bounded direct
    rw [Array.size_swapIfInBounds] at bounded
    rw [swapped child, swapped (((hole - 1) / 2 - 1) / 2)]
    have edge := state.heap child childPositive bounded
    have parentEdge := state.heap ((hole - 1) / 2)
    grind only

/-! ## 5. Method correctness proofs -/

prove_correct siftDown by
  velvet_vcgen [siftDown] <;> try grind only
  · grind only [siftState_initial]
  · exact .rfl
  · grind only [!maxChildIndex_spec, SiftState.heapFrom_of_maxChild]
  · grind only [= getElem!_pos, !maxChildIndex_spec, !Array.size_swapIfInBounds,
      SiftState.bounded, IsMaxChild]
  · grind only [!maxChildIndex_spec, SiftState.swap]
  · grind only [!perm_swapIfInBounds, Array.Perm.trans]
  · grind only [SiftState.heapFrom_of_no_left]

prove_correct build by
  velvet_vcgen [build] <;> try grind only
  · grind only [heapFrom_leaves]
  · exact .rfl
  · grind only [Inv.mk, IsMaxHeap]
  · grind only [SameElements]
  · grind only [Array.Perm.size_eq]
  · grind only [Array.Perm.trans]

prove_correct peek by
  velvet_vcgen [peek] <;>
    grind only [Inv.root_is_maximum]

prove_correct pop by
  velvet_vcgen [pop] <;> try grind only [Inv.root_is_maximum]
  · obtain ⟨value, equal⟩ := Array.size_eq_one_iff.mp if_cond
    rw [equal]
    exact .rfl
  · exact ⟨by intro child _ bounded; simp at bounded⟩
  · simp only [size_removeRoot]
    omega
  · exact removeRoot_heapFrom _ nonempty wellformed.heap
  · grind only [!perm_removeRoot, usr Array.Perm.push, Array.Perm.trans]
  · exact ⟨heap⟩

prove_correct push by
  velvet_vcgen [push] <;> try grind only
  · exact siftUpState_initial _ _ wellformed.heap
  · exact .rfl
  · grind only [SameElements]
  · exact ⟨heap_done⟩
  · grind only [SiftUpState.isMaxHeap_of_dominates]
  · grind only [SiftUpState.swap]
  · grind only [!perm_swapIfInBounds, Array.Perm.trans]
  · grind only [SiftUpState.isMaxHeap_of_root]

end PriorityQueue
end VelvetLib.DataStructure
