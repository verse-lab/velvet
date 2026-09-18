module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Tauto

/-!
## Program description

Merge two nondecreasing integer arrays into one nondecreasing array preserving
all multiplicities. For sizes `m` and `n`, the program is expected to run in
O(m+n) time and use O(m+n) space for the returned array.
-/

namespace MergeSortedArray

section Specs

public def sortedNondecreasing (a : Array Int) : Prop :=
  ∀ i, i + 1 < a.size → a[i]! ≤ a[i + 1]!
public def countInArray (a : Array Int) (v : Int) : Nat :=
  a.toList.count v
public def precondition (a b : Array Int) : Prop :=
  sortedNondecreasing a ∧ sortedNondecreasing b

public def postcondition (a b result : Array Int) : Prop :=
  result.size = a.size + b.size ∧
  sortedNondecreasing result ∧
  ∀ v, countInArray result v = countInArray a v + countInArray b v

end Specs

section Implementation

public def mergeGo (a b : Array Int) (i j : Nat) (out : Array Int) : Array Int :=
  if i < a.size then
    if j < b.size then
      if a[i]! ≤ b[j]! then mergeGo a b (i + 1) j (out.push a[i]!)
      else mergeGo a b i (j + 1) (out.push b[j]!)
    else mergeGo a b (i + 1) j (out.push a[i]!)
  else if j < b.size then mergeGo a b i (j + 1) (out.push b[j]!)
  else out
termination_by (a.size - i) + (b.size - j)

public def merge (a b : Array Int) : Array Int :=
  mergeGo a b 0 0 #[]

method mergeSorted (a : Array Int) (b : Array Int)
  returns (result : Array Int)
  requires sorted_inputs: precondition a b
  ensures merged: postcondition a b result
do
  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut result : Array Int := #[]
  while remaining_input: i < a.size ∨ j < b.size
    invariant continuation: mergeGo a b i j result = merge a b
    decreasing remaining: (a.size - i) + (b.size - j)
  do
    if left_available: i < a.size then
      if right_available: j < b.size then
        if take_left: a[i]! ≤ b[j]! then
          result := result.push a[i]!
          i := i + 1
        else
          result := result.push b[j]!
          j := j + 1
      else
        result := result.push a[i]!
        i := i + 1
    else
      result := result.push b[j]!
      j := j + 1
  return result

end Implementation

section Proof

public def mergeList : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x ≤ y then x :: mergeList xs (y :: ys)
      else y :: mergeList (x :: xs) ys
termination_by xs ys => xs.length + ys.length

theorem mem_mergeList (v : Int) : ∀ xs ys,
    v ∈ mergeList xs ys ↔ v ∈ xs ∨ v ∈ ys := by
  intro xs ys
  fun_induction mergeList xs ys <;> simp_all <;> tauto

theorem count_mergeList (v : Int) : ∀ xs ys,
    (mergeList xs ys).count v = xs.count v + ys.count v := by
  intro xs ys
  fun_induction mergeList xs ys <;>
    simp_all [List.count_cons, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem mergeList_nil (xs : List Int) : mergeList xs [] = xs := by
  induction xs <;> simp [mergeList, *]

theorem length_mergeList : ∀ xs ys,
    (mergeList xs ys).length = xs.length + ys.length := by
  intro xs ys
  fun_induction mergeList xs ys <;> simp_all <;> omega

theorem mergeList_sorted : ∀ xs ys,
    xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) →
    (mergeList xs ys).Pairwise (· ≤ ·) := by
  intro xs ys
  fun_induction mergeList xs ys
  case case1 ys => simp_all
  case case2 x xs => simp_all
  case case3 x xs y ys hxy ih =>
    intro hxs hys
    rw [List.pairwise_cons] at hxs hys ⊢
    refine ⟨?_, ih hxs.2 (List.pairwise_cons.mpr hys)⟩
    intro z hz
    rw [mem_mergeList] at hz
    rcases hz with hz | hz
    · exact hxs.1 z hz
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hxy
      · exact hxy.trans (hys.1 z hz)
  case case4 x xs y ys hxy ih =>
    intro hxs hys
    rw [List.pairwise_cons] at hxs hys ⊢
    refine ⟨?_, ih (List.pairwise_cons.mpr hxs) hys.2⟩
    intro z hz
    rw [mem_mergeList] at hz
    rcases hz with hz | hz
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · exact (by omega : y ≤ x).trans (hxs.1 z hz)
    · exact hys.1 z hz

theorem mergeGo_toList (a b : Array Int) (i j : Nat) (out : Array Int)
    (hi : i ≤ a.size) (hj : j ≤ b.size) :
    (mergeGo a b i j out).toList =
      out.toList ++ mergeList (a.toList.drop i) (b.toList.drop j) := by
  fun_induction mergeGo a b i j out
  case case1 i j out hai hbj hle ih =>
    rw [ih (by omega) (by omega), Array.toList_push, List.append_assoc]
    have ha : a.toList.drop i = a[i]! :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa)]
      simp [getElem!_pos, hai]
    have hb : b.toList.drop j = b[j]! :: b.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa)]
      simp [getElem!_pos, hbj]
    rw [ha, hb]
    simp [mergeList, hle]
  case case2 i j out hai hbj hle ih =>
    rw [ih (by omega) (by omega), Array.toList_push, List.append_assoc]
    have ha : a.toList.drop i = a[i]! :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa)]
      simp [getElem!_pos, hai]
    have hb : b.toList.drop j = b[j]! :: b.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa)]
      simp [getElem!_pos, hbj]
    rw [ha, hb]
    simp [mergeList, hle]
  case case3 i j out hai hbj ih =>
    rw [ih (by omega) (by omega), Array.toList_push, List.append_assoc]
    have ha : a.toList.drop i = a[i]! :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa)]
      simp [getElem!_pos, hai]
    have : j = b.size := by omega
    subst j
    rw [ha]
    have hb0 : b.toList.drop b.size = [] := by simp
    rw [hb0]
    simp
  case case4 i j out hai hbj ih =>
    rw [ih (by omega) (by omega), Array.toList_push, List.append_assoc]
    have hb : b.toList.drop j = b[j]! :: b.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa)]
      simp [getElem!_pos, hbj]
    have : i = a.size := by omega
    subst i
    rw [hb]
    have ha0 : a.toList.drop a.size = [] := by simp
    rw [ha0]
    simp [mergeList]
  case case5 i j out hai hbj =>
    have hi_eq : i = a.size := by omega
    have hj_eq : j = b.size := by omega
    subst i
    subst j
    have ha0 : a.toList.drop a.size = [] := by simp
    have hb0 : b.toList.drop b.size = [] := by simp
    rw [ha0, hb0]
    simp

theorem merge_toList (a b : Array Int) :
    (merge a b).toList = mergeList a.toList b.toList := by
  simpa [merge] using mergeGo_toList a b 0 0 #[] (by omega) (by omega)

theorem sortedNondecreasing_iff_pairwise (a : Array Int) :
    sortedNondecreasing a ↔ a.toList.Pairwise (· ≤ ·) := by
  constructor
  · intro h
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have chain : ∀ d i, i + d < a.size → a[i]! ≤ a[i + d]! := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          intro i hib
          cases d with
          | zero => simpa using h i (by omega)
          | succ d =>
              exact (ih i (by omega)).trans (h (i + d + 1) (by omega))
    have hij' : i ≤ j := Nat.le_of_lt hij
    have heq : i + (j - i) = j := Nat.add_sub_of_le hij'
    have hiA : i < a.size := by simpa using hi
    have hjA : j < a.size := by simpa using hj
    have hc := chain (j - i) i (by simpa [heq] using hjA)
    rw [heq] at hc
    rw [getElem!_pos a i hiA, getElem!_pos a j hjA] at hc
    exact hc
  · intro h i hi
    rw [List.pairwise_iff_getElem] at h
    have hi0 : i < a.size := Nat.lt_trans (Nat.lt_succ_self i) hi
    rw [getElem!_pos a i hi0, getElem!_pos a (i + 1) hi]
    exact h i (i + 1) (by simpa) (by simpa) (by omega)

theorem merge_correct (a b : Array Int) (h : precondition a b) :
    postcondition a b (merge a b) := by
  rw [postcondition]
  have hsA := (sortedNondecreasing_iff_pairwise a).mp h.1
  have hsB := (sortedNondecreasing_iff_pairwise b).mp h.2
  have hm := mergeList_sorted a.toList b.toList hsA hsB
  constructor
  · change (merge a b).toList.length = a.toList.length + b.toList.length
    rw [merge_toList]
    exact length_mergeList a.toList b.toList
  constructor
  · apply (sortedNondecreasing_iff_pairwise (merge a b)).mpr
    rw [merge_toList]
    exact hm
  · intro v
    unfold countInArray
    rw [merge_toList]
    exact count_mergeList v a.toList b.toList
prove_correct mergeSorted by
  velvet_vcgen [mergeSorted, postcondition] with try finish
  case continuation => simp [merge]
  case merged =>
    rename_i a b
    have hi : ¬i < a.size := fun h => h_done_with (Or.inl h)
    have hj : ¬j < b.size := fun h => h_done_with (Or.inr h)
    rw [mergeGo.eq_def] at continuation
    simp [hi, hj] at continuation
    rw [continuation]
    exact merge_correct a b sorted_inputs
  case continuation =>
    rename_i a b
    rw [mergeGo.eq_def] at continuation
    simp only [left_available, right_available] at continuation
    rw [getElem!_pos a i left_available, getElem!_pos b j right_available] at continuation
    rw [getElem!_pos a i left_available] at take_left
    rw [getElem!_pos b j right_available] at take_left
    simp only [take_left] at continuation
    rw [getElem!_pos a i left_available] at ⊢
    exact continuation
  case continuation =>
    rename_i a b
    rw [getElem!_pos b j right_available] at take_left
    rw [mergeGo.eq_def] at continuation
    simp only [left_available, right_available] at continuation
    rw [getElem!_pos a i left_available, getElem!_pos b j right_available] at continuation
    rw [getElem!_pos a i left_available] at take_left
    simp only [take_left] at continuation
    rw [getElem!_pos b j right_available] at ⊢
    exact continuation
  case continuation =>
    rename_i a b
    rw [getElem!_pos a i left_available] at ⊢
    rw [mergeGo.eq_def] at continuation
    simp [left_available, right_available] at continuation
    exact continuation
  case continuation =>
    rename_i a b
    rw [mergeGo.eq_def] at continuation
    have hj : j < b.size := by omega
    rw [getElem!_pos b j hj] at ⊢
    simp [left_available, hj] at continuation
    exact continuation

end Proof

end MergeSortedArray
