module

public import Velvet
public meta import Velvet
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Order.Basic

/-!
## Program description

IntervalListIntersections: Intersect two sorted, pairwise-disjoint lists of closed
integer intervals. The output is the list of all non-empty intersections between
an interval from the first list and an interval from the second list, sorted and
pairwise disjoint. The program is expected to run in O(m+n) time and O(m+n) space
for the returned array.
-/

namespace IntervalListIntersections

section Specs

-- An interval is represented as a pair (start, end).
public abbrev Interval := Int × Int

-- Convert an interval to the set of integers it denotes.
public def intervalSet (iv : Interval) : Set Int :=
  Set.Icc iv.1 iv.2

-- The interval is well-formed.
public def isValidInterval (iv : Interval) : Prop :=
  iv.1 ≤ iv.2

-- Array is sorted by starts (nondecreasing).
public def sortedByStart (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.1 ≤ a[j]!.1

-- Array is pairwise disjoint in the strong closed-interval sense.
-- This implies that whenever i < j, the i-th interval ends strictly before the j-th interval begins.
public def pairwiseDisjointClosed (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.2 < a[j]!.1

-- The union of all interval sets represented by an array.
public def unionIntervalSets (a : Array Interval) : Set Int :=
  {x : Int | ∃ (i : Nat), i < a.size ∧ x ∈ intervalSet a[i]!}

-- Precondition: both lists contain only valid intervals and are sorted/disjoint.
public def precondition (firstList : Array Interval) (secondList : Array Interval) : Prop :=
  (∀ (i : Nat), i < firstList.size → isValidInterval firstList[i]!) ∧
  (∀ (i : Nat), i < secondList.size → isValidInterval secondList[i]!) ∧
  sortedByStart firstList ∧
  sortedByStart secondList ∧
  pairwiseDisjointClosed firstList ∧
  pairwiseDisjointClosed secondList

-- Postcondition: output is a valid sorted/disjoint interval list whose union equals the set intersection
-- of the unions of input lists.
public def postcondition (firstList : Array Interval) (secondList : Array Interval)
  (result : Array Interval) : Prop :=
  (∀ (k : Nat), k < result.size → isValidInterval result[k]!) ∧
  sortedByStart result ∧
  pairwiseDisjointClosed result ∧
  unionIntervalSets result = (unionIntervalSets firstList ∩ unionIntervalSets secondList)

end Specs

section Implementation

public def intersectGo (firstList : Array Interval) (secondList : Array Interval)
    (i j : Nat) (acc : Array Interval) : Array Interval :=
  if i < firstList.size then
    if j < secondList.size then
      if max firstList[i]!.1 secondList[j]!.1 ≤ min firstList[i]!.2 secondList[j]!.2 then
        if firstList[i]!.2 ≤ secondList[j]!.2 then
          intersectGo firstList secondList (i + 1) j
            (acc.push (max firstList[i]!.1 secondList[j]!.1, min firstList[i]!.2 secondList[j]!.2))
        else
          intersectGo firstList secondList i (j + 1)
            (acc.push (max firstList[i]!.1 secondList[j]!.1, min firstList[i]!.2 secondList[j]!.2))
      else
        if firstList[i]!.2 ≤ secondList[j]!.2 then
          intersectGo firstList secondList (i + 1) j acc
        else
          intersectGo firstList secondList i (j + 1) acc
    else
      acc
  else
    acc
termination_by (firstList.size - i) + (secondList.size - j)

public def intervalIntersection (firstList : Array Interval) (secondList : Array Interval) : Array Interval :=
  intersectGo firstList secondList 0 0 #[]

method intervalListIntersections (firstList : Array Interval) (secondList : Array Interval)
  returns (result : Array Interval)
  requires valid_inputs: precondition firstList secondList
  ensures intersected: postcondition firstList secondList result
do
  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut result : Array Interval := #[]
  while loop_active: i < firstList.size ∧ j < secondList.size
    invariant continuation:
      intersectGo firstList secondList i j result = intervalIntersection firstList secondList
    decreasing remaining: (firstList.size - i) + (secondList.size - j)
  do
    if push_interval: max firstList[i]!.1 secondList[j]!.1 ≤ min firstList[i]!.2 secondList[j]!.2 then
      if advance_first: firstList[i]!.2 ≤ secondList[j]!.2 then
        result := result.push (max firstList[i]!.1 secondList[j]!.1, min firstList[i]!.2 secondList[j]!.2)
        i := i + 1
      else
        result := result.push (max firstList[i]!.1 secondList[j]!.1, min firstList[i]!.2 secondList[j]!.2)
        j := j + 1
    else
      if advance_first: firstList[i]!.2 ≤ secondList[j]!.2 then
        i := i + 1
      else
        j := j + 1
  return result

end Implementation

section Proof

theorem getElem!_push_lt' [Inhabited α] (a : Array α) (v : α) (j : Nat)
    (hj : j < a.size) : (a.push v)[j]! = a[j]! := by
  have hjp : j < (a.push v).size := by simp; omega
  calc
    (a.push v)[j]! = (a.push v)[j] := getElem!_pos (a.push v) j hjp
    _ = a[j] := Array.getElem_push_lt hj
    _ = a[j]! := (getElem!_pos a j hj).symm

theorem getElem!_push_eq' [Inhabited α] (a : Array α) (v : α) :
    (a.push v)[a.size]! = v := by
  simp [getElem!_pos]

theorem unionIntervalSets_push (acc : Array Interval) (iv : Interval) :
    unionIntervalSets (acc.push iv) = unionIntervalSets acc ∪ intervalSet iv := by
  unfold unionIntervalSets
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hia : i < acc.size
    · rw [getElem!_push_lt' acc iv i hia] at hx
      exact Or.inl ⟨i, hia, hx⟩
    · have hieq : i = acc.size := by simp at hi; omega
      subst i
      rw [getElem!_push_eq'] at hx
      exact Or.inr hx
  · rintro (⟨i, hi, hx⟩ | hx)
    · refine ⟨i, by simp; omega, ?_⟩
      rw [getElem!_push_lt' acc iv i hi]
      exact hx
    · refine ⟨acc.size, by simp, ?_⟩
      rw [getElem!_push_eq']
      exact hx

theorem pairwiseDisjointClosed_push (acc : Array Interval) (iv : Interval)
    (h_pd : pairwiseDisjointClosed acc)
    (h_valid : ∀ k, k < acc.size → isValidInterval acc[k]!)
    (h_bound : acc.size > 0 → acc[acc.size - 1]!.2 < iv.1) :
    pairwiseDisjointClosed (acc.push iv) := by
  intro i j hij hj
  simp only [Array.size_push] at hj
  by_cases hja : j < acc.size
  · rw [getElem!_push_lt' acc iv i (by omega), getElem!_push_lt' acc iv j hja]
    exact h_pd i j hij hja
  · have hjeq : j = acc.size := by omega
    subst j
    rw [getElem!_push_lt' acc iv i (by omega), getElem!_push_eq']
    by_cases h_last : i = acc.size - 1
    · subst i
      exact h_bound (by omega)
    · have hi_lt : i < acc.size - 1 := by omega
      have h1 := h_pd i (acc.size - 1) hi_lt (by omega)
      have h2 := h_valid (acc.size - 1) (by omega)
      have h3 := h_bound (by omega)
      unfold isValidInterval at h2
      exact h1.trans_le (h2.trans (le_of_lt h3))

theorem pd_implies_sorted (a : Array Interval)
    (h_valid : ∀ k, k < a.size → isValidInterval a[k]!)
    (h_pd : pairwiseDisjointClosed a) :
    sortedByStart a := by
  intro i j hij hj
  have hi : i < a.size := by omega
  have h1 : a[i]!.1 ≤ a[i]!.2 := h_valid i hi
  have h2 : a[i]!.2 < a[j]!.1 := h_pd i j hij hj
  exact h1.trans (le_of_lt h2)

theorem go_structural (fl sl : Array Interval) (hpre : precondition fl sl)
    (i j : Nat) (acc : Array Interval)
    (h_valid : ∀ k, k < acc.size → isValidInterval acc[k]!)
    (h_pd : pairwiseDisjointClosed acc)
    (h_bound : acc.size > 0 → i < fl.size → j < sl.size →
      acc[acc.size - 1]!.2 < max fl[i]!.1 sl[j]!.1) :
    (∀ k, k < (intersectGo fl sl i j acc).size → isValidInterval (intersectGo fl sl i j acc)[k]!) ∧
    pairwiseDisjointClosed (intersectGo fl sl i j acc) := by
  induction h_measure : (fl.size - i) + (sl.size - j) using Nat.strong_induction_on
    generalizing i j acc with
  | h m ih =>
    rw [intersectGo.eq_def]
    split_ifs with hi hj hse hadv
    · have h_acc_valid : ∀ k, k < (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)).size →
          isValidInterval (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2))[k]! := by
        intro k hk
        simp only [Array.size_push] at hk
        by_cases hka : k < acc.size
        · rw [getElem!_push_lt' _ _ k hka]
          exact h_valid k hka
        · have hkeq : k = acc.size := by omega
          subst k
          rw [getElem!_push_eq']
          exact hse
      have h_acc_pd : pairwiseDisjointClosed (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)) := by
        apply pairwiseDisjointClosed_push acc (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) h_pd h_valid
        intro hpos
        exact h_bound hpos hi hj
      have h_step : (fl.size - (i + 1)) + (sl.size - j) < m := by omega
      apply ih ((fl.size - (i + 1)) + (sl.size - j)) h_step (i + 1) j _ h_acc_valid h_acc_pd _ rfl
      intro _ hi1 hj1
      rw [Array.size_push]
      have : acc.size + 1 - 1 = acc.size := by omega
      rw [this, getElem!_push_eq']
      have h1 : min fl[i]!.2 sl[j]!.2 ≤ fl[i]!.2 := min_le_left fl[i]!.2 sl[j]!.2
      have h2 : fl[i]!.2 < fl[i + 1]!.1 := hpre.2.2.2.2.1 i (i + 1) (by omega) hi1
      have h3 : fl[i + 1]!.1 ≤ max fl[i + 1]!.1 sl[j]!.1 := le_max_left _ _
      exact (lt_of_le_of_lt h1 h2).trans_le h3
    · have h_acc_valid : ∀ k, k < (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)).size →
          isValidInterval (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2))[k]! := by
        intro k hk
        simp only [Array.size_push] at hk
        by_cases hka : k < acc.size
        · rw [getElem!_push_lt' _ _ k hka]
          exact h_valid k hka
        · have hkeq : k = acc.size := by omega
          subst k
          rw [getElem!_push_eq']
          exact hse
      have h_acc_pd : pairwiseDisjointClosed (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)) := by
        apply pairwiseDisjointClosed_push acc (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) h_pd h_valid
        intro hpos
        exact h_bound hpos hi hj
      have h_step : (fl.size - i) + (sl.size - (j + 1)) < m := by omega
      apply ih ((fl.size - i) + (sl.size - (j + 1))) h_step i (j + 1) _ h_acc_valid h_acc_pd _ rfl
      intro _ hi1 hj1
      rw [Array.size_push]
      have : acc.size + 1 - 1 = acc.size := by omega
      rw [this, getElem!_push_eq']
      have h1 : min fl[i]!.2 sl[j]!.2 ≤ sl[j]!.2 := min_le_right fl[i]!.2 sl[j]!.2
      have h2 : sl[j]!.2 < sl[j + 1]!.1 := hpre.2.2.2.2.2 j (j + 1) (by omega) hj1
      have h3 : sl[j + 1]!.1 ≤ max fl[i]!.1 sl[j + 1]!.1 := le_max_right _ _
      exact (lt_of_le_of_lt h1 h2).trans_le h3
    · have h_step : (fl.size - (i + 1)) + (sl.size - j) < m := by omega
      apply ih ((fl.size - (i + 1)) + (sl.size - j)) h_step (i + 1) j acc h_valid h_pd _ rfl
      intro hpos hi1 hj1
      have hb := h_bound hpos hi hj
      have hle : fl[i]!.1 ≤ fl[i + 1]!.1 := hpre.2.2.1 i (i + 1) (by omega) hi1
      omega
    · have h_step : (fl.size - i) + (sl.size - (j + 1)) < m := by omega
      apply ih ((fl.size - i) + (sl.size - (j + 1))) h_step i (j + 1) acc h_valid h_pd _ rfl
      intro hpos hi1 hj1
      have hb := h_bound hpos hi hj
      have hle : sl[j]!.1 ≤ sl[j + 1]!.1 := hpre.2.2.2.1 j (j + 1) (by omega) hj1
      omega
    · exact ⟨h_valid, h_pd⟩
    · exact ⟨h_valid, h_pd⟩

public def futureIntersections (fl sl : Array Interval) (i j : Nat) : Set Int :=
  {x : Int | ∃ i' j', i ≤ i' ∧ j ≤ j' ∧ i' < fl.size ∧ j' < sl.size ∧
    x ∈ intervalSet fl[i']! ∧ x ∈ intervalSet sl[j']!}

theorem futureIntersections_step_first (fl sl : Array Interval) (hpre : precondition fl sl)
    (i j : Nat) (hi : i < fl.size) (hj : j < sl.size) (hadv : fl[i]!.2 ≤ sl[j]!.2) :
    futureIntersections fl sl i j =
      intervalSet (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) ∪
      futureIntersections fl sl (i + 1) j := by
  ext x
  simp only [futureIntersections, Set.mem_ofPred_eq, Set.mem_union, intervalSet, Set.mem_Icc]
  constructor
  · rintro ⟨i', j', hi', hj', hi's, hj's, hx1, hx2⟩
    rcases Nat.eq_or_lt_of_le hi' with rfl | hi_lt
    · rcases Nat.eq_or_lt_of_le hj' with rfl | hj_lt
      · exact Or.inl ⟨max_le_iff.mpr ⟨hx1.1, hx2.1⟩, le_min_iff.mpr ⟨hx1.2, hx2.2⟩⟩
      · have hdisj := hpre.2.2.2.2.2 j j' hj_lt hj's
        omega
    · exact Or.inr ⟨i', j', hi_lt, hj', hi's, hj's, hx1, hx2⟩
  · rintro (⟨hmax, hmin⟩ | ⟨i', j', hi', hj', hi's, hj's, hx1, hx2⟩)
    · rw [max_le_iff] at hmax
      rw [le_min_iff] at hmin
      exact ⟨i, j, le_rfl, le_rfl, hi, hj, ⟨hmax.1, hmin.1⟩, ⟨hmax.2, hmin.2⟩⟩
    · exact ⟨i', j', Nat.le_of_succ_le hi', hj', hi's, hj's, hx1, hx2⟩

theorem futureIntersections_step_second (fl sl : Array Interval) (hpre : precondition fl sl)
    (i j : Nat) (hi : i < fl.size) (hj : j < sl.size) (hadv : ¬ fl[i]!.2 ≤ sl[j]!.2) :
    futureIntersections fl sl i j =
      intervalSet (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) ∪
      futureIntersections fl sl i (j + 1) := by
  ext x
  simp only [futureIntersections, Set.mem_ofPred_eq, Set.mem_union, intervalSet, Set.mem_Icc]
  constructor
  · rintro ⟨i', j', hi', hj', hi's, hj's, hx1, hx2⟩
    rcases Nat.eq_or_lt_of_le hj' with rfl | hj_lt
    · rcases Nat.eq_or_lt_of_le hi' with rfl | hi_lt
      · exact Or.inl ⟨max_le_iff.mpr ⟨hx1.1, hx2.1⟩, le_min_iff.mpr ⟨hx1.2, hx2.2⟩⟩
      · have hdisj := hpre.2.2.2.2.1 i i' hi_lt hi's
        omega
    · exact Or.inr ⟨i', j', hi', hj_lt, hi's, hj's, hx1, hx2⟩
  · rintro (⟨hmax, hmin⟩ | ⟨i', j', hi', hj', hi's, hj's, hx1, hx2⟩)
    · rw [max_le_iff] at hmax
      rw [le_min_iff] at hmin
      exact ⟨i, j, le_rfl, le_rfl, hi, hj, ⟨hmax.1, hmin.1⟩, ⟨hmax.2, hmin.2⟩⟩
    · exact ⟨i', j', hi', Nat.le_of_succ_le hj', hi's, hj's, hx1, hx2⟩

theorem go_union_eq (fl sl : Array Interval) (hpre : precondition fl sl)
    (i j : Nat) (acc : Array Interval) :
    unionIntervalSets (intersectGo fl sl i j acc) =
    unionIntervalSets acc ∪ futureIntersections fl sl i j := by
  induction h_measure : (fl.size - i) + (sl.size - j) using Nat.strong_induction_on
    generalizing i j acc with
  | h m ih =>
    rw [intersectGo.eq_def]
    split_ifs with hi hj hse hadv hadv2
    · rw [futureIntersections_step_first fl sl hpre i j hi hj hadv]
      have h_step : (fl.size - (i + 1)) + (sl.size - j) < m := by omega
      rw [ih ((fl.size - (i + 1)) + (sl.size - j)) h_step (i + 1) j _ rfl]
      rw [unionIntervalSets_push, Set.union_assoc]
    · rw [futureIntersections_step_second fl sl hpre i j hi hj hadv]
      have h_step : (fl.size - i) + (sl.size - (j + 1)) < m := by omega
      rw [ih ((fl.size - i) + (sl.size - (j + 1))) h_step i (j + 1) _ rfl]
      rw [unionIntervalSets_push, Set.union_assoc]
    · rw [futureIntersections_step_first fl sl hpre i j hi hj hadv2]
      have h_empty : intervalSet (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) = ∅ := by
        unfold intervalSet
        exact Set.Icc_eq_empty (by omega)
      rw [h_empty, Set.empty_union]
      have h_step : (fl.size - (i + 1)) + (sl.size - j) < m := by omega
      exact ih ((fl.size - (i + 1)) + (sl.size - j)) h_step (i + 1) j acc rfl
    · rw [futureIntersections_step_second fl sl hpre i j hi hj hadv2]
      have h_empty : intervalSet (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) = ∅ := by
        unfold intervalSet
        exact Set.Icc_eq_empty (by omega)
      rw [h_empty, Set.empty_union]
      have h_step : (fl.size - i) + (sl.size - (j + 1)) < m := by omega
      exact ih ((fl.size - i) + (sl.size - (j + 1))) h_step i (j + 1) acc rfl
    · have h_empty : futureIntersections fl sl i j = ∅ := by
        ext x
        simp only [futureIntersections, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, j', _, hj', _, hj's, _⟩
        omega
      rw [h_empty, Set.union_empty]
    · have h_empty : futureIntersections fl sl i j = ∅ := by
        ext x
        simp only [futureIntersections, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i', _, hi', _, hi's, _, _⟩
        omega
      rw [h_empty, Set.union_empty]

theorem intersectGo_correct (firstList secondList : Array Interval)
    (hpre : precondition firstList secondList) :
    postcondition firstList secondList (intervalIntersection firstList secondList) := by
  unfold intervalIntersection
  have h_empty_valid : ∀ k, k < (#[] : Array Interval).size → isValidInterval (#[] : Array Interval)[k]! := by
    intro k hk
    simp at hk
  have h_empty_pd : pairwiseDisjointClosed (#[] : Array Interval) := by
    intro i j hij hj
    simp at hj
  have h_empty_bound : (#[] : Array Interval).size > 0 → 0 < firstList.size → 0 < secondList.size →
      (#[] : Array Interval)[(#[] : Array Interval).size - 1]!.2 < max firstList[0]!.1 secondList[0]!.1 := by
    intro h
    simp at h
  have h_struct := go_structural firstList secondList hpre 0 0 #[] h_empty_valid h_empty_pd h_empty_bound
  have h_union := go_union_eq firstList secondList hpre 0 0 #[]
  refine ⟨h_struct.1, pd_implies_sorted _ h_struct.1 h_struct.2, h_struct.2, ?_⟩
  rw [h_union]
  have h_empty_union : unionIntervalSets (#[] : Array Interval) = ∅ := by
    ext x
    simp [unionIntervalSets]
  rw [h_empty_union, Set.empty_union]
  ext x
  simp only [futureIntersections, unionIntervalSets, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨i', j', _, _, hi's, hj's, hx1, hx2⟩
    exact ⟨⟨i', hi's, hx1⟩, ⟨j', hj's, hx2⟩⟩
  · rintro ⟨⟨i', hi's, hx1⟩, ⟨j', hj's, hx2⟩⟩
    exact ⟨i', j', Nat.zero_le _, Nat.zero_le _, hi's, hj's, hx1, hx2⟩

theorem intersectGo_step_push_first (fl sl : Array Interval) (i j : Nat) (acc : Array Interval)
    (hi : i < fl.size) (hj : j < sl.size)
    (hse : max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2)
    (hadv : fl[i]!.2 ≤ sl[j]!.2) :
    intersectGo fl sl i j acc =
      intersectGo fl sl (i + 1) j
        (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)) := by
  rw [intersectGo.eq_def]
  simp only [hi, hj, hse, hadv, ↓reduceIte]

theorem intersectGo_step_push_second (fl sl : Array Interval) (i j : Nat) (acc : Array Interval)
    (hi : i < fl.size) (hj : j < sl.size)
    (hse : max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2)
    (hadv : ¬ fl[i]!.2 ≤ sl[j]!.2) :
    intersectGo fl sl i j acc =
      intersectGo fl sl i (j + 1)
        (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)) := by
  rw [intersectGo.eq_def]
  simp only [hi, hj, hse, hadv, ↓reduceIte]

theorem intersectGo_step_skip_first (fl sl : Array Interval) (i j : Nat) (acc : Array Interval)
    (hi : i < fl.size) (hj : j < sl.size)
    (hse : ¬ max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2)
    (hadv : fl[i]!.2 ≤ sl[j]!.2) :
    intersectGo fl sl i j acc = intersectGo fl sl (i + 1) j acc := by
  rw [intersectGo.eq_def]
  simp only [hi, hj, hse, hadv, ↓reduceIte]

theorem intersectGo_step_skip_second (fl sl : Array Interval) (i j : Nat) (acc : Array Interval)
    (hi : i < fl.size) (hj : j < sl.size)
    (hse : ¬ max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2)
    (hadv : ¬ fl[i]!.2 ≤ sl[j]!.2) :
    intersectGo fl sl i j acc = intersectGo fl sl i (j + 1) acc := by
  rw [intersectGo.eq_def]
  simp only [hi, hj, hse, hadv, ↓reduceIte]

prove_correct intervalListIntersections by
  velvet_vcgen [intervalListIntersections, postcondition]
  · simp [intervalIntersection]
  ·
    rename_i firstList secondList
    rw [intersectGo.eq_def] at continuation
    split_ifs at continuation with h1 h2
    · exfalso; exact h_done_with ⟨h1, h2⟩
    · exfalso; exact h_done_with ⟨h1, h2⟩
    · exfalso; exact h_done_with ⟨h1, h2⟩
    · exfalso; exact h_done_with ⟨h1, h2⟩
    · rw [continuation]; exact intersectGo_correct firstList secondList valid_inputs
    · rw [continuation]; exact intersectGo_correct firstList secondList valid_inputs
  · omega
  · rw [← continuation]
    exact (intersectGo_step_push_first _ _ _ _ _ loop_active.1 loop_active.2
      push_interval advance_first).symm
  · omega
  · rw [← continuation]
    exact (intersectGo_step_push_second _ _ _ _ _ loop_active.1 loop_active.2
      push_interval advance_first).symm
  · omega
  · rw [← continuation]
    exact (intersectGo_step_skip_first _ _ _ _ _ loop_active.1 loop_active.2
      push_interval advance_first).symm
  · omega
  · rw [← continuation]
    exact (intersectGo_step_skip_second _ _ _ _ _ loop_active.1 loop_active.2
      push_interval advance_first).symm
  · exact continuation
  · omega

end Proof

end IntervalListIntersections
