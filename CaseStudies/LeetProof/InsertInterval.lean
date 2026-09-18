module

public import Velvet
public meta import Velvet
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Order.Basic

/-!
## Program description

Insert one valid closed interval into a start-sorted, strictly separated array,
merging every overlap or touching boundary. The program is expected to run in
O(n) time and O(n) extra space for the result.
-/

namespace InsertInterval

section Specs

public abbrev Interval := Int × Int

public abbrev istart (i : Interval) : Int := i.1
public abbrev iend (i : Interval) : Int := i.2

@[simp] public def wfInterval (i : Interval) : Prop := istart i ≤ iend i

public def sortedByStart (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size → istart a[i]! ≤ istart a[i + 1]!

public def noOverlapConsecutive (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size → iend a[i]! < istart a[i + 1]!

public def allWf (a : Array Interval) : Prop :=
  ∀ i, i < a.size → wfInterval a[i]!

@[simp] public def memInterval (x : Int) (i : Interval) : Prop :=
  istart i ≤ x ∧ x ≤ iend i

public def coveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ i, i < a.size ∧ memInterval x a[i]!

public def canonical (a : Array Interval) : Prop :=
  sortedByStart a ∧ noOverlapConsecutive a ∧ allWf a

public def precondition (intervals : Array Interval) (newInterval : Interval) : Prop :=
  canonical intervals ∧ wfInterval newInterval

public def postcondition
    (intervals : Array Interval) (newInterval : Interval)
    (result : Array Interval) : Prop :=
  canonical result ∧
  (∀ x, coveredBy x result ↔ coveredBy x intervals ∨ memInterval x newInterval) ∧
  (∀ i, i + 1 < result.size → iend result[i]! < istart result[i + 1]!)

-- Local specification used for the merge phase.  Keeping it here makes this
-- example independent of the sibling `MergeIntervals` example.
public def mergeLexSorted (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size →
    istart a[i]! < istart a[i + 1]! ∨
    (istart a[i]! = istart a[i + 1]! ∧ iend a[i]! ≤ iend a[i + 1]!) ∨
    (istart a[i]! = istart a[i + 1]! ∧ iend a[i]! = iend a[i + 1]!)

public def mergeAllValid (a : Array Interval) : Prop :=
  ∀ i, i < a.size → istart a[i]! ≤ iend a[i]!

public def mergeNondecreasingStarts (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size → istart a[i]! ≤ istart a[i + 1]!

public def mergeStrictlyNonOverlapping (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size → iend a[i]! < istart a[i + 1]!

public def mergeCoveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ i, i < a.size ∧ memInterval x a[i]!

public def mergePrecondition (intervals : Array Interval) : Prop :=
  mergeAllValid intervals ∧ mergeLexSorted intervals

public def mergePostcondition (intervals result : Array Interval) : Prop :=
  mergeAllValid result ∧
  mergeNondecreasingStarts result ∧
  mergeStrictlyNonOverlapping result ∧
  ∀ x, mergeCoveredBy x result ↔ mergeCoveredBy x intervals

end Specs

section Implementation

@[expose] public def intervalLexLe (a b : Interval) : Prop :=
  istart a < istart b ∨ istart a = istart b ∧ iend a ≤ iend b

public instance intervalLexLeDecidable (a b : Interval) : Decidable (intervalLexLe a b) :=
  by unfold intervalLexLe; infer_instance

public def insertSource (intervals : Array Interval) (newInterval : Interval) : Array Interval :=
  (intervals.toList.orderedInsert intervalLexLe newInterval).toArray

public def insertSourceGo (rest : List Interval) (newInterval : Interval)
    (acc : List Interval) : Array Interval :=
  match rest with
  | [] => (newInterval :: acc).reverse.toArray
  | iv :: tail =>
    if intervalLexLe newInterval iv then
      (acc.reverse ++ newInterval :: iv :: tail).toArray
    else insertSourceGo tail newInterval (iv :: acc)
termination_by rest.length

public def mergeStep (acc : Array Interval) (iv : Interval) : Array Interval :=
  if acc.size = 0 then acc.push iv
  else
    let k := acc.size - 1
    let last := acc[k]!
    if iv.1 ≤ last.2 then acc.set! k (last.1, max last.2 iv.2)
    else acc.push iv

public def mergeCoveredByPrefix (x : Int) (intervals : Array Interval) (n : Nat) : Prop :=
  ∃ j, j < n ∧ j < intervals.size ∧ memInterval x intervals[j]!

public def mergeStartsFromPrefix (intervals result : Array Interval) (n : Nat) : Prop :=
  ∀ k, k < result.size →
    ∃ j, j < n ∧ j < intervals.size ∧ istart result[k]! = istart intervals[j]!

public def MergeInvariant (intervals : Array Interval) (n : Nat)
    (result : Array Interval) : Prop :=
  n ≤ intervals.size ∧
  mergeAllValid result ∧
  mergeNondecreasingStarts result ∧
  mergeStrictlyNonOverlapping result ∧
  (∀ x, mergeCoveredBy x result ↔ mergeCoveredByPrefix x intervals n) ∧
  mergeStartsFromPrefix intervals result n

method buildInsertSource (intervals : Array Interval) (newInterval : Interval)
  returns (source : Array Interval)
  requires sorted_input: canonical intervals
  ensures built: source = insertSource intervals newInterval
do
  let mut rest := intervals.toList
  let mut acc : List Interval := []
  let mut answer : Option (Array Interval) := none
  while active: rest ≠ [] ∧ answer = none
    invariant continuation:
      answer = none → insertSourceGo rest newInterval acc = insertSource intervals newInterval
    invariant answer_correct:
      ∀ source, answer = some source → source = insertSource intervals newInterval
    decreasing remaining: rest.length
    done_with finished: rest = [] ∨ answer ≠ none
  do
    match rest with
    | [] => answer := answer
    | iv :: tail =>
      if before: intervalLexLe newInterval iv then
        answer := some ((acc.reverse ++ newInterval :: iv :: tail).toArray)
        rest := []
      else
        acc := iv :: acc
        rest := tail
  match answer with
  | some source => return source
  | none => return (newInterval :: acc).reverse.toArray

method mergeSource (intervals : Array Interval)
  returns (result : Array Interval)
  requires valid_sorted: mergePrecondition intervals
  ensures merged: mergePostcondition intervals result
do
  let mut i : Nat := 0
  let mut result : Array Interval := #[]
  while scanning: i < intervals.size
    invariant merged_prefix: MergeInvariant intervals i result
    decreasing remaining: intervals.size - i
  do
    result := mergeStep result intervals[i]!
    i := i + 1
  return result

method insertInterval (intervals : Array Interval) (newInterval : Interval)
  returns (result : Array Interval)
  requires canonical_input: precondition intervals newInterval
  ensures inserted: postcondition intervals newInterval result
do
  let mut result : Array Interval := #[]
  let mut curStart : Int := istart newInterval
  let mut curEnd : Int := iend newInterval
  let mut i : Nat := 0
  let mut inserted : Bool := false
  while scanning: i < intervals.size
    invariant i_bounds: i ≤ intervals.size
    invariant pending_wf: curStart ≤ curEnd
    invariant result_canonical: canonical result
    invariant result_before_next: i < intervals.size →
      (result.size = 0 ∨ iend result[result.size - 1]! < istart intervals[i]!)
    invariant result_before_pending: inserted = false →
      (result.size = 0 ∨ iend result[result.size - 1]! < curStart)
    invariant coverage: ∀ x : Int,
      (coveredBy x result ∨ (inserted = false ∧ memInterval x (curStart, curEnd))) ↔
        (coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval)
    invariant inserted_pending: inserted = true →
      ∃ j : Nat, j < result.size ∧ result[j]! = (curStart, curEnd)
    decreasing remaining: intervals.size - i
    done_with done: i = intervals.size
  do
    let iv := intervals[i]!
    let s := istart iv
    let e := iend iv
    if already_inserted: inserted then
      result := result.push iv
      i := i + 1
    else if before_pending: e < curStart then
      result := result.push iv
      i := i + 1
    else if pending_before: curEnd < s then
      result := result.push (curStart, curEnd)
      inserted := true
      result := result.push iv
      i := i + 1
    else
      if extend_left: s < curStart then curStart := s
      if extend_right: curEnd < e then curEnd := e
      i := i + 1
  if not_inserted: inserted = false then
    result := result.push (curStart, curEnd)
  return result

end Implementation

section Proof

theorem merge_starts_le_of_lt (a : Array Interval) (h : mergeLexSorted a)
    {i j : Nat} (hij : i < j) (hj : j < a.size) : istart a[i]! ≤ istart a[j]! := by
  have adjacent : ∀ k, k + 1 < a.size → istart a[k]! ≤ istart a[k + 1]! := by
    intro k hk
    rcases h k hk with hlt | heq | heq
    · exact hlt.le
    · exact heq.1.le
    · exact heq.1.le
  have chain : ∀ d k, k + d < a.size → istart a[k]! ≤ istart a[k + d]! := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro k hkd
        cases d with
        | zero => simpa using adjacent k (by omega)
        | succ d => exact (ih k (by omega)).trans (adjacent (k + d + 1) (by omega))
  have heq : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  have hc := chain (j - i) i (by simpa [heq] using hj)
  simpa [heq] using hc

theorem mergeCoveredByPrefix_succ (intervals : Array Interval) (i : Nat)
    (hi : i < intervals.size) (x : Int) :
    mergeCoveredByPrefix x intervals (i + 1) ↔
      mergeCoveredByPrefix x intervals i ∨ memInterval x intervals[i]! := by
  constructor
  · rintro ⟨j, hj, hjs, hx⟩
    by_cases hji : j < i
    · exact Or.inl ⟨j, hji, hjs, hx⟩
    · have : j = i := by omega
      subst j
      exact Or.inr hx
  · rintro (⟨j, hj, hjs, hx⟩ | hx)
    · exact ⟨j, by omega, hjs, hx⟩
    · exact ⟨i, by omega, hi, hx⟩

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

theorem getElem!_set!_ne' [Inhabited α] (a : Array α) (k j : Nat) (v : α)
    (hjk : j ≠ k) : (a.set! k v)[j]! = a[j]! := by
  exact Array.getElem!_set!_ne a k j v (Ne.symm hjk)

theorem mergeCovered_push (a : Array Interval) (iv : Interval) (x : Int) :
    mergeCoveredBy x (a.push iv) ↔ mergeCoveredBy x a ∨ memInterval x iv := by
  constructor
  · rintro ⟨j, hj, hx⟩
    by_cases hja : j < a.size
    · rw [getElem!_push_lt' a iv j hja] at hx
      exact Or.inl ⟨j, hja, hx⟩
    · have hjeq : j = a.size := by simp at hj; omega
      subst j
      rw [getElem!_push_eq'] at hx
      exact Or.inr hx
  · rintro (⟨j, hj, hx⟩ | hx)
    · refine ⟨j, by simp; omega, ?_⟩
      rw [getElem!_push_lt' a iv j hj]
      exact hx
    · refine ⟨a.size, by simp, ?_⟩
      rw [getElem!_push_eq']
      exact hx

theorem mergeCovered_setLast (a : Array Interval) (iv : Interval)
    (hne : a.size ≠ 0) (hstart : istart a[a.size - 1]! ≤ istart iv)
    (hoverlap : istart iv ≤ iend a[a.size - 1]!) (x : Int) :
    mergeCoveredBy x
        (a.set! (a.size - 1) (istart a[a.size - 1]!, max (iend a[a.size - 1]!) (iend iv))) ↔
      mergeCoveredBy x a ∨ memInterval x iv := by
  let k := a.size - 1
  have hk : k < a.size := by
    dsimp [k]
    omega
  let merged : Interval := (istart a[k]!, max (iend a[k]!) (iend iv))
  have hlast : memInterval x a[k]! → memInterval x merged := by
    rintro ⟨hlo, hhi⟩
    exact ⟨hlo, hhi.trans (le_max_left _ _)⟩
  have hiv : memInterval x iv → memInterval x merged := by
    rintro ⟨hlo, hhi⟩
    exact ⟨hstart.trans hlo, hhi.trans (le_max_right _ _)⟩
  have hsplit : memInterval x merged → memInterval x a[k]! ∨ memInterval x iv := by
    rintro ⟨hlo, hhi⟩
    simp [merged, iend] at hhi
    by_cases hxle : x ≤ iend a[k]!
    · exact Or.inl ⟨hlo, hxle⟩
    · refine Or.inr ⟨hoverlap.trans (le_of_not_ge hxle), ?_⟩
      rcases hhi with hleft | hright
      · exact False.elim (hxle hleft)
      · exact hright
  change mergeCoveredBy x (a.set! k merged) ↔ _
  constructor
  · rintro ⟨j, hj, hx⟩
    by_cases hjk : j = k
    · subst j
      unfold memInterval istart iend at hx ⊢
      have hm : memInterval x merged := by
        rw [Array.getElem!_set!_self _ _ _ hk] at hx
        exact hx
      rcases hsplit hm with hl | hr
      · exact Or.inl ⟨k, hk, hl⟩
      · exact Or.inr hr
    · rw [getElem!_set!_ne' a k j merged hjk] at hx
      exact Or.inl ⟨j, by simpa [Array.size_set!] using hj, hx⟩
  · rintro (⟨j, hj, hx⟩ | hx)
    · refine ⟨j, by simpa [Array.size_set!] using hj, ?_⟩
      by_cases hjk : j = k
      · subst j
        unfold memInterval istart iend at hx ⊢
        rw [Array.getElem!_set!_self _ _ _ hk]
        exact hlast hx
      · rw [getElem!_set!_ne' a k j merged hjk]
        exact hx
    · refine ⟨k, by simpa [Array.size_set!] using hk, ?_⟩
      unfold memInterval istart iend at hx ⊢
      rw [Array.getElem!_set!_self _ _ _ hk]
      exact hiv hx

theorem setLastEnd_start_eq (a : Array Interval) (e : Int) (j : Nat)
    (hne : a.size ≠ 0) :
    istart (a.set! (a.size - 1) (istart a[a.size - 1]!, e))[j]! = istart a[j]! := by
  let k := a.size - 1
  have hk : k < a.size := by
    dsimp [k]
    omega
  by_cases hjk : j = k
  · subst j
    unfold istart
    rw [Array.getElem!_set!_self _ _ _ hk]
  · rw [getElem!_set!_ne' a k j _ hjk]

theorem setLastEnd_valid (a : Array Interval) (e : Int) (_hne : a.size ≠ 0)
    (hvalid : mergeAllValid a) (he : iend a[a.size - 1]! ≤ e) :
    mergeAllValid (a.set! (a.size - 1) (istart a[a.size - 1]!, e)) := by
  intro j hj
  have hjo : j < a.size := by simpa [Array.size_set!] using hj
  let k := a.size - 1
  have hk : k < a.size := by
    dsimp [k]
    omega
  by_cases hjk : j = k
  · subst j
    unfold istart iend
    rw [Array.getElem!_set!_self _ _ _ hk]
    exact (hvalid k hk).trans he
  · rw [getElem!_set!_ne' a k j _ hjk]
    exact hvalid j hjo

theorem setLastEnd_starts (a : Array Interval) (e : Int) (hne : a.size ≠ 0)
    (h : mergeNondecreasingStarts a) :
    mergeNondecreasingStarts (a.set! (a.size - 1) (istart a[a.size - 1]!, e)) := by
  intro j hj
  have hjo : j + 1 < a.size := by simpa [Array.size_set!] using hj
  rw [setLastEnd_start_eq a e j hne, setLastEnd_start_eq a e (j + 1) hne]
  exact h j hjo

theorem setLastEnd_separated (a : Array Interval) (e : Int) (hne : a.size ≠ 0)
    (h : mergeStrictlyNonOverlapping a) :
    mergeStrictlyNonOverlapping (a.set! (a.size - 1) (istart a[a.size - 1]!, e)) := by
  intro j hj
  have hjo : j + 1 < a.size := by simpa [Array.size_set!] using hj
  have hjk : j ≠ a.size - 1 := by omega
  unfold iend
  rw [getElem!_set!_ne' a (a.size - 1) j _ hjk]
  change iend a[j]! < istart _
  rw [setLastEnd_start_eq a e (j + 1) hne]
  exact h j hjo

theorem mergeInvariant_step (intervals : Array Interval) (i : Nat)
    (result : Array Interval) (hpre : mergePrecondition intervals)
    (hinv : MergeInvariant intervals i result) (hi : i < intervals.size) :
    MergeInvariant intervals (i + 1) (mergeStep result intervals[i]!) := by
  rcases hinv with ⟨hin, hvalid, hstarts, hsep, hcover, horigin⟩
  unfold mergeStep
  by_cases hempty : result.size = 0
  · have hresult : result = #[] := Array.size_eq_zero_iff.mp hempty
    subst result
    simp
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp at hk
      have hk0 : k = 0 := by omega
      subst k
      simpa [mergeAllValid, getElem!_pos, hi] using hpre.1 i hi
    · intro k hk
      simp at hk
    · intro k hk
      simp at hk
    · intro x
      constructor
      · rintro ⟨k, hk, hx⟩
        simp at hk
        have hk0 : k = 0 := by omega
        subst k
        refine ⟨i, by omega, hi, ?_⟩
        simpa [getElem!_pos, hi] using hx
      · rintro ⟨j, hj, hjs, hx⟩
        have hji : j < i ∨ j = i := by omega
        rcases hji with hji | rfl
        · have : mergeCoveredBy x (#[] : Array Interval) :=
            (hcover x).2 ⟨j, hji, hjs, hx⟩
          rcases this with ⟨k, hk, _⟩
          omega
        · refine ⟨0, by simp, ?_⟩
          simpa [getElem!_pos, hi] using hx
    · intro k hk
      simp at hk
      have hk0 : k = 0 := by omega
      subst k
      refine ⟨i, by omega, hi, ?_⟩
      simp [istart, getElem!_pos, hi]
  · simp only [hempty, ite_false]
    dsimp
    let k := result.size - 1
    have hk : k < result.size := by
      dsimp [k]
      omega
    rcases horigin k hk with ⟨j, hj, hjs, hstart_origin⟩
    have hlast_start : istart result[k]! ≤ istart intervals[i]! := by
      rw [hstart_origin]
      exact merge_starts_le_of_lt intervals hpre.2 hj hi
    by_cases hoverlap : istart intervals[i]! ≤ iend result[k]!
    · have hoverlap' : intervals[i]!.1 ≤ result[result.size - 1]!.2 := by
        simpa [k, istart, iend] using hoverlap
      simp only [hoverlap', ite_true]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [k, istart, iend] using
          setLastEnd_valid result (max (iend result[k]!) (iend intervals[i]!)) hempty
            hvalid (le_max_left _ _)
      · simpa [k, istart, iend] using
          setLastEnd_starts result (max (iend result[k]!) (iend intervals[i]!)) hempty hstarts
      · simpa [k, istart, iend] using
          setLastEnd_separated result (max (iend result[k]!) (iend intervals[i]!)) hempty hsep
      · intro x
        have hc := mergeCovered_setLast result intervals[i]! hempty hlast_start hoverlap x
        have hp := mergeCoveredByPrefix_succ intervals i hi x
        simpa [k, istart, iend] using
          (hc.trans ((or_congr (hcover x) Iff.rfl).trans hp.symm))
      · intro q hq
        have hqo : q < result.size := by simpa [Array.size_set!] using hq
        rcases horigin q hqo with ⟨t, ht, hts, heq⟩
        refine ⟨t, by omega, hts, ?_⟩
        simpa [k, istart, iend] using
          (setLastEnd_start_eq result
            (max (iend result[k]!) (iend intervals[i]!)) q hempty).trans heq
    · have hoverlap' : ¬intervals[i]!.1 ≤ result[result.size - 1]!.2 := by
        simpa [k, istart, iend] using hoverlap
      simp only [hoverlap', ite_false]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
        by_cases hqo : q < result.size
        · rw [getElem!_push_lt' result intervals[i]! q hqo]
          exact hvalid q hqo
        · have hqeq : q = result.size := by omega
          subst q
          rw [getElem!_push_eq']
          exact hpre.1 i hi
      · intro q hq
        simp at hq
        by_cases hnext : q + 1 < result.size
        · rw [getElem!_push_lt' result intervals[i]! q (by omega),
            getElem!_push_lt' result intervals[i]! (q + 1) hnext]
          exact hstarts q hnext
        · have hnext_eq : q + 1 = result.size := by omega
          have hqeq : q = k := by simp [k]; omega
          subst q
          rw [getElem!_push_lt' result intervals[i]! k hk]
          rw [hnext_eq, getElem!_push_eq']
          exact hlast_start
      · intro q hq
        simp at hq
        by_cases hnext : q + 1 < result.size
        · rw [getElem!_push_lt' result intervals[i]! q (by omega),
            getElem!_push_lt' result intervals[i]! (q + 1) hnext]
          exact hsep q hnext
        · have hqeq : q = k := by simp [k]; omega
          have hnext_eq : q + 1 = result.size := by omega
          subst q
          rw [getElem!_push_lt' result intervals[i]! k hk]
          rw [hnext_eq, getElem!_push_eq']
          exact lt_of_not_ge hoverlap
      · intro x
        exact (mergeCovered_push result intervals[i]! x).trans
          ((or_congr (hcover x) Iff.rfl).trans
            (mergeCoveredByPrefix_succ intervals i hi x).symm)
      · intro q hq
        simp at hq
        by_cases hqo : q < result.size
        · rcases horigin q hqo with ⟨t, ht, hts, heq⟩
          refine ⟨t, by omega, hts, ?_⟩
          rw [getElem!_push_lt' result intervals[i]! q hqo]
          exact heq
        · have hqeq : q = result.size := by omega
          subst q
          refine ⟨i, by omega, hi, ?_⟩
          rw [getElem!_push_eq']

theorem mergeCoveredByPrefix_full (intervals : Array Interval) (x : Int) :
    mergeCoveredByPrefix x intervals intervals.size ↔ mergeCoveredBy x intervals := by
  constructor
  · rintro ⟨j, _, hj, hx⟩
    exact ⟨j, hj, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, hj, hj, hx⟩

prove_correct mergeSource by
  velvet_vcgen [mergeSource] with try finish
  case merged_prefix =>
    simp [MergeInvariant, mergeAllValid, mergeNondecreasingStarts,
      mergeStrictlyNonOverlapping, mergeCoveredBy, mergeCoveredByPrefix,
      mergeStartsFromPrefix]
  case merged =>
    rename_i intervals
    rcases merged_prefix with ⟨hi, hvalid, hstarts, hsep, hcover, _⟩
    have hieq : i = intervals.size := by omega
    subst i
    exact ⟨hvalid, hstarts, hsep,
      fun x => (hcover x).trans (mergeCoveredByPrefix_full intervals x)⟩
  case merged_prefix =>
    exact mergeInvariant_step _ _ _ valid_sorted merged_prefix scanning

theorem intervalLexLe_total (a b : Interval) :
    intervalLexLe a b ∨ intervalLexLe b a := by
  unfold intervalLexLe istart iend
  omega

theorem intervalLexLe_trans (a b c : Interval) :
    intervalLexLe a b → intervalLexLe b c → intervalLexLe a c := by
  unfold intervalLexLe istart iend
  omega

theorem starts_lt_of_lt (a : Array Interval) (h : canonical a)
    {i j : Nat} (hij : i < j) (hj : j < a.size) : istart a[i]! < istart a[j]! := by
  have adjacent : ∀ k, k + 1 < a.size → istart a[k]! < istart a[k + 1]! := by
    intro k hk
    exact (h.2.2 k (by omega)).trans_lt (h.2.1 k hk)
  have chain : ∀ d k, 0 < d → k + d < a.size → istart a[k]! < istart a[k + d]! := by
    intro d
    induction d with
    | zero => omega
    | succ d ih =>
        intro k hd hkd
        cases d with
        | zero => simpa using adjacent k (by omega)
        | succ d => exact (ih k (by omega) (by omega)).trans (adjacent (k + d + 1) (by omega))
  have heq : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  have hc := chain (j - i) i (Nat.sub_pos_of_lt hij) (by simpa [heq] using hj)
  simpa [heq] using hc

theorem input_pairwise_lex (a : Array Interval) (h : canonical a) :
    a.toList.Pairwise intervalLexLe := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  apply Or.inl
  have hi' : i < a.size := by simpa using hi
  have hj' : j < a.size := by simpa using hj
  change istart a[i] < istart a[j]
  simpa only [getElem!_pos a i hi', getElem!_pos a j hj'] using
    starts_lt_of_lt a h hij hj'

theorem getElem!_toArray' [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    l.toArray[i]! = l[i] := by
  have hia : i < l.toArray.size := by simpa using hi
  calc
    l.toArray[i]! = l.toArray[i] := getElem!_pos l.toArray i hia
    _ = l[i] := List.getElem_toArray hia

theorem source_pairwise_lex (intervals : Array Interval) (newInterval : Interval)
    (h : canonical intervals) :
    (intervals.toList.orderedInsert intervalLexLe newInterval).Pairwise intervalLexLe := by
  let : Std.Total intervalLexLe := ⟨intervalLexLe_total⟩
  let : IsTrans Interval intervalLexLe := ⟨intervalLexLe_trans⟩
  exact (input_pairwise_lex intervals h).orderedInsert newInterval _

theorem source_lexSorted (intervals : Array Interval) (newInterval : Interval)
    (h : canonical intervals) :
    mergeLexSorted (insertSource intervals newInterval) := by
  let sourceList := intervals.toList.orderedInsert intervalLexLe newInterval
  have hp : sourceList.Pairwise intervalLexLe := source_pairwise_lex intervals newInterval h
  intro i hi
  have hil : i < sourceList.length := by simpa [insertSource, sourceList] using (show i < (insertSource intervals newInterval).size by omega)
  have hjl : i + 1 < sourceList.length := by simpa [insertSource, sourceList] using hi
  have hr := (List.pairwise_iff_getElem.mp hp) i (i + 1) hil hjl (by omega)
  change sourceList.toArray[i]!.1 < sourceList.toArray[i + 1]!.1 ∨
    (sourceList.toArray[i]!.1 = sourceList.toArray[i + 1]!.1 ∧
      sourceList.toArray[i]!.2 ≤ sourceList.toArray[i + 1]!.2) ∨
    (sourceList.toArray[i]!.1 = sourceList.toArray[i + 1]!.1 ∧
      sourceList.toArray[i]!.2 = sourceList.toArray[i + 1]!.2)
  rw [getElem!_toArray' sourceList i hil, getElem!_toArray' sourceList (i + 1) hjl]
  unfold intervalLexLe at hr
  exact hr.elim Or.inl (fun he => Or.inr (Or.inl he))

theorem source_allValid (intervals : Array Interval) (newInterval : Interval)
    (h : precondition intervals newInterval) :
    mergeAllValid (insertSource intervals newInterval) := by
  intro i hi
  let sourceList := intervals.toList.orderedInsert intervalLexLe newInterval
  have hil : i < sourceList.length := by simpa [insertSource, sourceList] using hi
  have hmem : sourceList[i] ∈ sourceList := List.getElem_mem hil
  have hchoice : sourceList[i] = newInterval ∨ sourceList[i] ∈ intervals.toList := by
    simpa [sourceList] using (List.mem_orderedInsert (r := intervalLexLe)).mp hmem
  rcases hchoice with heq | hold
  · change sourceList.toArray[i]!.1 ≤ sourceList.toArray[i]!.2
    rw [getElem!_toArray' sourceList i hil, heq]
    exact h.2
  · rcases List.mem_iff_getElem.mp hold with ⟨j, hj, hjeq⟩
    have hjarr : j < intervals.size := by simpa using hj
    have hwf := h.1.2.2 j hjarr
    change sourceList.toArray[i]!.1 ≤ sourceList.toArray[i]!.2
    rw [getElem!_toArray' sourceList i hil, ← hjeq]
    have hlistget : intervals.toList[j] = intervals[j] := by simp
    rw [hlistget]
    simpa only [wfInterval, istart, iend, getElem!_pos intervals j hjarr] using hwf

theorem coveredBy_iff_mem (x : Int) (a : Array Interval) :
    coveredBy x a ↔ ∃ iv, iv ∈ a.toList ∧ memInterval x iv := by
  constructor
  · rintro ⟨i, hi, hx⟩
    refine ⟨a[i]!, ?_, hx⟩
    have hil : i < a.toList.length := by simpa using hi
    simp [getElem!_pos, hi]
  · rintro ⟨iv, hiv, hx⟩
    rcases List.mem_iff_getElem.mp hiv with ⟨i, hi, heq⟩
    have hi' : i < a.size := by simpa using hi
    refine ⟨i, hi', ?_⟩
    have hget : a[i]! = iv := by
      rw [getElem!_pos a i hi']
      simpa using heq
    rw [hget]
    exact hx

theorem covered_insertSource (x : Int) (intervals : Array Interval)
    (newInterval : Interval) :
    coveredBy x (insertSource intervals newInterval) ↔
      coveredBy x intervals ∨ memInterval x newInterval := by
  rw [coveredBy_iff_mem]
  constructor
  · rintro ⟨iv, hiv, hx⟩
    have hiv' : iv ∈ intervals.toList.orderedInsert intervalLexLe newInterval := by
      simpa [insertSource] using hiv
    have hc := (List.mem_orderedInsert (r := intervalLexLe)).mp
      hiv'
    rcases hc with rfl | hold
    · exact Or.inr hx
    · exact Or.inl ((coveredBy_iff_mem x intervals).2 ⟨iv, hold, hx⟩)
  · rintro (hold | hnew)
    · rcases (coveredBy_iff_mem x intervals).1 hold with ⟨iv, hiv, hx⟩
      refine ⟨iv, ?_, hx⟩
      simpa [insertSource] using
        (List.mem_orderedInsert (r := intervalLexLe) (a := iv) (b := newInterval) (l := intervals.toList)).2 (Or.inr hiv)
    · refine ⟨newInterval, ?_, hnew⟩
      simp [insertSource]

theorem source_precondition (intervals : Array Interval) (newInterval : Interval)
    (h : precondition intervals newInterval) :
    mergePrecondition (insertSource intervals newInterval) :=
  ⟨source_allValid intervals newInterval h,
    source_lexSorted intervals newInterval h.1⟩

theorem merged_implies_inserted (intervals : Array Interval) (newInterval : Interval)
    (result : Array Interval)
    (h : mergePostcondition (insertSource intervals newInterval) result) :
    postcondition intervals newInterval result := by
  rcases h with ⟨hvalid, hstarts, hsep, hcover⟩
  have hcanonical : canonical result := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sortedByStart, mergeNondecreasingStarts] using hstarts
    · simpa [noOverlapConsecutive, mergeStrictlyNonOverlapping] using hsep
    · simpa [allWf, wfInterval, mergeAllValid] using hvalid
  refine ⟨hcanonical, ?_, hcanonical.2.1⟩
  intro x
  have hm : coveredBy x result ↔ coveredBy x (insertSource intervals newInterval) := by
    simpa [coveredBy, mergeCoveredBy] using hcover x
  exact hm.trans (covered_insertSource x intervals newInterval)

theorem insertSourceGo_eq (rest : List Interval) (newInterval : Interval)
    (acc : List Interval) :
    insertSourceGo rest newInterval acc =
      (acc.reverse ++ rest.orderedInsert intervalLexLe newInterval).toArray := by
  induction rest generalizing acc with
  | nil => simp [insertSourceGo]
  | cons iv tail ih =>
      rw [insertSourceGo.eq_def, List.orderedInsert_cons]
      by_cases h : intervalLexLe newInterval iv
      · simp [h]
      · simp [h, ih, List.reverse_cons, List.append_assoc]

theorem canonical_empty : canonical (#[] : Array Interval) := by
  constructor
  · intro i hi; simp at hi
  · constructor
    · intro i hi; simp at hi
    · intro i hi; simp at hi

theorem canonical_push (a : Array Interval) (iv : Interval)
    (hcanon : canonical a) (hwf : wfInterval iv)
    (hlast : a.size = 0 ∨ iend a[a.size - 1]! < istart iv) :
    canonical (a.push iv) := by
  rcases hcanon with ⟨hsorted, hsep, hall⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hnext : k + 1 < a.size
    · rw [getElem!_push_lt' a iv k (by omega),
          getElem!_push_lt' a iv (k + 1) hnext]
      exact hsorted k hnext
    · have hne : a.size ≠ 0 := by omega
      have hk_last : k = a.size - 1 := by omega
      subst k
      have hadd : a.size - 1 + 1 = a.size := by omega
      rw [hadd]
      rw [getElem!_push_lt' a iv (a.size - 1) (by omega), getElem!_push_eq' a iv]
      exact (hall (a.size - 1) (by omega)).trans (hlast.resolve_left hne).le
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hnext : k + 1 < a.size
    · rw [getElem!_push_lt' a iv k (by omega),
          getElem!_push_lt' a iv (k + 1) hnext]
      exact hsep k hnext
    · have hne : a.size ≠ 0 := by omega
      have hk_last : k = a.size - 1 := by omega
      subst k
      have hadd : a.size - 1 + 1 = a.size := by omega
      rw [hadd]
      rw [getElem!_push_lt' a iv (a.size - 1) (by omega), getElem!_push_eq' a iv]
      exact hlast.resolve_left hne
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hka : k < a.size
    · rw [getElem!_push_lt' a iv k hka]
      exact hall k hka
    · have : k = a.size := by omega
      subst k
      rw [getElem!_push_eq']
      exact hwf

theorem coveredBy_push (x : Int) (a : Array Interval) (iv : Interval) :
    coveredBy x (a.push iv) ↔ coveredBy x a ∨ memInterval x iv := by
  simpa [coveredBy, mergeCoveredBy] using mergeCovered_push a iv x

theorem coveredBy_extract_succ (x : Int) (a : Array Interval) (i : Nat)
    (hi : i < a.size) :
    coveredBy x (a.extract 0 (i + 1)) ↔
      coveredBy x (a.extract 0 i) ∨ memInterval x a[i]! := by
  have hext : a.extract 0 (i + 1) = (a.extract 0 i).push a[i]! := by
    have h := Array.extract_succ_right (as := a) (i := 0) (j := i) (Nat.succ_pos i) hi
    rw [getElem!_pos a i hi]
    exact h
  rw [hext, coveredBy_push]

theorem memInterval_union_overlap (x : Int) (a b : Interval)
    (hwa : wfInterval a) (hwb : wfInterval b)
    (hab : ¬iend a < istart b) (hba : ¬iend b < istart a) :
    memInterval x a ∨ memInterval x b ↔
      memInterval x (min (istart a) (istart b), max (iend a) (iend b)) := by
  rcases a with ⟨as, ae⟩
  rcases b with ⟨bs, be⟩
  simp only [wfInterval, memInterval, istart, iend] at *
  simp only [min_def, max_def]
  split_ifs <;> omega

theorem finish_not_inserted (intervals : Array Interval) (newInterval pending : Interval)
    (result : Array Interval) (hcanon : canonical result) (hwf : wfInterval pending)
    (hlast : result.size = 0 ∨ iend result[result.size - 1]! < istart pending)
    (hcoverage : ∀ x, coveredBy x result ∨ memInterval x pending ↔
      coveredBy x intervals ∨ memInterval x newInterval) :
    postcondition intervals newInterval (result.push pending) := by
  have hc := canonical_push result pending hcanon hwf hlast
  refine ⟨hc, ?_, hc.2.1⟩
  intro x
  rw [coveredBy_push]
  exact hcoverage x

theorem finish_inserted (intervals : Array Interval) (newInterval : Interval)
    (result : Array Interval) (hcanon : canonical result)
    (hcoverage : ∀ x, coveredBy x result ↔
      coveredBy x intervals ∨ memInterval x newInterval) :
    postcondition intervals newInterval result := by
  exact ⟨hcanon, hcoverage, hcanon.2.1⟩

theorem coverage_push_step (intervals : Array Interval) (newInterval pending : Interval)
    (result : Array Interval) (inserted : Bool) (i : Nat) (hi : i < intervals.size)
    (hcoverage : ∀ x,
      coveredBy x result ∨ inserted = false ∧ memInterval x pending ↔
        coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval) :
    ∀ x,
      coveredBy x (result.push intervals[i]!) ∨ inserted = false ∧ memInterval x pending ↔
        coveredBy x (intervals.extract 0 (i + 1)) ∨ memInterval x newInterval := by
  intro x
  rw [coveredBy_push, coveredBy_extract_succ x intervals i hi]
  constructor
  · rintro ((hres | hiv) | hpending)
    · rcases (hcoverage x).1 (Or.inl hres) with hprefix | hnew
      · exact Or.inl (Or.inl hprefix)
      · exact Or.inr hnew
    · exact Or.inl (Or.inr hiv)
    · rcases (hcoverage x).1 (Or.inr hpending) with hprefix | hnew
      · exact Or.inl (Or.inl hprefix)
      · exact Or.inr hnew
  · rintro ((hprefix | hiv) | hnew)
    · rcases (hcoverage x).2 (Or.inl hprefix) with hres | hpending
      · exact Or.inl (Or.inl hres)
      · exact Or.inr hpending
    · exact Or.inl (Or.inr hiv)
    · rcases (hcoverage x).2 (Or.inr hnew) with hres | hpending
      · exact Or.inl (Or.inl hres)
      · exact Or.inr hpending

theorem canonical_input_wf (intervals : Array Interval) (newInterval : Interval)
    (hpre : precondition intervals newInterval) (i : Nat) (hi : i < intervals.size) :
    wfInterval intervals[i]! := hpre.1.2.2 i hi

theorem input_next_separated (intervals : Array Interval) (newInterval : Interval)
    (hpre : precondition intervals newInterval) (i : Nat) (hi : i + 1 < intervals.size) :
    iend intervals[i]! < istart intervals[i + 1]! := hpre.1.2.1 i hi

theorem unchanged_result_before_next (intervals : Array Interval) (newInterval : Interval)
    (result : Array Interval) (i : Nat) (hi : i < intervals.size)
    (hbefore : result.size = 0 ∨ iend result[result.size - 1]! < istart intervals[i]!)
    (hnext : i + 1 < intervals.size) (hpre : precondition intervals newInterval) :
    result.size = 0 ∨ iend result[result.size - 1]! < istart intervals[i + 1]! := by
  rcases hbefore with hempty | hlast
  · exact Or.inl hempty
  · right
    exact hlast.trans ((hpre.1.2.2 i hi).trans_lt
      (input_next_separated intervals newInterval hpre i hnext))

theorem pushed_before_next (result : Array Interval) (iv next : Interval) :
    iend (result.push iv)[(result.push iv).size - 1]! < istart next ↔
      iend iv < istart next := by
  have heq : (result.push iv).size - 1 = result.size := by simp
  rw [heq, getElem!_push_eq']

theorem witness_survives_push (result : Array Interval) (iv pending : Interval)
    (h : ∃ j, j < result.size ∧ result[j]! = pending) :
    ∃ j, j < (result.push iv).size ∧ (result.push iv)[j]! = pending := by
  rcases h with ⟨j, hj, heq⟩
  exact ⟨j, by simp; omega, by rw [getElem!_push_lt' result iv j hj]; exact heq⟩

theorem coverage_merge_step (intervals : Array Interval)
    (newInterval oldPending newPending : Interval) (result : Array Interval)
    (i : Nat) (hi : i < intervals.size)
    (hcoverage : ∀ x, coveredBy x result ∨ memInterval x oldPending ↔
      coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval)
    (hunion : ∀ x, memInterval x oldPending ∨ memInterval x intervals[i]! ↔
      memInterval x newPending) :
    ∀ x, coveredBy x result ∨ memInterval x newPending ↔
      coveredBy x (intervals.extract 0 (i + 1)) ∨ memInterval x newInterval := by
  intro x
  rw [coveredBy_extract_succ x intervals i hi]
  constructor
  · rintro (hres | hmerged)
    · rcases (hcoverage x).1 (Or.inl hres) with hprefix | hnew
      · exact Or.inl (Or.inl hprefix)
      · exact Or.inr hnew
    · rcases (hunion x).2 hmerged with hpending | hiv
      · rcases (hcoverage x).1 (Or.inr hpending) with hprefix | hnew
        · exact Or.inl (Or.inl hprefix)
        · exact Or.inr hnew
      · exact Or.inl (Or.inr hiv)
  · rintro ((hprefix | hiv) | hnew)
    · rcases (hcoverage x).2 (Or.inl hprefix) with hres | hpending
      · exact Or.inl hres
      · exact Or.inr ((hunion x).1 (Or.inl hpending))
    · exact Or.inr ((hunion x).1 (Or.inr hiv))
    · rcases (hcoverage x).2 (Or.inr hnew) with hres | hpending
      · exact Or.inl hres
      · exact Or.inr ((hunion x).1 (Or.inl hpending))

prove_correct buildInsertSource by
  velvet_vcgen [buildInsertSource] with try finish
  case continuation =>
    rename_i intervals newStart newEnd
    simpa [insertSource] using insertSourceGo_eq intervals.toList (newStart, newEnd) []
  case built =>
    have hrest : rest = [] := by
      rcases finished with h | h
      · exact h
      · exact absurd h_none h
    have hc := continuation h_none
    subst rest
    rw [insertSourceGo.eq_def] at hc
    exact hc
  case answer_correct =>
    intro source hsource
    have hc := continuation active.2
    rw [h_cons, insertSourceGo.eq_def] at hc
    simp [before] at hc
    exact (Option.some.inj hsource).symm.trans hc
  case continuation =>
    intro _
    have hc := continuation active.2
    rw [h_cons, insertSourceGo.eq_def] at hc
    simpa [before] using hc

prove_correct insertInterval by
  velvet_vcgen [insertInterval] with try finish
  case pending_wf => exact canonical_input.2
  case result_canonical => exact canonical_empty
  case inserted =>
    rename_i intervals newStart newEnd
    have hext : intervals.extract 0 i = intervals := by subst i; simp
    have hcov : ∀ x, coveredBy x result ∨ memInterval x (curStart, curEnd) ↔
        coveredBy x intervals ∨ memInterval x (newStart, newEnd) := by
      intro x
      simpa [not_inserted, hext] using coverage x
    exact finish_not_inserted intervals (newStart, newEnd) (curStart, curEnd) result
      result_canonical pending_wf (result_before_pending not_inserted) hcov
  case inserted =>
    rename_i intervals newStart newEnd
    have hins : inserted = true := by cases inserted <;> simp_all
    have hext : intervals.extract 0 i = intervals := by subst i; simp
    have hcov : ∀ x, coveredBy x result ↔
        coveredBy x intervals ∨ memInterval x (newStart, newEnd) := by
      intro x
      simpa [hins, hext] using coverage x
    exact finish_inserted intervals (newStart, newEnd) result result_canonical hcov
  case result_canonical =>
    rename_i intervals newStart newEnd
    exact canonical_push result intervals[i]! result_canonical
      (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
      (result_before_next scanning)
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    right
    rw [pushed_before_next]
    exact input_next_separated intervals (newStart, newEnd) canonical_input i hnext
  case coverage =>
    rename_i intervals newStart newEnd
    exact coverage_push_step intervals (newStart, newEnd) (curStart, curEnd) result inserted i
      scanning coverage
  case inserted_pending =>
    rename_i intervals newStart newEnd
    intro _
    exact witness_survives_push result intervals[i]! (curStart, curEnd)
      (inserted_pending already_inserted)
  case result_canonical =>
    rename_i intervals newStart newEnd
    exact canonical_push result intervals[i]! result_canonical
      (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
      (result_before_next scanning)
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    right
    rw [pushed_before_next]
    exact input_next_separated intervals (newStart, newEnd) canonical_input i hnext
  case coverage =>
    rename_i intervals newStart newEnd
    exact coverage_push_step intervals (newStart, newEnd) (curStart, curEnd) result inserted i
      scanning coverage
  case result_canonical =>
    rename_i intervals newStart newEnd
    have hins : inserted = false := by cases inserted <;> simp_all
    have hc1 := canonical_push result (curStart, curEnd) result_canonical pending_wf
      (result_before_pending hins)
    apply canonical_push (result.push (curStart, curEnd)) intervals[i]! hc1
      (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
    right
    rw [pushed_before_next]
    exact pending_before
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    right
    rw [pushed_before_next]
    exact input_next_separated intervals (newStart, newEnd) canonical_input i hnext
  case coverage =>
    rename_i intervals newStart newEnd
    have hins : inserted = false := by cases inserted <;> simp_all
    have hcov1 : ∀ x, coveredBy x (result.push (curStart, curEnd)) ↔
        coveredBy x (intervals.extract 0 i) ∨ memInterval x (newStart, newEnd) := by
      intro x
      rw [coveredBy_push]
      simpa [hins] using coverage x
    have hcov2 := coverage_push_step intervals (newStart, newEnd) (curStart, curEnd)
      (result.push (curStart, curEnd)) true i scanning
      (fun x => by simpa using hcov1 x)
    simpa using hcov2
  case inserted_pending =>
    rename_i intervals newStart newEnd
    intro _
    apply witness_survives_push (result.push (curStart, curEnd)) intervals[i]!
      (curStart, curEnd)
    exact ⟨result.size, by simp, getElem!_push_eq' result (curStart, curEnd)⟩
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    exact unchanged_result_before_next intervals (newStart, newEnd) result i scanning
      (result_before_next scanning) hnext canonical_input
  case coverage =>
    rename_i intervals newStart newEnd
    have hins : inserted = false := by cases inserted <;> simp_all
    have hm : ∀ x, memInterval x (curStart, curEnd) ∨ memInterval x intervals[i]! ↔
        memInterval x (intervals[i]!.1, intervals[i]!.2) := by
      intro x
      have hu := memInterval_union_overlap x (curStart, curEnd) intervals[i]!
        pending_wf (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
        pending_before before_pending
      simpa [min_eq_right (le_of_lt extend_left), max_eq_right (le_of_lt extend_right)] using hu
    have hc := coverage_merge_step intervals (newStart, newEnd) (curStart, curEnd)
      (intervals[i]!.1, intervals[i]!.2) result i scanning
      (fun x => by simpa [hins] using coverage x) hm
    simpa [hins] using hc
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    exact unchanged_result_before_next intervals (newStart, newEnd) result i scanning
      (result_before_next scanning) hnext canonical_input
  case coverage =>
    rename_i intervals newStart newEnd
    have hins : inserted = false := by cases inserted <;> simp_all
    have hm : ∀ x, memInterval x (curStart, curEnd) ∨ memInterval x intervals[i]! ↔
        memInterval x (intervals[i]!.1, curEnd) := by
      intro x
      have hu := memInterval_union_overlap x (curStart, curEnd) intervals[i]!
        pending_wf (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
        pending_before before_pending
      simpa [min_eq_right (le_of_lt extend_left), max_eq_left (le_of_not_gt extend_right)] using hu
    have hc := coverage_merge_step intervals (newStart, newEnd) (curStart, curEnd)
      (intervals[i]!.1, curEnd) result i scanning
      (fun x => by simpa [hins] using coverage x) hm
    simpa [hins] using hc
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    exact unchanged_result_before_next intervals (newStart, newEnd) result i scanning
      (result_before_next scanning) hnext canonical_input
  case coverage =>
    rename_i intervals newStart newEnd
    have hins : inserted = false := by cases inserted <;> simp_all
    have hm : ∀ x, memInterval x (curStart, curEnd) ∨ memInterval x intervals[i]! ↔
        memInterval x (curStart, intervals[i]!.2) := by
      intro x
      have hu := memInterval_union_overlap x (curStart, curEnd) intervals[i]!
        pending_wf (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
        pending_before before_pending
      simpa [min_eq_left (le_of_not_gt extend_left), max_eq_right (le_of_lt extend_right)] using hu
    have hc := coverage_merge_step intervals (newStart, newEnd) (curStart, curEnd)
      (curStart, intervals[i]!.2) result i scanning
      (fun x => by simpa [hins] using coverage x) hm
    simpa [hins] using hc
  case result_before_next =>
    rename_i intervals newStart newEnd
    intro hnext
    exact unchanged_result_before_next intervals (newStart, newEnd) result i scanning
      (result_before_next scanning) hnext canonical_input
  case coverage =>
    rename_i intervals newStart newEnd
    have hins : inserted = false := by cases inserted <;> simp_all
    have hm : ∀ x, memInterval x (curStart, curEnd) ∨ memInterval x intervals[i]! ↔
        memInterval x (curStart, curEnd) := by
      intro x
      have hu := memInterval_union_overlap x (curStart, curEnd) intervals[i]!
        pending_wf (canonical_input_wf intervals (newStart, newEnd) canonical_input i scanning)
        pending_before before_pending
      simpa [min_eq_left (le_of_not_gt extend_left), max_eq_left (le_of_not_gt extend_right)] using hu
    have hc := coverage_merge_step intervals (newStart, newEnd) (curStart, curEnd)
      (curStart, curEnd) result i scanning
      (fun x => by simpa [hins] using coverage x) hm
    simpa [hins] using hc

end Proof

end InsertInterval
