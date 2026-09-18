module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Order.Basic

/-!
## Program description

Merge overlapping or touching closed intervals from an input already sorted
lexicographically. The output is sorted, strictly separated, and has identical
point coverage. The program is expected to run in O(n) time and O(n) extra
space for the result.
-/

namespace MergeIntervals

section Specs

public abbrev Interval := Int × Int

public def istart (iv : Interval) : Int := iv.1

public def iend (iv : Interval) : Int := iv.2

public def InInterval (x : Int) (iv : Interval) : Prop :=
  istart iv ≤ x ∧ x ≤ iend iv

public def LexSortedIntervals (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size →
    (istart a[i]! < istart a[i + 1]!) ∨
    (istart a[i]! = istart a[i + 1]! ∧ iend a[i]! ≤ iend a[i + 1]!) ∨
    (istart a[i]! = istart a[i + 1]! ∧ iend a[i]! = iend a[i + 1]!)

public def AllValid (a : Array Interval) : Prop :=
  ∀ i, i < a.size → istart a[i]! ≤ iend a[i]!

public def StrictlyNonOverlapping (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size → iend a[i]! < istart a[i + 1]!

public def NondecreasingStarts (a : Array Interval) : Prop :=
  ∀ i, i + 1 < a.size → istart a[i]! ≤ istart a[i + 1]!

public def CoveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ i, i < a.size ∧ InInterval x a[i]!

public def IntervalIsTight (input : Array Interval) (iv : Interval) : Prop :=
  CoveredBy (istart iv) input ∧
  CoveredBy (iend iv) input ∧
  (∀ x, istart iv ≤ x ∧ x ≤ iend iv → CoveredBy x input)

public def precondition (intervals : Array Interval) : Prop :=
  AllValid intervals ∧ LexSortedIntervals intervals

public def postcondition (intervals result : Array Interval) : Prop :=
  AllValid result ∧
  NondecreasingStarts result ∧
  StrictlyNonOverlapping result ∧
  (∀ x, CoveredBy x result ↔ CoveredBy x intervals) ∧
  (∀ i, i < result.size → IntervalIsTight intervals result[i]!)

end Specs

section Implementation

public def mergeStep (acc : Array Interval) (iv : Interval) : Array Interval :=
  if acc.size = 0 then acc.push iv
  else
    let k := acc.size - 1
    let last := acc[k]!
    if iv.1 ≤ last.2 then acc.set! k (last.1, max last.2 iv.2)
    else acc.push iv

public def CoveredByPrefix (x : Int) (intervals : Array Interval) (n : Nat) : Prop :=
  ∃ j, j < n ∧ j < intervals.size ∧ InInterval x intervals[j]!

public def StartsFromPrefix (intervals result : Array Interval) (n : Nat) : Prop :=
  ∀ k, k < result.size →
    ∃ j, j < n ∧ j < intervals.size ∧ istart result[k]! = istart intervals[j]!

public def MergeInvariant (intervals : Array Interval) (n : Nat)
    (result : Array Interval) : Prop :=
  n ≤ intervals.size ∧
  AllValid result ∧
  NondecreasingStarts result ∧
  StrictlyNonOverlapping result ∧
  (∀ x, CoveredBy x result ↔ CoveredByPrefix x intervals n) ∧
  StartsFromPrefix intervals result n

method mergeIntervals (intervals : Array Interval)
  returns (result : Array Interval)
  requires valid_sorted: precondition intervals
  ensures merged: postcondition intervals result
do
  let mut i : Nat := 0
  let mut result : Array Interval := #[]
  while' scanning: i < intervals.size
    invariant merged_prefix: MergeInvariant intervals i result
    decreasing remaining: intervals.size - i
  do
    result := mergeStep result intervals[i]!
    i := i + 1
  return result

end Implementation

section Proof

-- Proofs of the semantic loop invariant and the final specification live here.
theorem starts_le_of_lt (a : Array Interval) (h : LexSortedIntervals a)
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

theorem coveredByPrefix_succ (intervals : Array Interval) (i : Nat) (hi : i < intervals.size)
    (x : Int) :
    CoveredByPrefix x intervals (i + 1) ↔
      CoveredByPrefix x intervals i ∨ InInterval x intervals[i]! := by
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

theorem covered_push (a : Array Interval) (iv : Interval) (x : Int) :
    CoveredBy x (a.push iv) ↔ CoveredBy x a ∨ InInterval x iv := by
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

theorem covered_setLast_merge (a : Array Interval) (iv : Interval)
    (hne : a.size ≠ 0) (hstart : istart a[a.size - 1]! ≤ istart iv)
    (hoverlap : istart iv ≤ iend a[a.size - 1]!) (x : Int) :
    CoveredBy x
        (a.set! (a.size - 1) (istart a[a.size - 1]!, max (iend a[a.size - 1]!) (iend iv))) ↔
      CoveredBy x a ∨ InInterval x iv := by
  let k := a.size - 1
  have hk : k < a.size := by
    dsimp [k]
    omega
  let merged : Interval := (istart a[k]!, max (iend a[k]!) (iend iv))
  have hlast : InInterval x a[k]! → InInterval x merged := by
    rintro ⟨hlo, hhi⟩
    exact ⟨hlo, hhi.trans (le_max_left _ _)⟩
  have hiv : InInterval x iv → InInterval x merged := by
    rintro ⟨hlo, hhi⟩
    exact ⟨hstart.trans hlo, hhi.trans (le_max_right _ _)⟩
  have hsplit : InInterval x merged → InInterval x a[k]! ∨ InInterval x iv := by
    rintro ⟨hlo, hhi⟩
    simp [merged, iend] at hhi
    by_cases hxle : x ≤ iend a[k]!
    · exact Or.inl ⟨hlo, hxle⟩
    · refine Or.inr ⟨hoverlap.trans (le_of_not_ge hxle), ?_⟩
      rcases hhi with hleft | hright
      · exact False.elim (hxle hleft)
      · exact hright
  change CoveredBy x (a.set! k merged) ↔ _
  constructor
  · rintro ⟨j, hj, hx⟩
    by_cases hjk : j = k
    · subst j
      unfold InInterval istart iend at hx ⊢
      have hm : InInterval x merged := by
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
        unfold InInterval istart iend at hx ⊢
        rw [Array.getElem!_set!_self _ _ _ hk]
        exact hlast hx
      · rw [getElem!_set!_ne' a k j merged hjk]
        exact hx
    · refine ⟨k, by simpa [Array.size_set!] using hk, ?_⟩
      unfold InInterval istart iend at hx ⊢
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
    (hvalid : AllValid a) (he : iend a[a.size - 1]! ≤ e) :
    AllValid (a.set! (a.size - 1) (istart a[a.size - 1]!, e)) := by
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
    (h : NondecreasingStarts a) :
    NondecreasingStarts (a.set! (a.size - 1) (istart a[a.size - 1]!, e)) := by
  intro j hj
  have hjo : j + 1 < a.size := by simpa [Array.size_set!] using hj
  rw [setLastEnd_start_eq a e j hne, setLastEnd_start_eq a e (j + 1) hne]
  exact h j hjo

theorem setLastEnd_separated (a : Array Interval) (e : Int) (hne : a.size ≠ 0)
    (h : StrictlyNonOverlapping a) :
    StrictlyNonOverlapping (a.set! (a.size - 1) (istart a[a.size - 1]!, e)) := by
  intro j hj
  have hjo : j + 1 < a.size := by simpa [Array.size_set!] using hj
  have hjk : j ≠ a.size - 1 := by omega
  unfold iend
  rw [getElem!_set!_ne' a (a.size - 1) j _ hjk]
  change iend a[j]! < istart _
  rw [setLastEnd_start_eq a e (j + 1) hne]
  exact h j hjo

theorem mergeInvariant_step (intervals : Array Interval) (i : Nat)
    (result : Array Interval) (hpre : precondition intervals)
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
      simpa [AllValid, getElem!_pos, hi] using hpre.1 i hi
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
        · have : CoveredBy x (#[] : Array Interval) := (hcover x).2 ⟨j, hji, hjs, hx⟩
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
      exact starts_le_of_lt intervals hpre.2 hj hi
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
        have hc := covered_setLast_merge result intervals[i]! hempty hlast_start hoverlap x
        have hp := coveredByPrefix_succ intervals i hi x
        simpa [k, istart, iend] using (hc.trans ((or_congr (hcover x) Iff.rfl).trans hp.symm))
      · intro q hq
        have hqo : q < result.size := by simpa [Array.size_set!] using hq
        rcases horigin q hqo with ⟨t, ht, hts, heq⟩
        refine ⟨t, by omega, hts, ?_⟩
        simpa [k, istart, iend] using
          (setLastEnd_start_eq result (max (iend result[k]!) (iend intervals[i]!)) q hempty).trans heq
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
        exact (covered_push result intervals[i]! x).trans
          ((or_congr (hcover x) Iff.rfl).trans (coveredByPrefix_succ intervals i hi x).symm)
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

theorem coveredByPrefix_full (intervals : Array Interval) (x : Int) :
    CoveredByPrefix x intervals intervals.size ↔ CoveredBy x intervals := by
  constructor
  · rintro ⟨j, _, hj, hx⟩
    exact ⟨j, hj, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, hj, hj, hx⟩

theorem tight_of_valid_coverage (input result : Array Interval)
    (hvalid : AllValid result)
    (hcover : ∀ x, CoveredBy x result ↔ CoveredBy x input)
    {i : Nat} (hi : i < result.size) : IntervalIsTight input result[i]! := by
  have hv := hvalid i hi
  refine ⟨?_, ?_, ?_⟩
  · apply (hcover (istart result[i]!)).1
    exact ⟨i, hi, le_rfl, hv⟩
  · apply (hcover (iend result[i]!)).1
    exact ⟨i, hi, hv, le_rfl⟩
  · intro x hx
    apply (hcover x).1
    exact ⟨i, hi, hx⟩

prove_correct mergeIntervals by
  velvet_vcgen [mergeIntervals] with try finish
  case merged_prefix =>
    simp [MergeInvariant, AllValid, NondecreasingStarts, StrictlyNonOverlapping,
      CoveredBy, CoveredByPrefix, StartsFromPrefix]
  case merged =>
    rename_i intervals
    rcases merged_prefix with ⟨hi, hvalid, hstarts, hsep, hcover, horigin⟩
    have hieq : i = intervals.size := by omega
    subst i
    have hcover_full : ∀ x, CoveredBy x result ↔ CoveredBy x intervals := by
      intro x
      exact (hcover x).trans (coveredByPrefix_full intervals x)
    exact ⟨hvalid, hstarts, hsep, hcover_full,
      fun _ hk => tight_of_valid_coverage intervals result hvalid hcover_full hk⟩
  case merged_prefix => exact mergeInvariant_step _ _ _ valid_sorted merged_prefix scanning

end Proof

end MergeIntervals
