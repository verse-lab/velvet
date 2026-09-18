module

public import Velvet
public meta import Velvet
public import Mathlib.Data.List.Basic

/-!
## Program description

Partition a character sequence into as many contiguous parts as possible so that
each character appears in at most one part; return the sizes of the parts.

The program is expected to run in O(n²) time and O(n) extra space. It accepts
an array directly, builds a last-occurrence association list, and then uses the
standard greedy boundary scan. Association-list updates and lookups take linear
time in the number of distinct characters.
-/

namespace PartitionLabels

section Specs

public def partStarts (sizes : List Nat) : List Nat :=
  sizes.scanl (fun acc x => acc + x) 0

public def totalSize (sizes : List Nat) : Nat :=
  sizes.foldl (fun acc x => acc + x) 0

public def InPart (sizes : List Nat) (k : Nat) (i : Nat) : Prop :=
  let b := partStarts sizes
  (b[k]?).isSome ∧
  (b[k + 1]?).isSome ∧
  (b[k]?).getD 0 ≤ i ∧
  i < (b[k + 1]?).getD 0

public def isValidPartition (s : Array Char) (sizes : List Nat) : Prop :=
  totalSize sizes = s.size ∧
  (∀ x : Nat, x ∈ sizes → x > 0) ∧
  (∀ (i : Nat) (j : Nat),
      i < s.size → j < s.size → s[i]! = s[j]! →
        ∃ k : Nat, InPart sizes k i ∧ InPart sizes k j)

public def isMaxParts (s : Array Char) (sizes : List Nat) : Prop :=
  isValidPartition s sizes ∧
  (∀ sizes2 : List Nat, isValidPartition s sizes2 → sizes2.length ≤ sizes.length)

public def precondition (_s : Array Char) : Prop :=
  True

public def postcondition (s : Array Char) (result : List Nat) : Prop :=
  isMaxParts s result

end Specs

section Implementation

public def isValidPartitionArray (s : Array Char) (sizes : List Nat) : Prop :=
  isValidPartition s sizes

public def isMaxPartsArray (s : Array Char) (sizes : List Nat) : Prop :=
  isMaxParts s sizes

public def arrayPostcondition (s : Array Char) (result : List Nat) : Prop :=
  postcondition s result

public def isCutPointBool (s : Array Char) (p : Nat) : Bool :=
  (List.range p).all fun x =>
    (List.range (s.size - p)).all fun y_offset =>
      s[x]! != s[p + y_offset]!

public def nextCutGo (s : Array Char) (p : Nat) : Nat :=
  if p < s.size then
    if isCutPointBool s p then
      p
    else
      nextCutGo s (p + 1)
  else
    s.size
termination_by s.size - p

public def nextCut (s : Array Char) (start : Nat) : Nat :=
  nextCutGo s (start + 1)

public def buildParts (s : Array Char) (start : Nat) : List Nat :=
  if start < s.size then
    let nxt := nextCut s start
    if nxt > start then
      (nxt - start) :: buildParts s nxt
    else
      [s.size - start]
  else
    []
termination_by s.size - start

public def setLast : List (Char × Nat) → Char → Nat → List (Char × Nat)
  | [], c, i => [(c, i)]
  | (d, v) :: rest, c, i =>
      if d = c then (d, i) :: rest else (d, v) :: setLast rest c i

public def updateRun : List (Char × Nat) → List (Char × Nat) → Bool → Char → Nat → List (Char × Nat)
  | accRev, [], found, c, i =>
      if found then accRev.reverse else (c, i) :: accRev.reverse
  | accRev, (d, v) :: rest, found, c, i =>
      if d = c then updateRun ((d, i) :: accRev) rest true c i
      else updateRun ((d, v) :: accRev) rest found c i

public def updateAll (m : List (Char × Nat)) (c : Char) (i : Nat) : List (Char × Nat) :=
  updateRun [] m false c i

public def lookupRun : List (Char × Nat) → Char → Nat → Nat
  | [], _, value => value
  | (d, v) :: rest, c, value => if d = c then v else lookupRun rest c value

public def getLast (m : List (Char × Nat)) (c : Char) (fallback : Nat) : Nat :=
  lookupRun m c fallback

public def lastMapPrefix (a : Array Char) (i : Nat) : List (Char × Nat) :=
  (List.range i).foldl (fun m j => updateAll m a[j]! j) []

public def greedyRun (a : Array Char) (m : List (Char × Nat))
    (j start endIdx : Nat) (resRev : List Nat) : List Nat :=
  if h : j < a.size then
    let lastJ := getLast m a[j]! j
    let newEnd := Nat.max endIdx lastJ
    if j = newEnd then
      greedyRun a m (j + 1) (j + 1) (j + 1)
        ((newEnd + 1 - start) :: resRev)
    else
      greedyRun a m (j + 1) start newEnd resRev
  else
    resRev.reverse
termination_by a.size - j

method partitionLabels (s : Array Char)
  returns (result : List Nat)
  requires valid: precondition s
  ensures max_parts: postcondition s result
do
  let a := s
  if a.isEmpty then
    return []

  let mut lastMap : List (Char × Nat) := []
  let mut i : Nat := 0
  while building_last: i < a.size
    invariant build_bounds: i ≤ a.size
    invariant build_model: lastMap = lastMapPrefix a i
    decreasing build_remaining: a.size - i
  do
    let c := a[i]!
    let mut found : Bool := false
    let mut accRev : List (Char × Nat) := []
    let mut rest := lastMap
    while updating_entry: rest ≠ []
      invariant update_rest_bound: rest.length ≤ lastMap.length
      invariant update_acc_bound: accRev.length ≤ lastMap.length
      invariant update_partition: accRev.length + rest.length = lastMap.length
      invariant update_model: updateRun accRev rest found c i = updateAll lastMap c i
      decreasing update_remaining: rest.length
    do
      match rest with
      | [] => rest := []
      | (d, v) :: rs =>
        if same_char: d = c then
          accRev := (d, i) :: accRev
          found := true
        else
          accRev := (d, v) :: accRev
        rest := rs
    if was_found: found then
      lastMap := accRev.reverse
    else
      lastMap := (c, i) :: accRev.reverse
    i := i + 1

  let mut resRev : List Nat := []
  let mut start : Nat := 0
  let mut endIdx : Nat := 0
  let mut j : Nat := 0
  while greedy_scan: j < a.size
    invariant scan_bounds: j ≤ a.size
    invariant scan_model:
      greedyRun a lastMap j start endIdx resRev = greedyRun a lastMap 0 0 0 []
    decreasing scan_remaining: a.size - j
  do
    let c := a[j]!
    let mut lastJ := j
    let mut entries := lastMap
    while lookup_last: entries ≠ []
      invariant lookup_bound: entries.length ≤ lastMap.length
      invariant lookup_model: lookupRun entries c lastJ = getLast lastMap c j
      decreasing lookup_remaining: entries.length
    do
      match entries with
      | [] => entries := []
      | (d, v) :: es =>
        if same_char: d = c then
          lastJ := v
          entries := []
        else
          entries := es
    if extends_end: lastJ > endIdx then
      endIdx := lastJ
    if closes: j = endIdx then
      resRev := (endIdx + 1 - start) :: resRev
      start := j + 1
      endIdx := start
    j := j + 1
  return resRev.reverse

end Implementation

section Proof

theorem foldl_add_eq (xs : List Nat) (init : Nat) :
    xs.foldl (fun acc x => acc + x) init = init + xs.sum := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [ih]
    omega

theorem totalSize_eq_sum (xs : List Nat) : totalSize xs = xs.sum := by
  unfold totalSize
  rw [foldl_add_eq]
  omega

theorem empty_of_positive_sum_zero (xs : List Nat) (hsum : xs.sum = 0) (hpos : ∀ x ∈ xs, x > 0) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hy : y > 0 := hpos y (by simp)
    have : (y :: ys).sum ≥ y := by simp
    omega

theorem scanl_add_getElem? (xs : List Nat) (init : Nat) (k : Nat) :
    k ≤ xs.length → (xs.scanl (fun acc x => acc + x) init)[k]? = some (init + (xs.take k).sum) := by
  induction xs generalizing init k with
  | nil =>
    intro hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst this
    simp
  | cons x xs ih =>
    intro hk
    cases k with
    | zero =>
      simp
    | succ k' =>
      have hk' : k' ≤ xs.length := by
        have : k' + 1 ≤ xs.length + 1 := hk
        omega
      have ih' := ih (init := init + x) (k := k') hk'
      simp only [List.scanl_cons, List.getElem?_cons_succ]
      rw [ih']
      simp [List.take]
      omega

theorem length_partStarts (xs : List Nat) : (partStarts xs).length = xs.length + 1 := by
  unfold partStarts
  simp

theorem getElem?_partStarts (xs : List Nat) (k : Nat) (hk : k ≤ xs.length) :
    (partStarts xs)[k]? = some (xs.take k).sum := by
  unfold partStarts
  have h := scanl_add_getElem? xs 0 k hk
  simpa using h

theorem list_getElem?_isSome {α : Type} (l : List α) (idx : Nat) : (l[idx]?).isSome ↔ idx < l.length := by
  constructor
  · intro h
    cases hget : l[idx]? with
    | none => simp [hget] at h
    | some x =>
      rw [List.getElem?_eq_some_iff] at hget
      exact hget.1
  · intro h
    rw [List.getElem?_eq_getElem h]
    rfl

theorem inPart_iff (sizes : List Nat) (k i : Nat) :
    InPart sizes k i ↔ k < sizes.length ∧ (sizes.take k).sum ≤ i ∧ i < (sizes.take (k + 1)).sum := by
  unfold InPart
  have hlen := length_partStarts sizes
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [list_getElem?_isSome] at h1 h2
    rw [hlen] at h1 h2
    have hk : k < sizes.length := by omega
    have hget1 := getElem?_partStarts sizes k (by omega)
    have hget2 := getElem?_partStarts sizes (k + 1) (by omega)
    rw [hget1] at h3
    rw [hget2] at h4
    simp only [Option.getD_some] at h3 h4
    exact ⟨hk, h3, h4⟩
  · rintro ⟨hk, h1, h2⟩
    have hget1 := getElem?_partStarts sizes k (by omega)
    have hget2 := getElem?_partStarts sizes (k + 1) (by omega)
    refine ⟨by rw [list_getElem?_isSome, hlen]; omega,
            by rw [list_getElem?_isSome, hlen]; omega, ?_, ?_⟩
    · rw [hget1]
      simp [h1]
    · rw [hget2]
      simp [h2]

public def isCutPoint (s : Array Char) (p : Nat) : Prop :=
  p ≤ s.size ∧ ∀ (x : Nat) (y : Nat), x < p → p ≤ y → y < s.size → s[x]! ≠ s[y]!

theorem isCutPoint_zero (s : Array Char) : isCutPoint s 0 := by
  refine ⟨Nat.zero_le _, fun x _ hx => (Nat.not_lt_zero x hx).elim⟩

theorem isCutPoint_length (s : Array Char) : isCutPoint s s.size := by
  refine ⟨Nat.le_refl _, fun _ y _ hy hy_lt => (by omega)⟩

theorem isCutPointBool_eq (s : Array Char) (p : Nat) (hp : p ≤ s.size) :
    isCutPointBool s p = true ↔ isCutPoint s p := by
  unfold isCutPointBool isCutPoint
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne]
  constructor
  · intro h
    refine ⟨hp, ?_⟩
    intro x y hx hpy hy
    have hy_off : y - p < s.size - p := by omega
    have hx_range : x < p := hx
    have h_all := h x hx_range (y - p) hy_off
    have hy_eq : p + (y - p) = y := by omega
    rwa [hy_eq] at h_all
  · intro ⟨_, h⟩ x hx y_off hy_off
    have hy : p + y_off < s.size := by omega
    exact h x (p + y_off) hx (by omega) hy

theorem nextCutGo_ge (s : Array Char) (p : Nat) (hp : p ≤ s.size) : nextCutGo s p ≥ p := by
  fun_induction nextCutGo s p
  case case1 p h hcut =>
    exact Nat.le_refl _
  case case2 p h hcut ih =>
    exact Nat.le_trans (by omega) (ih (by omega))
  case case3 p h =>
    omega

theorem nextCutGo_le (s : Array Char) (p : Nat) : nextCutGo s p ≤ s.size := by
  fun_induction nextCutGo s p
  case case1 p h hcut =>
    omega
  case case2 p h hcut ih =>
    exact ih
  case case3 p h =>
    omega

theorem nextCut_gt (s : Array Char) (start : Nat) (h : start < s.size) : nextCut s start ≥ start + 1 := by
  unfold nextCut
  exact nextCutGo_ge s (start + 1) (by omega)

theorem nextCut_le (s : Array Char) (start : Nat) : nextCut s start ≤ s.size := by
  unfold nextCut
  exact nextCutGo_le s (start + 1)

theorem nextCutGo_isCutPoint (s : Array Char) (p : Nat) : isCutPoint s (nextCutGo s p) := by
  fun_induction nextCutGo s p
  case case1 p h hcut =>
    have hp : p ≤ s.size := by omega
    rw [← isCutPointBool_eq s p hp]
    exact hcut
  case case2 p h hcut ih =>
    exact ih
  case case3 p h =>
    exact isCutPoint_length s

theorem nextCut_isCutPoint (s : Array Char) (start : Nat) : isCutPoint s (nextCut s start) := by
  unfold nextCut
  exact nextCutGo_isCutPoint s (start + 1)

theorem nextCutGo_min (s : Array Char) (p q : Nat) (hq : isCutPoint s q) (hpq : p ≤ q) :
    nextCutGo s p ≤ q := by
  fun_induction nextCutGo s p
  case case1 p h hcut =>
    exact hpq
  case case2 p h hcut ih =>
    have hp : p ≤ s.size := by omega
    have hnot_cut : ¬ isCutPoint s p := by
      rw [← isCutPointBool_eq s p hp]
      intro h
      simp [h] at hcut
    have hp_ne_q : p ≠ q := by
      rintro rfl
      exact hnot_cut hq
    have hp_lt_q : p < q := by omega
    have hp1_le_q : p + 1 ≤ q := by omega
    exact ih hp1_le_q
  case case3 p h =>
    have : q ≤ s.size := hq.1
    omega

theorem nextCut_min (s : Array Char) (start q : Nat) (hq : isCutPoint s q) (hgt : start < q) :
    nextCut s start ≤ q := by
  unfold nextCut
  exact nextCutGo_min s (start + 1) q hq hgt

theorem buildParts_pos (s : Array Char) (start : Nat) :
    ∀ x ∈ buildParts s start, x > 0 := by
  fun_induction buildParts s start
  case case1 start h nxt hadv ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact ih x hx
  case case2 start h nxt hadv =>
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    omega
  case case3 start h =>
    intro x hx
    simp at hx

theorem buildParts_sum (s : Array Char) (start : Nat) (hstart : start ≤ s.size) :
    (buildParts s start).sum = s.size - start := by
  fun_induction buildParts s start
  case case1 start h nxt hadv ih =>
    have hnxt_le : nxt ≤ s.size := nextCut_le s start
    have ih' := ih hnxt_le
    simp only [List.sum_cons, ih']
    omega
  case case2 start h nxt hadv =>
    have hgt : nextCut s start ≥ start + 1 := nextCut_gt s start h
    omega
  case case3 start h =>
    simp
    omega

theorem buildParts_eq_cons (s : Array Char) (start : Nat) (h : start < s.size) :
    buildParts s start = (nextCut s start - start) :: buildParts s (nextCut s start) := by
  rw [buildParts.eq_def]
  have hgt := nextCut_gt s start h
  have hadv : nextCut s start > start := by omega
  simp [h, hadv]

theorem buildParts_take_cutPoint (s : Array Char) (start : Nat) (hstart : isCutPoint s start) (k : Nat)
    (hk : k ≤ (buildParts s start).length) :
    isCutPoint s (((buildParts s start).take k).sum + start) := by
  induction k generalizing start with
  | zero =>
    simp [hstart]
  | succ k ih =>
    by_cases h_lt : start < s.size
    · rw [buildParts_eq_cons s start h_lt] at hk ⊢
      simp only [List.length_cons] at hk
      have hk' : k ≤ (buildParts s (nextCut s start)).length := by omega
      simp only [List.take_succ_cons, List.sum_cons]
      have hnxt_cut : isCutPoint s (nextCut s start) := nextCut_isCutPoint s start
      have ih' := ih (nextCut s start) hnxt_cut hk'
      have hgt : nextCut s start ≥ start + 1 := nextCut_gt s start h_lt
      have heq : nextCut s start - start + ((buildParts s (nextCut s start)).take k).sum + start =
                 ((buildParts s (nextCut s start)).take k).sum + nextCut s start := by omega
      rw [heq]
      exact ih'
    · have : buildParts s start = [] := by
        rw [buildParts.eq_def]
        simp [h_lt]
      rw [this] at hk
      simp at hk

theorem buildParts_take_succ_sum (s : Array Char) (start : Nat) (k : Nat)
    (hk : k < (buildParts s start).length) :
    ((buildParts s start).take (k + 1)).sum + start =
      nextCut s (((buildParts s start).take k).sum + start) := by
  induction k generalizing start with
  | zero =>
    by_cases h_lt : start < s.size
    · rw [buildParts_eq_cons s start h_lt]
      simp [List.take]
      have hgt : nextCut s start ≥ start + 1 := nextCut_gt s start h_lt
      omega
    · have : buildParts s start = [] := by
        rw [buildParts.eq_def]
        simp [h_lt]
      rw [this] at hk
      simp at hk
  | succ k ih =>
    by_cases h_lt : start < s.size
    · rw [buildParts_eq_cons s start h_lt] at hk ⊢
      simp only [List.length_cons] at hk
      have hk' : k < (buildParts s (nextCut s start)).length := by omega
      simp only [List.take_succ_cons, List.sum_cons]
      have ih' := ih (nextCut s start) hk'
      have hgt : nextCut s start ≥ start + 1 := nextCut_gt s start h_lt
      have heq1 : nextCut s start - start + ((buildParts s (nextCut s start)).take (k + 1)).sum + start =
                  ((buildParts s (nextCut s start)).take (k + 1)).sum + nextCut s start := by omega
      have heq2 : nextCut s start - start + ((buildParts s (nextCut s start)).take k).sum + start =
                  ((buildParts s (nextCut s start)).take k).sum + nextCut s start := by omega
      rw [heq1, heq2]
      exact ih'
    · have : buildParts s start = [] := by
        rw [buildParts.eq_def]
        simp [h_lt]
      rw [this] at hk
      simp at hk

theorem exists_part_of_sum_gt (sizes : List Nat) (hpos : ∀ x ∈ sizes, x > 0) (i : Nat)
    (hi : i < sizes.sum) :
    ∃ k < sizes.length, (sizes.take k).sum ≤ i ∧ i < (sizes.take (k + 1)).sum := by
  induction sizes generalizing i with
  | nil =>
    simp at hi
  | cons x xs ih =>
    have hx_pos : x > 0 := hpos x (by simp)
    have hxs_pos : ∀ y ∈ xs, y > 0 := fun y hy => hpos y (List.mem_cons_of_mem x hy)
    by_cases hix : i < x
    · refine ⟨0, by simp, by simp, by simp [List.take, hix]⟩
    · have hle : x ≤ i := by omega
      have hi' : i - x < xs.sum := by
        simp only [List.sum_cons] at hi
        omega
      rcases ih hxs_pos (i - x) hi' with ⟨k', hk'_len, hk'_le, hk'_lt⟩
      refine ⟨k' + 1, by simp [hk'_len], ?_, ?_⟩
      · simp only [List.take_succ_cons, List.sum_cons]
        omega
      · simp only [List.take_succ_cons, List.sum_cons]
        omega

theorem buildParts_valid (s : Array Char) : isValidPartitionArray s (buildParts s 0) := by
  have htot : totalSize (buildParts s 0) = s.size := by
    rw [totalSize_eq_sum, buildParts_sum s 0 (Nat.zero_le _)]
    omega
  have hpos : ∀ x ∈ buildParts s 0, x > 0 := buildParts_pos s 0
  refine ⟨htot, hpos, ?_⟩
  intro i j hi hj heq
  have hsum_eq : (buildParts s 0).sum = s.size := by
    rw [← totalSize_eq_sum]
    exact htot
  have hi_sum : i < (buildParts s 0).sum := by omega
  rcases exists_part_of_sum_gt (buildParts s 0) hpos i hi_sum with ⟨k, hk_len, hki1, hki2⟩
  have hcut_k : isCutPoint s ((buildParts s 0).take k).sum := by
    have := buildParts_take_cutPoint s 0 (isCutPoint_zero s) k (by omega)
    simpa using this
  have hcut_k1 : isCutPoint s ((buildParts s 0).take (k + 1)).sum := by
    have := buildParts_take_cutPoint s 0 (isCutPoint_zero s) (k + 1) (by omega)
    simpa using this
  have hj1 : ((buildParts s 0).take k).sum ≤ j := by
    by_contra hlt
    have hlt' : j < ((buildParts s 0).take k).sum := by omega
    have hne := hcut_k.2 j i hlt' hki1 hi
    exact hne heq.symm
  have hj2 : j < ((buildParts s 0).take (k + 1)).sum := by
    by_contra hge
    have hge' : ((buildParts s 0).take (k + 1)).sum ≤ j := by omega
    have hne := hcut_k1.2 i j hki2 hge' hj
    exact hne heq
  refine ⟨k, ?_, ?_⟩
  · rw [inPart_iff]
    exact ⟨hk_len, hki1, hki2⟩
  · rw [inPart_iff]
    exact ⟨hk_len, hj1, hj2⟩

theorem sum_take_le_sum_take (xs : List Nat) (a b : Nat) (hab : a ≤ b) :
    (xs.take a).sum ≤ (xs.take b).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => omega
      | succ b' =>
        simp only [List.take_succ_cons, List.sum_cons]
        have ih' := ih a' b' (by omega)
        omega

theorem cutPoint_of_validPartition (s : Array Char) (sizes : List Nat)
    (hvalid : isValidPartitionArray s sizes) (r : Nat) (hr : r ≤ sizes.length) :
    isCutPoint s (sizes.take r).sum := by
  unfold isCutPoint
  rcases hvalid with ⟨htot, _, hchar⟩
  rw [totalSize_eq_sum] at htot
  have hsum_le : (sizes.take r).sum ≤ s.size := by
    have := sum_take_le_sum_take sizes r sizes.length hr
    rw [List.take_length] at this
    omega
  refine ⟨hsum_le, ?_⟩
  intro x y hx hy hy_len h_eq
  rcases hchar x y (by omega) hy_len h_eq with ⟨k, hpart_x, hpart_y⟩
  rw [inPart_iff] at hpart_x hpart_y
  rcases hpart_x with ⟨hk_len, hx1, hx2⟩
  rcases hpart_y with ⟨-, hy1, hy2⟩
  by_cases hkr : k < r
  · have htake : (sizes.take (k + 1)).sum ≤ (sizes.take r).sum :=
      sum_take_le_sum_take sizes (k + 1) r (by omega)
    omega
  · have htake : (sizes.take r).sum ≤ (sizes.take k).sum :=
      sum_take_le_sum_take sizes r k (by omega)
    omega

theorem sum_take_succ_gt (xs : List Nat) (r : Nat) (hr : r < xs.length)
    (hpos : ∀ x ∈ xs, x > 0) :
    (xs.take (r + 1)).sum > (xs.take r).sum := by
  induction xs generalizing r with
  | nil =>
    simp at hr
  | cons x xs ih =>
    cases r with
    | zero =>
      have hx : x > 0 := hpos x (by simp)
      simp [hx]
    | succ r' =>
      simp only [List.length_cons] at hr
      have hr' : r' < xs.length := by omega
      have hxs_pos : ∀ y ∈ xs, y > 0 := fun y hy => hpos y (List.mem_cons_of_mem x hy)
      simp only [List.take_succ_cons, List.sum_cons]
      have ih' := ih r' hr' hxs_pos
      omega

theorem buildParts_maximal_le (s : Array Char) (sizes2 : List Nat)
    (hvalid2 : isValidPartitionArray s sizes2) (r : Nat) (hr : r ≤ sizes2.length) :
    r ≤ (buildParts s 0).length ∧ ((buildParts s 0).take r).sum ≤ (sizes2.take r).sum := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have hr_le : r ≤ sizes2.length := by omega
    rcases ih hr_le with ⟨hr_len, hcr_le⟩
    have hr_lt : r < sizes2.length := by omega
    have hbr_lt : (sizes2.take r).sum < (sizes2.take (r + 1)).sum :=
      sum_take_succ_gt sizes2 r hr_lt hvalid2.2.1
    have hbr1_le_len : (sizes2.take (r + 1)).sum ≤ s.size := by
      have := sum_take_le_sum_take sizes2 (r + 1) sizes2.length (by omega)
      rw [List.take_length] at this
      have htot := hvalid2.1
      rw [totalSize_eq_sum] at htot
      omega
    have hcr_lt : ((buildParts s 0).take r).sum < s.size := by omega
    have hr_strict : r < (buildParts s 0).length := by
      by_contra h_ge
      have heq : r = (buildParts s 0).length := by omega
      have hsum_all : ((buildParts s 0).take r).sum = s.size := by
        rw [heq, List.take_length, buildParts_sum s 0 (Nat.zero_le _)]
        omega
      omega
    have hr1_len : r + 1 ≤ (buildParts s 0).length := by omega
    have hsucc_sum := buildParts_take_succ_sum s 0 r hr_strict
    have heq0 : ((buildParts s 0).take (r + 1)).sum + 0 = ((buildParts s 0).take (r + 1)).sum := by omega
    have heq1 : ((buildParts s 0).take r).sum + 0 = ((buildParts s 0).take r).sum := by omega
    rw [heq0, heq1] at hsucc_sum
    have hcut_br1 : isCutPoint s (sizes2.take (r + 1)).sum :=
      cutPoint_of_validPartition s sizes2 hvalid2 (r + 1) (by omega)
    have hmin := nextCut_min s (((buildParts s 0).take r).sum) ((sizes2.take (r + 1)).sum)
      hcut_br1 (by omega)
    rw [hsucc_sum]
    exact ⟨hr1_len, hmin⟩

theorem buildParts_maximal (s : Array Char) (sizes2 : List Nat)
    (hvalid2 : isValidPartitionArray s sizes2) :
    sizes2.length ≤ (buildParts s 0).length := by
  have := buildParts_maximal_le s sizes2 hvalid2 sizes2.length (Nat.le_refl _)
  exact this.1

theorem partitionLabels_empty (s : Array Char) (hs : s.isEmpty = true) :
    arrayPostcondition s [] := by
  have hzero : s.size = 0 := by simpa using hs
  have hnil : s = #[] := Array.eq_empty_of_size_eq_zero hzero
  subst hnil
  unfold arrayPostcondition postcondition isMaxParts isValidPartition
  refine ⟨⟨rfl, by simp, fun i _ hi => by simp at hi⟩, ?_⟩
  intro sizes2 ⟨htot, hpos, _⟩
  rw [totalSize_eq_sum] at htot
  have : sizes2 = [] := empty_of_positive_sum_zero sizes2 htot hpos
  subst this
  exact Nat.le_refl _

theorem partitionLabels_correct (s : Array Char) :
    arrayPostcondition s (buildParts s 0) := by
  unfold arrayPostcondition postcondition isMaxParts
  exact ⟨buildParts_valid s, fun sizes2 hvalid2 => buildParts_maximal s sizes2 hvalid2⟩

theorem lastMapPrefix_zero (a : Array Char) : lastMapPrefix a 0 = [] := by
  simp [lastMapPrefix]

theorem lastMapPrefix_succ (a : Array Char) (i : Nat) :
    lastMapPrefix a (i + 1) = updateAll (lastMapPrefix a i) a[i]! i := by
  simp [lastMapPrefix, List.range_succ, List.foldl_append]

theorem lookupRun_append (l r : List (Char × Nat)) (c : Char) (fallback : Nat) :
    lookupRun (l ++ r) c fallback = lookupRun l c (lookupRun r c fallback) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rcases e with ⟨d, v⟩
    simp [lookupRun, ih]

theorem lookupRun_of_not_mem (l : List (Char × Nat)) (c : Char) (fallback : Nat)
    (h : c ∉ l.map Prod.fst) : lookupRun l c fallback = fallback := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rcases e with ⟨d, v⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [lookupRun]
    split
    · rename_i hdc
      exact (h.1 hdc.symm).elim
    · exact ih h.2

theorem updateRun_lookup (accRev rest : List (Char × Nat)) (found : Bool)
    (c d : Char) (i fallback : Nat)
    (hfound : found = true → ∀ fb, lookupRun accRev.reverse c fb = i)
    (hmissing : found = false → c ∉ accRev.map Prod.fst) :
    lookupRun (updateRun accRev rest found c i) d fallback =
      if d = c then i else lookupRun (accRev.reverse ++ rest) d fallback := by
  induction rest generalizing accRev found with
  | nil =>
    simp only [updateRun]
    split
    · rename_i hf
      by_cases hdc : d = c
      · subst d
        simp [hfound hf fallback]
      · simp [hdc]
    · rename_i hf
      by_cases hdc : d = c
      · subst d; simp [lookupRun]
      · have hcd : c ≠ d := Ne.symm hdc
        simp [lookupRun, hdc, hcd]
  | cons e rest ih =>
    rcases e with ⟨e, v⟩
    simp only [updateRun]
    split
    · subst e
      rw [ih (hfound := by
        intro _ fb
        rw [List.reverse_cons, lookupRun_append]
        by_cases hf : found = true
        · simp [hfound hf (lookupRun [(c, i)] c fb)]
        · have hf' : found = false := by cases found <;> simp_all
          have hn := hmissing hf'
          have hn' : c ∉ accRev.reverse.map Prod.fst := by simpa using hn
          rw [lookupRun_of_not_mem _ _ _ hn']
          simp [lookupRun]) (hmissing := by simp)]
      rw [lookupRun_append]
      by_cases hdc : d = c
      · subst d; simp
      · have hcd : c ≠ d := Ne.symm hdc
        simp [hdc, hcd, List.reverse_cons, lookupRun_append, lookupRun]
    · rw [ih (hfound := by
          intro hf fb
          rw [List.reverse_cons, lookupRun_append]
          have hec : e ≠ c := by assumption
          have htail : lookupRun [(e, v)] c fb = fb := by simp [lookupRun, hec]
          rw [htail]
          exact hfound hf fb) (hmissing := by
          intro hf
          have hn := hmissing hf
          have hec : e ≠ c := by assumption
          have hce : c ≠ e := Ne.symm hec
          simpa [hce] using hn)]
      simp [List.reverse_cons, lookupRun_append]

theorem getLast_updateAll (m : List (Char × Nat)) (c d : Char) (i fallback : Nat) :
    getLast (updateAll m c i) d fallback =
      if d = c then i else getLast m d fallback := by
  simpa [getLast, updateAll, lookupRun] using
    updateRun_lookup ([] : List (Char × Nat)) m false c d i fallback (by simp) (by simp)

public def lastValue (a : Array Char) (c : Char) (fallback i : Nat) : Nat :=
  (List.range i).foldl (fun v j => if a[j]! = c then j else v) fallback

theorem lastValue_succ (a : Array Char) (c : Char) (fallback i : Nat) :
    lastValue a c fallback (i + 1) =
      if a[i]! = c then i else lastValue a c fallback i := by
  simp [lastValue, List.range_succ, List.foldl_append]

theorem getLast_lastMapPrefix (a : Array Char) (i : Nat) (c : Char) (fallback : Nat) :
    getLast (lastMapPrefix a i) c fallback = lastValue a c fallback i := by
  induction i with
  | zero => simp [lastMapPrefix, lastValue, getLast, lookupRun]
  | succ i ih =>
    rw [show i + 1 = i + 1 by rfl, lastMapPrefix_succ, getLast_updateAll,
      lastValue_succ, ih]
    by_cases h : a[i]! = c
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · have hs : ¬c = a[i]! := fun heq => h heq.symm
      rw [ite_eq_right h, ite_eq_right hs]

theorem lastValue_ge_match (a : Array Char) (c : Char) (fallback i k : Nat)
    (hk : k < i) (hmatch : a[k]! = c) :
    k ≤ lastValue a c fallback i := by
  induction i generalizing k with
  | zero => omega
  | succ i ih =>
    rw [lastValue_succ]
    by_cases hi : a[i]! = c
    · simp [hi]
      omega
    · simp [hi]
      by_cases hki : k = i
      · subst k; exact (hi hmatch).elim
      · exact ih k (by omega) hmatch

theorem lastValue_le_max (a : Array Char) (c : Char) (fallback i : Nat) :
    lastValue a c fallback i ≤ max fallback (i - 1) := by
  induction i with
  | zero => simp [lastValue]
  | succ i ih =>
    rw [lastValue_succ]
    split
    · omega
    · exact Nat.le_trans ih (by omega)

theorem lastValue_lt (a : Array Char) (c : Char) (fallback i : Nat)
    (hf : fallback < i) : lastValue a c fallback i < i := by
  have := lastValue_le_max a c fallback i
  omega

theorem lastValue_match (a : Array Char) (c : Char) (fallback i : Nat)
    (hf : fallback < i) (hmatch : a[fallback]! = c) :
    a[lastValue a c fallback i]! = c := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [lastValue_succ]
    by_cases hi : a[i]! = c
    · rw [ite_eq_left hi]
      exact hi
    · rw [ite_eq_right hi]
      by_cases hf' : fallback < i
      · exact ih hf'
      · have heq : fallback = i := by omega
        subst fallback
        exact (hi hmatch).elim

theorem isCutPoint_iff_lastValue (a : Array Char) (p : Nat) :
    isCutPoint a p ↔
      p ≤ a.size ∧ ∀ x, x < p → lastValue a a[x]! x a.size < p := by
  constructor
  · rintro hcut
    refine ⟨hcut.1, ?_⟩
    intro x hx
    have hp : p ≤ a.size := hcut.1
    have hxs : x < a.size := by omega
    have hlast_lt_size := lastValue_lt a a[x]! x a.size hxs
    by_contra hge
    have hp_last : p ≤ lastValue a a[x]! x a.size := by omega
    have hne := hcut.2 x (lastValue a a[x]! x a.size) hx hp_last hlast_lt_size
    exact hne (lastValue_match a a[x]! x a.size hxs rfl).symm
  · rintro ⟨hp, hall⟩
    refine ⟨hp, ?_⟩
    intro x y hx hpy hy hxy
    have hlast_ge := lastValue_ge_match a a[x]! x a.size y hy hxy.symm
    have hlast_lt := hall x hx
    omega

public def scanInvariant (a : Array Char) (j start endIdx : Nat) (resRev : List Nat) : Prop :=
  start ≤ j ∧ j ≤ a.size ∧ isCutPoint a start ∧
  resRev.reverse ++ buildParts a start = buildParts a 0 ∧
  (∀ x, start ≤ x → x < j → lastValue a a[x]! x a.size ≤ endIdx) ∧
  (endIdx > start → ∃ x, start ≤ x ∧ x < j ∧
    lastValue a a[x]! x a.size = endIdx) ∧
  (∀ q, start < q → q ≤ j → ∃ x, start ≤ x ∧ x < q ∧
    q ≤ lastValue a a[x]! x a.size)

theorem nextCut_eq_of_scan_close (a : Array Char) (start j endIdx : Nat)
    (hj : j < a.size) (hsj : start ≤ j) (hstart : isCutPoint a start)
    (hbound : ∀ x, start ≤ x → x < j →
      lastValue a a[x]! x a.size ≤ endIdx)
    (hobstruct : ∀ q, start < q → q ≤ j → ∃ x, start ≤ x ∧ x < q ∧
      q ≤ lastValue a a[x]! x a.size)
    (hclose : j = max endIdx (lastValue a a[j]! j a.size)) :
    nextCut a start = j + 1 := by
  have hjlast : lastValue a a[j]! j a.size < a.size :=
    lastValue_lt a a[j]! j a.size hj
  have hcut : isCutPoint a (j + 1) := by
    rw [isCutPoint_iff_lastValue]
    refine ⟨by omega, ?_⟩
    intro x hx
    by_cases hxs : x < start
    · have hs := (isCutPoint_iff_lastValue a start).mp hstart
      exact Nat.lt_trans (hs.2 x hxs) (by omega)
    · by_cases hxj : x < j
      · have hb := hbound x (by omega) hxj
        have : endIdx ≤ j := by omega
        omega
      · have heq : x = j := by omega
        subst x
        omega
  apply Nat.le_antisymm
  · exact nextCut_min a start (j + 1) hcut (by
      have := hstart.1
      omega)
  · have hgt := nextCut_gt a start (by
      have := hstart.1
      omega)
    by_contra hlt
    have hnxt_lt : nextCut a start < j + 1 := by omega
    have hnxt_le_j : nextCut a start ≤ j := by omega
    have hnxt_cut := nextCut_isCutPoint a start
    rcases hobstruct (nextCut a start) (by omega) hnxt_le_j with ⟨x, hsx, hx, hle⟩
    have hall := (isCutPoint_iff_lastValue a (nextCut a start)).mp hnxt_cut
    have := hall.2 x hx
    omega

theorem greedyRun_eq_buildParts (a : Array Char) (m : List (Char × Nat))
    (hm : ∀ x, x < a.size → getLast m a[x]! x = lastValue a a[x]! x a.size)
    (j start endIdx : Nat) (resRev : List Nat)
    (hinv : scanInvariant a j start endIdx resRev) :
    greedyRun a m j start endIdx resRev = buildParts a 0 := by
  fun_induction greedyRun a m j start endIdx resRev
  case case1 j start endIdx resRev hj lastJ newEnd hclose ih =>
    rcases hinv with ⟨hsj, hjs, hstart, hparts, hbound, hwitness, hobstruct⟩
    have hlast := hm j hj
    have hnew : newEnd = max endIdx (lastValue a a[j]! j a.size) := by
      dsimp only [newEnd, lastJ]
      rw [hlast]
    have hnext : nextCut a start = j + 1 := by
      apply nextCut_eq_of_scan_close a start j endIdx hj hsj hstart hbound hobstruct
      rw [← hnew]
      exact hclose
    apply ih
    refine ⟨by omega, by omega, by simpa [hnext] using nextCut_isCutPoint a start, ?_, ?_, ?_, ?_⟩
    · have hbuild := buildParts_eq_cons a start (by
        have := hstart.1
        omega)
      rw [hnext] at hbuild
      have hne : newEnd = j := hclose.symm
      rw [List.reverse_cons, hne]
      simpa [List.append_assoc, hbuild] using hparts
    · intro x hx1 hx2
      omega
    · intro hend
      omega
    · intro q hq1 hq2
      omega
  case case2 j start endIdx resRev hj lastJ newEnd hclose ih =>
    rcases hinv with ⟨hsj, hjs, hstart, hparts, hbound, hwitness, hobstruct⟩
    have hlast := hm j hj
    have hnew : newEnd = max endIdx (lastValue a a[j]! j a.size) := by
      dsimp only [newEnd, lastJ]
      rw [hlast]
    have hj_le_last : j ≤ lastValue a a[j]! j a.size :=
      lastValue_ge_match a a[j]! j a.size j hj rfl
    have hnew_gt : j < max endIdx (lastValue a a[j]! j a.size) := by
      rw [← hnew]
      omega
    apply ih
    refine ⟨by omega, by omega, hstart, hparts, ?_, ?_, ?_⟩
    · intro x hx1 hx2
      by_cases hxj : x < j
      · rw [hnew]
        exact Nat.le_trans (hbound x hx1 hxj) (Nat.le_max_left _ _)
      · have : x = j := by omega
        subst x
        rw [hnew]
        exact Nat.le_max_right _ _
    · intro hgt
      by_cases he : endIdx ≤ lastValue a a[j]! j a.size
      · refine ⟨j, hsj, by omega, ?_⟩
        rw [hnew, Nat.max_eq_right he]
      · have he' : lastValue a a[j]! j a.size ≤ endIdx := by omega
        rcases hwitness (by omega) with ⟨x, hx1, hx2, hx3⟩
        refine ⟨x, hx1, by omega, ?_⟩
        rw [hnew, Nat.max_eq_left he']
        exact hx3
    · intro q hq1 hq2
      by_cases hqj : q ≤ j
      · exact hobstruct q hq1 hqj
      · have hq : q = j + 1 := by omega
        subst q
        by_cases he : endIdx ≤ lastValue a a[j]! j a.size
        · refine ⟨j, hsj, by omega, ?_⟩
          have := Nat.max_eq_right he
          omega
        · have he' : lastValue a a[j]! j a.size < endIdx := by omega
          rcases hwitness (by omega) with ⟨x, hx1, hx2, hx3⟩
          refine ⟨x, hx1, by omega, ?_⟩
          omega
  case case3 j start endIdx resRev hj =>
    rcases hinv with ⟨hsj, hjs, hstart, hparts, hbound, hwitness, hobstruct⟩
    have hjeq : j = a.size := by omega
    subst j
    have hseq : start = a.size := by
      by_contra hne
      have hslt : start < a.size := by omega
      rcases hobstruct a.size hslt (Nat.le_refl _) with ⟨x, hx1, hx2, hle⟩
      have hlt := lastValue_lt a a[x]! x a.size hx2
      omega
    subst start
    have hb : buildParts a a.size = [] := by
      rw [buildParts.eq_def]
      simp
    rw [hb, List.append_nil] at hparts
    exact hparts

theorem greedyRun_full_eq_buildParts (a : Array Char) :
    greedyRun a (lastMapPrefix a a.size) 0 0 0 [] = buildParts a 0 := by
  apply greedyRun_eq_buildParts a (lastMapPrefix a a.size)
  · intro x hx
    exact getLast_lastMapPrefix a a.size a[x]! x
  · refine ⟨Nat.le_refl _, Nat.zero_le _, isCutPoint_zero a, by simp, ?_, ?_, ?_⟩
    · intro x _ hx
      omega
    · intro h
      omega
    · intro q hq _
      omega

theorem arrayPostcondition_eq (s : Array Char) (result : List Nat) :
    arrayPostcondition s result ↔ postcondition s result := by
  rfl

prove_correct partitionLabels by
  velvet_vcgen [partitionLabels, postcondition] with try finish
  case max_parts =>
    apply (arrayPostcondition_eq _ _).mp
    exact partitionLabels_empty _ (by simpa using if_cond)
  case max_parts =>
    rename_i s
    have hi : i = s.size :=
      Nat.le_antisymm build_bounds (Nat.le_of_not_gt h_done_with)
    subst i
    rw [build_model] at scan_model
    have hj : j = s.size :=
      Nat.le_antisymm scan_bounds (Nat.le_of_not_gt h_done_with_1)
    have hscan := scan_model
    rw [greedyRun.eq_def, dite_eq_right h_done_with_1] at hscan
    rw [greedyRun_full_eq_buildParts] at hscan
    apply (arrayPostcondition_eq _ _).mp
    rw [hscan]
    exact partitionLabels_correct s
  case build_model =>
    rename_i s
    exact lastMapPrefix_zero s
  case update_model =>
    rfl
  case update_model =>
    simp_all [updateRun]
  case update_model =>
    simp_all [updateRun]
  case build_model =>
    simp_all [lastMapPrefix_succ, updateRun, updateAll]
  case build_model =>
    simp_all [lastMapPrefix_succ, updateRun, updateAll]
  case lookup_model =>
    rfl
  case lookup_model =>
    simp_all [lookupRun]
  case scan_model =>
    rename_i s
    have hlast : lastJ = getLast lastMap s[j]! j := by
      have he : entries = [] := by simpa using h_done_with_1
      subst entries
      simpa [lookupRun, getLast] using lookup_model
    have hm : Nat.max endIdx lastJ = lastJ := Nat.max_eq_right (by omega)
    rw [greedyRun.eq_def, dite_eq_left greedy_scan] at scan_model
    dsimp only at scan_model
    rw [← hlast, hm, ite_eq_left closes] at scan_model
    simpa using scan_model
  case scan_model =>
    rename_i s
    have hlast : lastJ = getLast lastMap s[j]! j := by
      have he : entries = [] := by simpa using h_done_with_1
      subst entries
      simpa [lookupRun, getLast] using lookup_model
    have hm : Nat.max endIdx lastJ = lastJ := Nat.max_eq_right (by omega)
    rw [greedyRun.eq_def, dite_eq_left greedy_scan] at scan_model
    dsimp only at scan_model
    rw [← hlast, hm, ite_eq_right closes] at scan_model
    exact scan_model
  case scan_model =>
    rename_i s
    have hlast : lastJ = getLast lastMap s[j]! j := by
      have he : entries = [] := by simpa using h_done_with_1
      subst entries
      simpa [lookupRun, getLast] using lookup_model
    have hm : Nat.max endIdx lastJ = endIdx := Nat.max_eq_left (by omega)
    rw [greedyRun.eq_def, dite_eq_left greedy_scan] at scan_model
    dsimp only at scan_model
    rw [← hlast, hm, ite_eq_left closes] at scan_model
    simpa using scan_model
  case scan_model =>
    rename_i s
    have hlast : lastJ = getLast lastMap s[j]! j := by
      have he : entries = [] := by simpa using h_done_with_1
      subst entries
      simpa [lookupRun, getLast] using lookup_model
    have hm : Nat.max endIdx lastJ = endIdx := Nat.max_eq_left (by omega)
    rw [greedyRun.eq_def, dite_eq_left greedy_scan] at scan_model
    dsimp only at scan_model
    rw [← hlast, hm, ite_eq_right closes] at scan_model
    exact scan_model
  case lookup_model =>
    simp_all [lookupRun]

end Proof

end PartitionLabels
