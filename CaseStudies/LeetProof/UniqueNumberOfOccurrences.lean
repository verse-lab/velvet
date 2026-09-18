module

public import Velvet
public meta import Velvet

/-!
## Program description

1207. Unique Number of Occurrences: decide whether all element-frequency counts
in an integer array are pairwise distinct.

1. Input is an array of integers `arr`.
2. For each integer value `v` that appears in the array, define occ(v) as the
   number of indices `i` with `arr[i] = v`.
3. The output is `true` exactly when for any two distinct values `x` and `y`
   that both appear in the array, occ(x) ≠ occ(y).
4. Values that do not appear in the array are irrelevant to the uniqueness
   condition.
5. The given constraints restrict each element to the range [-1000, 1000].

The program is expected to run in O(n + R^2) time and O(R) space, where
R = 2001 is the range of values.
-/

namespace UniqueNumberOfOccurrences

section Specs

public def inProblemRange (x : Int) : Prop :=
  (-1000 ≤ x) ∧ (x ≤ 1000)

public def countsAreUnique (arr : Array Int) : Prop :=
  ∀ (x : Int) (y : Int), x ≠ y → x ∈ arr → y ∈ arr → arr.count x ≠ arr.count y

public def precondition (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → inProblemRange (arr[i]!)

public def postcondition (arr : Array Int) (result : Bool) : Prop :=
  (result = true ↔ countsAreUnique arr)

end Specs

section Implementation

method uniqueOccurrences (arr : Array Int)
  returns (result : Bool)
  requires valid: precondition arr
  ensures unique: postcondition arr result
do
  let mut counts : Array Nat := Array.replicate 2001 0
  let mut i : Nat := 0
  while' counting: i < arr.size
    invariant count_size: counts.size = 2001
    invariant i_bounds: i ≤ arr.size
    invariant prefix_counts: ∀ (v : Int), inProblemRange v →
      counts[(v + 1000).toNat]! = (arr.toList.take i).count v
    decreasing remaining_i: arr.size - i
    done_with counted: i = arr.size
  do
    let v : Int := arr[i]!
    let idx : Nat := (v + 1000).toNat
    let c : Nat := counts[idx]!
    counts := counts.set! idx (c + 1)
    i := i + 1

  let mut ok : Bool := true
  let mut x : Nat := 0
  while' outer_check: x < 2001 ∧ ok = true
    invariant x_bound: x ≤ 2001
    invariant count_size2: counts.size = 2001
    invariant outer_checked: ok = true →
      ∀ a b : Nat, a < x → a < b → b < 2001 →
        counts[a]! > 0 → counts[b]! > 0 → counts[a]! ≠ counts[b]!
    invariant outer_found_dup: ok = false →
      ∃ a b : Nat, a < b ∧ b < 2001 ∧
        counts[a]! > 0 ∧ counts[b]! > 0 ∧ counts[a]! = counts[b]!
    decreasing remaining_x: 2001 - x
    done_with outer_done: x = 2001 ∨ ok = false
  do
    let cx : Nat := counts[x]!
    if cx_pos: cx > 0 then
      let mut y : Nat := x + 1
      while' inner_check: y < 2001 ∧ ok = true
        invariant count_size3: counts.size = 2001
        invariant x_bound_inner: x < 2001
        invariant y_bounds: x + 1 ≤ y ∧ y ≤ 2001
        invariant cx_is_pos: counts[x]! > 0
        invariant outer_checked_inner: ok = true →
          ∀ a b : Nat, a < x → a < b → b < 2001 →
            counts[a]! > 0 → counts[b]! > 0 → counts[a]! ≠ counts[b]!
        invariant inner_checked: ok = true →
          ∀ b : Nat, x < b → b < y → counts[b]! > 0 → counts[x]! ≠ counts[b]!
        invariant inner_found_dup: ok = false →
          ∃ a b : Nat, a < b ∧ b < 2001 ∧
            counts[a]! > 0 ∧ counts[b]! > 0 ∧ counts[a]! = counts[b]!
        decreasing remaining_y: 2001 - y
        done_with inner_done: y = 2001 ∨ ok = false
      do
        let cy : Nat := counts[y]!
        if cy_pos: cy > 0 then
          if eq_count: counts[x]! = cy then
            ok := false
        y := y + 1
    x := x + 1
  return ok

end Implementation

section Proof

public def toIdx (x : Int) : Nat := (x + 1000).toNat
public def fromIdx (i : Nat) : Int := (i : Int) - 1000

theorem toIdx_lt_2001 {x : Int} (hx : inProblemRange x) : toIdx x < 2001 := by
  unfold inProblemRange at hx
  unfold toIdx
  omega

theorem fromIdx_inProblemRange {i : Nat} (hi : i < 2001) : inProblemRange (fromIdx i) := by
  unfold inProblemRange fromIdx
  constructor <;> omega

theorem toIdx_fromIdx {i : Nat} (hi : i < 2001) : toIdx (fromIdx i) = i := by
  unfold toIdx fromIdx
  omega

theorem fromIdx_toIdx {x : Int} (hx : inProblemRange x) : fromIdx (toIdx x) = x := by
  unfold inProblemRange toIdx fromIdx at *
  omega

theorem toIdx_inj {x y : Int} (hx : inProblemRange x) (hy : inProblemRange y) (h : toIdx x = toIdx y) : x = y := by
  have := congrArg fromIdx h
  rw [fromIdx_toIdx hx, fromIdx_toIdx hy] at this
  exact this

theorem replicate_zero_get! (i : Nat) (hi : i < 2001) :
    (Array.replicate 2001 0)[i]! = 0 := by
  have hpos : i < (Array.replicate 2001 0).size := by
    rw [Array.size_replicate]
    exact hi
  rw [getElem!_pos (Array.replicate 2001 0) i hpos]
  exact Array.getElem_replicate hpos

theorem list_mem_iff_count_pos (l : List Int) (x : Int) :
    x ∈ l ↔ l.count x > 0 := by
  constructor
  · intro hx
    have hne : l.count x ≠ 0 := by
      intro hzero
      exact (List.count_eq_zero.mp hzero) hx
    omega
  · intro hpos
    apply Classical.byContradiction
    intro hnot
    have hzero : l.count x = 0 := List.count_eq_zero.mpr hnot
    omega

theorem mem_iff_count_pos (arr : Array Int) (x : Int) :
    x ∈ arr ↔ arr.count x > 0 := by
  rw [Array.mem_def, ← Array.count_toList]
  exact list_mem_iff_count_pos arr.toList x

theorem mem_inProblemRange (arr : Array Int) (hpre : precondition arr) {x : Int} (hx : x ∈ arr) :
    inProblemRange x := by
  rcases Array.getElem_of_mem hx with ⟨i, hi, rfl⟩
  have h := hpre i hi
  rwa [getElem!_pos arr i hi] at h

theorem count_take_succ (arr : Array Int) (i : Nat) (v : Int) (hi : i < arr.size) :
    (arr.toList.take (i + 1)).count v =
      (arr.toList.take i).count v + if arr[i]! = v then 1 else 0 := by
  have hi_len : i < arr.toList.length := by simpa using hi
  rw [List.take_succ_eq_append_getElem hi_len]
  rw [List.count_append]
  simp [getElem!_pos arr i hi]
  by_cases h : arr[i] = v
  · simp [h]
  · simp [h]

theorem take_size_count (arr : Array Int) (v : Int) :
    (arr.toList.take arr.size).count v = arr.count v := by
  have hlen : arr.toList.length ≤ arr.size := by simp
  rw [List.take_of_length_le hlen, ← Array.count_toList]

theorem step_preserves_prefix_counts (arr : Array Int) (counts : Array Nat) (i : Nat)
    (hi : i < arr.size) (hsz : counts.size = 2001) (hpre : precondition arr)
    (hinv : ∀ v, inProblemRange v → counts[(v + 1000).toNat]! = (arr.toList.take i).count v) :
    ∀ v, inProblemRange v →
      (counts.set! (toIdx arr[i]!) (counts[toIdx arr[i]!]! + 1))[(v + 1000).toNat]! =
        (arr.toList.take (i + 1)).count v := by
  intro v hv
  have hvi := hpre i hi
  have hidx_i : toIdx arr[i]! < counts.size := by
    rw [hsz]
    exact toIdx_lt_2001 hvi
  have hidx_v : toIdx v < counts.size := by
    rw [hsz]
    exact toIdx_lt_2001 hv
  rw [count_take_succ arr i v hi]
  by_cases heq : arr[i]! = v
  · have h_idx_eq : toIdx arr[i]! = toIdx v := by rw [heq]
    have h1 : (v + 1000).toNat = toIdx v := rfl
    rw [h_idx_eq, h1]
    rw [Array.getElem!_set!_self counts (toIdx v) (counts[toIdx v]! + 1) hidx_v]
    unfold toIdx
    rw [hinv v hv, heq]
    simp
  · have hne : toIdx arr[i]! ≠ (v + 1000).toNat := by
      intro h
      have h' : toIdx arr[i]! = toIdx v := h
      exact heq (toIdx_inj hvi hv h')
    rw [Array.getElem!_set!_ne counts (toIdx arr[i]!) ((v + 1000).toNat) (counts[toIdx arr[i]!]! + 1) hne]
    rw [hinv v hv]
    simp [heq]

theorem postcondition_from_checked (arr : Array Int) (counts : Array Nat) (ok : Bool) (x : Nat)
    (hpre : precondition arr)
    (hcounts : ∀ v, inProblemRange v → counts[(v + 1000).toNat]! = arr.count v)
    (hchecked : ok = true → ∀ a b : Nat, a < x → a < b → b < 2001 →
      counts[a]! > 0 → counts[b]! > 0 → counts[a]! ≠ counts[b]!)
    (hfound : ok = false → ∃ a b : Nat, a < b ∧ b < 2001 ∧
      counts[a]! > 0 ∧ counts[b]! > 0 ∧ counts[a]! = counts[b]!)
    (hdone : x = 2001 ∨ ok = false) :
    postcondition arr ok := by
  unfold postcondition countsAreUnique
  cases ok with
  | false =>
      simp only [Bool.false_eq_true, false_iff]
      obtain ⟨a, b, hab, hb, ha_pos, hb_pos, hab_eq⟩ := hfound rfl
      have ha_lt : a < 2001 := by omega
      have hrange_a := fromIdx_inProblemRange ha_lt
      have hrange_b := fromIdx_inProblemRange hb
      have ha_to : toIdx (fromIdx a) = a := toIdx_fromIdx ha_lt
      have hb_to : toIdx (fromIdx b) = b := toIdx_fromIdx hb
      have hca : arr.count (fromIdx a) = counts[a]! := by
        have hc := hcounts (fromIdx a) hrange_a
        unfold toIdx at ha_to
        rw [ha_to] at hc
        exact hc.symm
      have hcb : arr.count (fromIdx b) = counts[b]! := by
        have hc := hcounts (fromIdx b) hrange_b
        unfold toIdx at hb_to
        rw [hb_to] at hc
        exact hc.symm
      have hmem_a : fromIdx a ∈ arr := by
        rw [mem_iff_count_pos, hca]
        exact ha_pos
      have hmem_b : fromIdx b ∈ arr := by
        rw [mem_iff_count_pos, hcb]
        exact hb_pos
      have hne : fromIdx a ≠ fromIdx b := by
        intro heq
        have := congrArg toIdx heq
        rw [toIdx_fromIdx ha_lt, toIdx_fromIdx hb] at this
        omega
      intro huni
      have := huni (fromIdx a) (fromIdx b) hne hmem_a hmem_b
      rw [hca, hcb] at this
      exact this hab_eq
  | true =>
      have hx : x = 2001 := by
        cases hdone with
        | inl h => exact h
        | inr h => contradiction
      simp only [true_iff]
      intro u v hne hu hv
      have hru := mem_inProblemRange arr hpre hu
      have hrv := mem_inProblemRange arr hpre hv
      have hu_pos : arr.count u > 0 := (mem_iff_count_pos arr u).1 hu
      have hv_pos : arr.count v > 0 := (mem_iff_count_pos arr v).1 hv
      have hau_lt : toIdx u < 2001 := toIdx_lt_2001 hru
      have hav_lt : toIdx v < 2001 := toIdx_lt_2001 hrv
      have hcu : counts[toIdx u]! = arr.count u := hcounts u hru
      have hcv : counts[toIdx v]! = arr.count v := hcounts v hrv
      have hidx_ne : toIdx u ≠ toIdx v := by
        intro heq
        exact hne (toIdx_inj hru hrv heq)
      have hchk := hchecked rfl
      have horder : toIdx u < toIdx v ∨ toIdx v < toIdx u := by omega
      cases horder with
      | inl hlt =>
          have := hchk (toIdx u) (toIdx v) (by omega) hlt hav_lt
          rw [hcu, hcv] at this
          exact this hu_pos hv_pos
      | inr hgt =>
          have := hchk (toIdx v) (toIdx u) (by omega) hgt hau_lt
          rw [hcu, hcv] at this
          exact Ne.symm (this hv_pos hu_pos)

prove_correct uniqueOccurrences by
  velvet_vcgen [uniqueOccurrences, postcondition] with try finish
  case prefix_counts =>
    intro v hv
    change (Array.replicate 2001 0)[toIdx v]! = _
    rw [replicate_zero_get! _ (toIdx_lt_2001 hv)]
    simp
  case prefix_counts =>
    intro v hv
    exact step_preserves_prefix_counts _ _ _ counting count_size valid prefix_counts v hv
  case unique =>
    rename_i arr
    have hcounts : ∀ v, inProblemRange v → counts[(v + 1000).toNat]! = arr.count v := by
      intro v hv
      have h1 := prefix_counts v hv
      rw [counted] at h1
      rw [h1, take_size_count]
    exact postcondition_from_checked arr counts ok x valid hcounts outer_checked outer_found_dup outer_done

end Proof

end UniqueNumberOfOccurrences
