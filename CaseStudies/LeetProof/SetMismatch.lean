module

public import Velvet
public meta import Velvet

/-!
## Program description

You have a set of integers `s`, which originally contains all the numbers from
`1` to `n`. Unfortunately, due to some error, one of the numbers in `s` got
duplicated to another number in the set, which results in repetition of one
number and loss of another number.

Given an integer array `nums` representing the data status of this set after the
error, find and return the number that occurs twice and the number that is
missing in the form of an array `[dup, miss]`.

The program is expected to run in O(n^2) time and O(1) extra space, excluding the
returned array.
-/

namespace SetMismatch

section Specs

public def inOneToN (n : Nat) (x : Nat) : Prop :=
  1 ≤ x ∧ x ≤ n

public def hasSetMismatch (nums : Array Nat) : Prop :=
  let n : Nat := nums.size
  (n > 0) ∧
  (∀ (i : Nat), i < n → inOneToN n nums[i]!) ∧
  (∃ (dup : Nat) (miss : Nat),
      dup ≠ miss ∧
      inOneToN n dup ∧
      inOneToN n miss ∧
      nums.count dup = 2 ∧
      nums.count miss = 0 ∧
      (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1))

public def precondition (nums : Array Nat) : Prop :=
  hasSetMismatch nums

public def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  let n : Nat := nums.size
  result.size = 2 ∧
  let dup : Nat := result[0]!
  let miss : Nat := result[1]!
  dup ≠ miss ∧
  inOneToN n dup ∧
  inOneToN n miss ∧
  nums.count dup = 2 ∧
  nums.count miss = 0 ∧
  (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1)

end Specs

section Implementation

public def scanGo (nums : Array Nat) (x : Nat) (dup miss : Nat) : Nat × Nat :=
  if x ≤ nums.size then
    let c := nums.count x
    let dup' := if c = 2 then x else dup
    let miss' := if c = 0 then x else miss
    scanGo nums (x + 1) dup' miss'
  else
    (dup, miss)
termination_by (nums.size + 1) - x

public def findMismatch (nums : Array Nat) : Array Nat :=
  let dm := scanGo nums 1 0 0
  #[dm.1, dm.2]

method findErrorNums (nums : Array Nat)
  returns (result : Array Nat)
  requires valid: precondition nums
  ensures mismatch: postcondition nums result
do
  let n := nums.size
  let mut dup : Nat := 0
  let mut miss : Nat := 0
  let mut x : Nat := 1
  while scanning: x ≤ n
    invariant bounds: 1 ≤ x ∧ x ≤ n + 1
    invariant scan_continuation:
      scanGo nums x dup miss = scanGo nums 1 0 0
    decreasing remaining: n + 1 - x
    done_with done: x = n + 1
  do
    let c := nums.count x
    if is_dup: c = 2 then
      dup := x
    else if is_miss: c = 0 then
      miss := x
    x := x + 1
  return #[dup, miss]

end Implementation

section Proof

theorem if_lt_succ (a k : Nat) (h : a ≠ k) :
    (if a < k then a else 0) = (if a < k + 1 then a else 0) := by
  by_cases hak : a < k
  · have hak' : a < k + 1 := by omega
    simp [hak, hak']
  · have hnot2 : ¬ a < k + 1 := by omega
    simp [hak, hnot2]

theorem scanGo_correct (nums : Array Nat) (dup miss : Nat)
    (hdupIn : inOneToN nums.size dup) (hmissIn : inOneToN nums.size miss)
    (hcountDup : nums.count dup = 2) (hcountMiss : nums.count miss = 0)
    (hcountOther : ∀ x, inOneToN nums.size x → x ≠ dup → x ≠ miss → nums.count x = 1) :
    ∀ x : Nat, 1 ≤ x →
      scanGo nums x (if dup < x then dup else 0) (if miss < x then miss else 0) = (dup, miss)
  | x, hx1 => by
      rw [scanGo.eq_def]
      by_cases hx : x ≤ nums.size
      · simp [hx]
        have hd_step : (if nums.count x = 2 then x else if dup < x then dup else 0) =
            if dup < x + 1 then dup else 0 := by
          by_cases hxd : x = dup
          · subst x
            simp [hcountDup]
          · have h_cne : nums.count x ≠ 2 := by
              by_cases hxm : x = miss
              · subst x
                simp [hcountMiss]
              · have : nums.count x = 1 := hcountOther x ⟨hx1, hx⟩ hxd hxm
                omega
            have := if_lt_succ dup x (Ne.symm hxd)
            simpa [h_cne] using this
        have hm_step : (if nums.count x = 0 then x else if miss < x then miss else 0) =
            if miss < x + 1 then miss else 0 := by
          by_cases hxm : x = miss
          · subst x
            simp [hcountMiss]
          · have h_cne : nums.count x ≠ 0 := by
              by_cases hxd : x = dup
              · subst x
                simp [hcountDup]
              · have : nums.count x = 1 := hcountOther x ⟨hx1, hx⟩ hxd hxm
                omega
            have := if_lt_succ miss x (Ne.symm hxm)
            simpa [h_cne] using this
        rw [hd_step, hm_step]
        exact scanGo_correct nums dup miss hdupIn hmissIn hcountDup hcountMiss hcountOther (x + 1) (by omega)
      · have hnot : ¬ (x ≤ nums.size) := hx
        simp [hnot]
        unfold inOneToN at hdupIn hmissIn
        constructor <;> { intro hle; omega }
termination_by x => (nums.size + 1) - x

theorem findMismatch_correct (nums : Array Nat) (hpre : precondition nums) :
    postcondition nums (findMismatch nums) := by
  unfold precondition hasSetMismatch at hpre
  rcases hpre with ⟨_hnpos, _hdom, ⟨dup, miss, hne, hdupIn, hmissIn, hcountDup, hcountMiss, hcountOther⟩⟩
  have hscan := scanGo_correct nums dup miss hdupIn hmissIn hcountDup hcountMiss hcountOther 1 (by omega)
  have h1 : (if dup < 1 then dup else 0) = 0 := by
    by_cases h : dup < 1
    · unfold inOneToN at hdupIn; omega
    · simp [h]
  have h2 : (if miss < 1 then miss else 0) = 0 := by
    by_cases h : miss < 1
    · unfold inOneToN at hmissIn; omega
    · simp [h]
  rw [h1, h2] at hscan
  unfold postcondition findMismatch
  simp [hscan]
  exact ⟨hne, hdupIn, hmissIn, hcountDup, hcountMiss, hcountOther⟩

prove_correct findErrorNums by
  velvet_vcgen [findErrorNums, postcondition] with try finish
  case scan_continuation =>
    rename_i nums
    rw [scanGo.eq_def] at scan_continuation
    simp [scanning, is_dup] at scan_continuation
    exact scan_continuation
  case scan_continuation =>
    rename_i nums
    rw [scanGo.eq_def] at scan_continuation
    simp [scanning, is_miss] at scan_continuation
    exact scan_continuation
  case scan_continuation =>
    rename_i nums
    rw [scanGo.eq_def] at scan_continuation
    simp [scanning, is_dup, is_miss] at scan_continuation
    exact scan_continuation
  case mismatch =>
    rename_i nums
    rw [done] at scan_continuation
    rw [scanGo.eq_def] at scan_continuation
    have hnot : ¬ (nums.size + 1 ≤ nums.size) := by omega
    simp [hnot] at scan_continuation
    have hres : findMismatch nums = #[dup, miss] := by
      unfold findMismatch
      simp [← scan_continuation]
    have hpost := findMismatch_correct nums valid
    rw [hres] at hpost
    exact hpost

end Proof

end SetMismatch
