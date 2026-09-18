module

public import Velvet
public meta import Velvet

/-!
## Program description

Given a 1-indexed array of integers `numbers` that is already sorted in
non-decreasing order, find two numbers such that they add up to a specific
`target` number. Return the indices of the two numbers (1-indexed) as an
integer array `[index1, index2]` of length 2.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace TwoSumIIInputArrayIsSorted

section Specs

public def isSortedNondecreasing (numbers : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!

public def isWitnessPair (numbers : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target

public def hasUniqueWitnessPair (numbers : Array Int) (target : Int) : Prop :=
  (∃ (i : Nat) (j : Nat), isWitnessPair numbers target i j) ∧
  (∀ (i₁ : Nat) (j₁ : Nat) (i₂ : Nat) (j₂ : Nat),
    isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)

public def outputMatchesUniquePair (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  (1 ≤ result[0]!) ∧ (result[0]! < result[1]!) ∧ (result[1]! ≤ numbers.size) ∧
  (numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target) ∧
  (∀ (i : Nat) (j : Nat), isWitnessPair numbers target i j →
    result[0]! = i + 1 ∧ result[1]! = j + 1)

public def precondition (numbers : Array Int) (target : Int) : Prop :=
  numbers.size ≥ 2 ∧
  isSortedNondecreasing numbers ∧
  hasUniqueWitnessPair numbers target

public def postcondition (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  outputMatchesUniquePair numbers target result

end Specs

section Implementation

method twoSum (numbers : Array Int) (target : Int)
  returns (result : Array Nat)
  requires valid: precondition numbers target
  ensures matches_unique_pair: postcondition numbers target result
do
  let mut l : Nat := 0
  let mut r : Nat := numbers.size - 1
  let mut found : Bool := false
  let mut ansL : Nat := 0
  let mut ansR : Nat := 1
  while' scanning: l < r ∧ found = false
    invariant l_le_r: l ≤ r
    invariant r_lt_size: r < numbers.size
    invariant l_lt_size: l < numbers.size
    invariant found_witness: found = true → isWitnessPair numbers target ansL ansR
    invariant witness_in_window: found = false →
      ∃ wL wR, isWitnessPair numbers target wL wR ∧ l ≤ wL ∧ wR ≤ r
    decreasing remaining: if found then 0 else r - l
    done_with done: l = r ∨ found = true
  do
    let sum : Int := numbers[l]! + numbers[r]!
    if sum_eq: sum = target then
      ansL := l
      ansR := r
      found := true
    else if sum_lt: sum < target then
      l := l + 1
    else
      r := r - 1
  return #[ansL + 1, ansR + 1]

end Implementation

section Proof

theorem sorted_le (numbers : Array Int) (hsorted : isSortedNondecreasing numbers)
    (i j : Nat) (hij : i ≤ j) (hj : j < numbers.size) :
    numbers[i]! ≤ numbers[j]! := by
  by_cases heq : i = j
  · subst heq
    omega
  · exact hsorted i j (Nat.lt_of_le_of_ne hij heq) hj

theorem initial_witness_in_window (numbers : Array Int) (target : Int)
    (hpre : precondition numbers target) :
    ∃ wL wR, isWitnessPair numbers target wL wR ∧ 0 ≤ wL ∧ wR ≤ numbers.size - 1 := by
  obtain ⟨wL, wR, hw⟩ := hpre.2.2.1
  have hr := hw.2.1
  refine ⟨wL, wR, hw, Nat.zero_le wL, by omega⟩

theorem step_left_preserves_witness (numbers : Array Int) (target : Int)
    (hsorted : isSortedNondecreasing numbers)
    (l r : Nat) (hr : r < numbers.size)
    (wL wR : Nat) (hw : isWitnessPair numbers target wL wR)
    (hlw : l ≤ wL) (hwr : wR ≤ r)
    (hsum_lt : numbers[l]! + numbers[r]! < target) :
    l + 1 ≤ wL ∧ wR ≤ r := by
  constructor
  · by_cases hle : l + 1 ≤ wL
    · exact hle
    · have heq : wL = l := by omega
      have hwR_le : numbers[wR]! ≤ numbers[r]! :=
        sorted_le numbers hsorted wR r hwr hr
      have hsum_eq : numbers[wL]! + numbers[wR]! = target := hw.2.2
      have htarget_le : target ≤ numbers[l]! + numbers[r]! := by
        calc target = numbers[wL]! + numbers[wR]! := hsum_eq.symm
          _ = numbers[l]! + numbers[wR]! := by rw [heq]
          _ ≤ numbers[l]! + numbers[r]! := by omega
      omega
  · exact hwr

theorem step_right_preserves_witness (numbers : Array Int) (target : Int)
    (hsorted : isSortedNondecreasing numbers)
    (l r : Nat)
    (wL wR : Nat) (hw : isWitnessPair numbers target wL wR)
    (hlw : l ≤ wL) (hwr : wR ≤ r)
    (hsum_gt : target < numbers[l]! + numbers[r]!) :
    l ≤ wL ∧ wR ≤ r - 1 := by
  constructor
  · exact hlw
  · by_cases hle : wR ≤ r - 1
    · exact hle
    · have heq : wR = r := by omega
      have hwL_ge : numbers[l]! ≤ numbers[wL]! :=
        sorted_le numbers hsorted l wL hlw (Nat.lt_trans hw.1 hw.2.1)
      have hsum_eq : numbers[wL]! + numbers[wR]! = target := hw.2.2
      have htarget_ge : numbers[l]! + numbers[r]! ≤ target := by
        calc numbers[l]! + numbers[r]! = numbers[l]! + numbers[wR]! := by rw [heq]
          _ ≤ numbers[wL]! + numbers[wR]! := by omega
          _ = target := hsum_eq
      omega

theorem exit_satisfies_postcondition (numbers : Array Int) (target : Int)
    (hpre : precondition numbers target)
    (l r : Nat) (found : Bool) (ansL ansR : Nat)
    (hfound_witness : found = true → isWitnessPair numbers target ansL ansR)
    (hwitness_window : found = false → ∃ wL wR, isWitnessPair numbers target wL wR ∧ l ≤ wL ∧ wR ≤ r)
    (hdone : l = r ∨ found = true) :
    postcondition numbers target #[ansL + 1, ansR + 1] := by
  have hfound : found = true := by
    cases found with
    | false =>
        have heq : l = r := by
          cases hdone with
          | inl h => exact h
          | inr h => contradiction
        obtain ⟨wL, wR, hw, hlw, hwr⟩ := hwitness_window rfl
        have : wL < wR := hw.1
        have : wL = wR := by omega
        omega
    | true => rfl
  have hw : isWitnessPair numbers target ansL ansR := hfound_witness hfound
  have hw_lt := hw.1
  have hw_sz := hw.2.1
  have hw_sum := hw.2.2
  unfold postcondition outputMatchesUniquePair
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp; omega
  · simp; omega
  · simp [hw_sum]
  · intro i j hij
    obtain ⟨heq1, heq2⟩ := hpre.2.2.2 i j ansL ansR hij hw
    subst heq1 heq2
    simp

prove_correct twoSum by
  velvet_vcgen [twoSum, postcondition] with try finish
  case r_lt_size =>
    rename_i numbers target
    have := valid.1
    omega
  case l_lt_size =>
    rename_i numbers target
    have := valid.1
    omega
  case witness_in_window =>
    rename_i numbers target
    intro _
    exact initial_witness_in_window numbers target valid
  case matches_unique_pair =>
    rename_i numbers target
    exact exit_satisfies_postcondition numbers target valid l r found ansL ansR found_witness witness_in_window done
  case found_witness =>
    intro _
    exact ⟨scanning.1, r_lt_size, sum_eq⟩
  case witness_in_window =>
    rename_i numbers target
    intro _
    obtain ⟨wL, wR, hw, hlw, hwr⟩ := witness_in_window scanning.2
    have hstep := step_left_preserves_witness numbers target valid.2.1 l r r_lt_size wL wR hw hlw hwr sum_lt
    exact ⟨wL, wR, hw, hstep.1, hstep.2⟩
  case witness_in_window =>
    rename_i numbers target
    intro _
    obtain ⟨wL, wR, hw, hlw, hwr⟩ := witness_in_window scanning.2
    have hgt : target < numbers[l]! + numbers[r]! := by omega
    have hstep := step_right_preserves_witness numbers target valid.2.1 l r wL wR hw hlw hwr hgt
    exact ⟨wL, wR, hw, hstep.1, hstep.2⟩

end Proof

end TwoSumIIInputArrayIsSorted
