module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Order.Basic

/-!
## Program description

Remove duplicates from a nondecreasing integer array and return the number of
unique elements together with an array whose relevant prefix contains them in
order. The program is expected to run in O(n) time and O(1) extra space.
-/

namespace RemoveDuplicatesFromSortedArray

section Specs

public def ArraySortedLe (a : Array Int) : Prop :=
  ∀ i, i + 1 < a.size → a[i]! ≤ a[i + 1]!

public def PrefixStrictIncreasing (a : Array Int) (k : Nat) : Prop :=
  k ≤ a.size ∧ ∀ i, i + 1 < k → a[i]! < a[i + 1]!

public def PrefixSameMembers (nums : Array Int) (k : Nat) (out : Array Int) : Prop :=
  k ≤ out.size ∧
    ∀ x, x ∈ nums ↔ ∃ i, i < k ∧ out[i]! = x

public def PrefixOccursInOrderFirst (nums out : Array Int) (k : Nat) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i, i < k → f i < nums.size ∧ out[i]! = nums[f i]!) ∧
    (∀ i j, i < j → j < k → f i < f j) ∧
    (∀ i, i < k → ∀ j, j < f i → nums[j]! ≠ out[i]!)

public def precondition (nums : Array Int) : Prop := ArraySortedLe nums

public def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  result.snd.size = nums.size ∧
  PrefixStrictIncreasing result.snd result.fst ∧
  PrefixSameMembers nums result.fst result.snd ∧
  PrefixOccursInOrderFirst nums result.snd result.fst

end Specs

section Implementation

public def ScannedMembers (nums : Array Int) (i write : Nat) (out : Array Int) : Prop :=
  ∀ x, x ∈ nums.take i ↔ ∃ j, j < write ∧ out[j]! = x

public def LastWritten (nums : Array Int) (i write : Nat) (last : Int)
    (out : Array Int) : Prop :=
  0 < i ∧ 0 < write ∧ write ≤ i ∧ i ≤ nums.size ∧
  last = nums[i - 1]! ∧ last = out[write - 1]!

public def OccursFirstBefore (nums out : Array Int) (write scanned : Nat) : Prop :=
  ∃ f : Nat → Nat,
    (∀ j, j < write → f j < scanned ∧ out[j]! = nums[f j]!) ∧
    (∀ j k, j < k → k < write → f j < f k) ∧
    (∀ j, j < write → ∀ k, k < f j → nums[k]! ≠ out[j]!)

public def compactScan (nums : Array Int) (i write : Nat) (last : Int)
    (out : Array Int) : Nat × Array Int :=
  if i < nums.size then
    let x := nums[i]!
    if x = last then compactScan nums (i + 1) write last out
    else compactScan nums (i + 1) (write + 1) x (out.set! write x)
  else (write, out)
termination_by nums.size - i

public def compact (nums : Array Int) : Nat × Array Int :=
  if nums.size = 0 then (0, nums)
  else
    let first := nums[0]!
    compactScan nums 1 1 first (nums.set! 0 first)

method removeDuplicates (nums : Array Int)
  returns (result : Nat × Array Int)
  requires sorted: precondition nums
  ensures compacted: postcondition nums result
do
  if empty: nums.size = 0 then
    return (0, nums)
  else
    let mut i : Nat := 1
    let mut write : Nat := 1
    let mut last : Int := nums[0]!
    let mut out : Array Int := nums.set! 0 last
    while' scanning: i < nums.size
      invariant continuation: compactScan nums i write last out = compact nums
      invariant output_size: out.size = nums.size
      invariant prefix_strict: PrefixStrictIncreasing out write
      invariant scanned_members: ScannedMembers nums i write out
      invariant first_occurrences: OccursFirstBefore nums out write i
      invariant last_written: LastWritten nums i write last out
      decreasing remaining: nums.size - i
    do
      let x := nums[i]!
      if repeated: x = last then
        i := i + 1
      else
        out := out.set! write x
        write := write + 1
        last := x
        i := i + 1
    return (write, out)

end Implementation

section Proof

theorem mem_take_succ (a : Array Int) (i : Nat) (x : Int) (hi : i < a.size) :
    x ∈ a.take (i + 1) ↔ x ∈ a.take i ∨ a[i]! = x := by
  simp [Array.mem_iff_getElem, getElem!_pos, hi]
  grind

theorem sortedLe_of_lt (a : Array Int) (h : ArraySortedLe a)
    {i j : Nat} (hi : i < j) (hj : j < a.size) : a[i]! ≤ a[j]! := by
  have chain : ∀ d i, i + d < a.size → a[i]! ≤ a[i + d]! := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro i hib
        cases d with
        | zero => simpa using h i (by omega)
        | succ d => exact (ih i (by omega)).trans (h (i + d + 1) (by omega))
  have heq : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hi)
  have hc := chain (j - i) i (by simpa [heq] using hj)
  simpa [heq] using hc

prove_correct removeDuplicates by
  velvet_vcgen [removeDuplicates, postcondition] with try finish
  case compacted =>
    rename_i nums
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact ⟨by simp, by simp⟩
    · unfold PrefixSameMembers
      have hn : nums.toList = [] := List.length_eq_zero_iff.mp (by simpa using empty)
      simp [Array.mem_def, hn]
    · unfold PrefixOccursInOrderFirst
      exact ⟨fun _ => 0, by simp⟩
  case continuation => simp [compact, empty]
  case prefix_strict =>
    unfold PrefixStrictIncreasing
    constructor
    · simpa [Array.size_set!] using (show 1 ≤ _ from Nat.one_le_iff_ne_zero.mpr empty)
    · intro i hi
      omega
  case scanned_members =>
    rename_i nums
    unfold ScannedMembers
    intro x
    rw [mem_take_succ nums 0 x (Nat.pos_of_ne_zero empty)]
    simp [Nat.pos_of_ne_zero empty]
  case first_occurrences =>
    rename_i nums
    unfold OccursFirstBefore
    refine ⟨fun i => i, ?_, ?_, ?_⟩
    · intro i hi
      have h0 : i = 0 := by omega
      subst i
      simp [Nat.pos_of_ne_zero empty]
    · intro i j hij hj
      omega
    · intro i hi j hj
      have : i = 0 := by omega
      subst i
      simp at hj
  case last_written =>
    rename_i nums
    unfold LastWritten
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
    · simp
    · simp [Nat.pos_of_ne_zero empty]
  case compacted =>
    rename_i nums
    have hi_eq : i = nums.size := by
      unfold LastWritten at last_written
      omega
    refine ⟨output_size, prefix_strict, ?_, ?_⟩
    · unfold PrefixSameMembers
      refine ⟨prefix_strict.1, ?_⟩
      intro x
      have hm := scanned_members x
      subst i
      simpa using hm
    · unfold OccursFirstBefore at first_occurrences
      unfold PrefixOccursInOrderFirst
      rcases first_occurrences with ⟨f, hf, hmono, hfirst⟩
      refine ⟨f, ?_, hmono, hfirst⟩
      intro j hj
      have hfj := hf j hj
      exact ⟨by omega, hfj.2⟩
  case continuation =>
    rw [compactScan.eq_def] at continuation
    simp only [scanning, repeated] at continuation
    exact continuation
  case scanned_members =>
    unfold ScannedMembers at scanned_members ⊢
    intro x
    rw [mem_take_succ _ _ _ scanning, scanned_members]
    constructor
    · rintro (h | h)
      · exact h
      · unfold LastWritten at last_written
        refine ⟨write - 1, by omega, ?_⟩
        rw [← last_written.2.2.2.2.2, ← repeated]
        exact h
    · intro h
      exact Or.inl h
  case first_occurrences =>
    unfold OccursFirstBefore at first_occurrences ⊢
    rcases first_occurrences with ⟨f, hf, hmono, hfirst⟩
    exact ⟨f, fun j hj => ⟨Nat.lt_succ_of_lt (hf j hj).1, (hf j hj).2⟩,
      hmono, hfirst⟩
  case last_written =>
    unfold LastWritten at last_written ⊢
    refine ⟨by omega, last_written.2.1, by omega,
      by omega, ?_, last_written.2.2.2.2.2⟩
    simpa using repeated.symm
  case continuation =>
    rw [compactScan.eq_def] at continuation
    simp only [scanning, repeated] at continuation
    exact continuation
  case prefix_strict =>
    rename_i nums
    unfold LastWritten at last_written
    have hw : write < out.size := by omega
    have hle : last ≤ nums[i]! := by
      rw [last_written.2.2.2.2.1]
      exact sortedLe_of_lt nums sorted (by omega) scanning
    have hlt : last < nums[i]! := lt_of_le_of_ne hle (Ne.symm repeated)
    unfold PrefixStrictIncreasing at prefix_strict ⊢
    refine ⟨by simpa [Array.size_set!] using (show write + 1 ≤ out.size by omega), ?_⟩
    intro k hk
    by_cases hb : k + 1 = write
    · rw [hb, Array.getElem!_set!_self out write nums[i]! hw]
      rw [Array.getElem!_set!_ne out write k nums[i]! (by omega)]
      have hk' : k = write - 1 := by omega
      rw [hk', ← last_written.2.2.2.2.2]
      exact hlt
    · rw [Array.getElem!_set!_ne out write k nums[i]! (by omega)]
      rw [Array.getElem!_set!_ne out write (k + 1) nums[i]! (by omega)]
      exact prefix_strict.2 k (by omega)
  case scanned_members =>
    rename_i nums
    unfold LastWritten at last_written
    have hw : write < out.size := by omega
    unfold ScannedMembers at scanned_members ⊢
    intro x
    rw [mem_take_succ _ _ _ scanning, scanned_members]
    constructor
    · rintro (h | rfl)
      · rcases h with ⟨j, hj, rfl⟩
        exact ⟨j, by omega,
          Array.getElem!_set!_ne out write j nums[i]! (by omega)⟩
      · exact ⟨write, by omega, Array.getElem!_set!_self out write nums[i]! hw⟩
    · rintro ⟨j, hj, hval⟩
      by_cases hjeq : j = write
      · subst j
        right
        rw [Array.getElem!_set!_self out write nums[i]! hw] at hval
        exact hval
      · left
        refine ⟨j, by omega, ?_⟩
        rw [Array.getElem!_set!_ne out write j nums[i]! (Ne.symm hjeq)] at hval
        exact hval
  case first_occurrences =>
    rename_i nums
    unfold LastWritten at last_written
    have hw : write < out.size := by omega
    have hle : last ≤ nums[i]! := by
      rw [last_written.2.2.2.2.1]
      exact sortedLe_of_lt nums sorted (by omega) scanning
    have hlt : last < nums[i]! := lt_of_le_of_ne hle (Ne.symm repeated)
    unfold OccursFirstBefore at first_occurrences ⊢
    rcases first_occurrences with ⟨f, hf, hmono, hfirst⟩
    let g : Nat → Nat := fun j => if j = write then i else f j
    refine ⟨g, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjeq : j = write
      · subst j
        refine ⟨?_, ?_⟩
        · simp [g]
        · rw [Array.getElem!_set!_self out write nums[i]! hw]
          simp [g]
      · have hfj := hf j (by omega)
        refine ⟨?_, ?_⟩
        · simp [g, hjeq]
          omega
        · rw [Array.getElem!_set!_ne out write j nums[i]! (Ne.symm hjeq)]
          simpa [g, hjeq] using hfj.2
    · intro j k hjk hk
      by_cases hkeq : k = write
      · subst k
        have hfj := hf j (by omega)
        simp [g, show j ≠ write by omega]
        omega
      · have hjw : j ≠ write := by omega
        simp [g, hkeq, hjw]
        exact hmono j k hjk (by omega)
    · intro j hj k hk
      by_cases hjeq : j = write
      · subst j
        have hki : k < i := by simpa [g] using hk
        have hki' : k < nums.size := lt_trans hki scanning
        have hki1 : k < i - 1 ∨ k = i - 1 := by omega
        rw [Array.getElem!_set!_self out write nums[i]! hw]
        intro heq
        have hki_le : nums[k]! ≤ last := by
          rw [last_written.2.2.2.2.1]
          rcases hki1 with h | h
          · exact sortedLe_of_lt nums sorted h (by omega)
          · subst k; exact le_rfl
        omega
      · have hjw : j < write := by omega
        have hold := hfirst j hjw k
        simp [g, hjeq] at hk
        rw [Array.getElem!_set!_ne out write j nums[i]! (Ne.symm hjeq)]
        exact hold hk
  case last_written =>
    rename_i nums
    unfold LastWritten at last_written ⊢
    have hw : write < out.size := by omega
    refine ⟨by omega, by omega, by omega, by omega, by simp, ?_⟩
    exact (Array.getElem!_set!_self out write nums[i]! hw).symm

end Proof

end RemoveDuplicatesFromSortedArray
