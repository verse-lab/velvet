module

public import Velvet.Examples.Loops
public meta import Velvet.Examples.Loops

/-!
# Loop examples — explicit VC discharge

Same contracts as `Loops.lean`, but each verification condition is discharged by
name (`case … => grind`) instead of the `finish` discharger, after stating its goal with
`show`. If `velvet_vcgen` ever renames, reorders or reshapes its VCs, these proofs fail and
catch the regression.
-/

set_option maxHeartbeats 10000000

theorem isGreaterInlineAnnotations_explicit : isGreaterInlineAnnotations.spec_triple := by
  unfold isGreaterInlineAnnotations.spec_triple
  velvet_vcgen [isGreaterInlineAnnotations]
  case idx_nonneg =>
    show
      0 ≤ 0
    grind
  case idx_bounded =>
    rename_i n a
    show
      0 ≤ a.size
    grind
  case ok_iff_prefix =>
    rename_i n a
    show
      true = true ↔ ∀ (j : Nat), j < 0 → a[j]! < n
    grind
  case postcond =>
    rename_i n a
    show
      ok = true ↔ ∀ (i : Nat), i < a.size → a[i]! < n
    grind
  case by_size =>
    rename_i n a
    show
      a.size - (i + 1) < a.size - i
    grind
  case idx_nonneg =>
    show
      0 ≤ i + 1
    grind
  case idx_bounded =>
    rename_i n a
    show
      i + 1 ≤ a.size
    grind
  case ok_iff_prefix =>
    rename_i n a
    show
      ok = true ↔ ∀ (j : Nat), j < i + 1 → a[j]! < n
    grind
  case by_size =>
    rename_i n a
    show
      a.size - (i + 1) < a.size - i
    grind
  case idx_nonneg =>
    show
      0 ≤ i + 1
    grind
  case idx_bounded =>
    rename_i n a
    show
      i + 1 ≤ a.size
    grind
  case ok_iff_prefix =>
    rename_i n a
    show
      false = true ↔ ∀ (j : Nat), j < i + 1 → a[j]! < n
    grind
  case idx_nonneg =>
    show
      0 ≤ i
    grind
  case idx_bounded =>
    rename_i n a
    show
      i ≤ a.size
    grind
  case ok_iff_prefix =>
    rename_i n a
    show
      ok = true ↔ ∀ (j : Nat), j < i → a[j]! < n
    grind
  case loop_done =>
    rename_i n a
    show
      a.size ≤ i
    grind

theorem sumDoubleRange_explicit : sumDoubleRange.spec_triple := by
  unfold sumDoubleRange.spec_triple
  velvet_vcgen [sumDoubleRange]
  case result_even =>
    show
      acc % 2 = 0
    grind
  case accumulator_even =>
    show
      (acc + 2 * i) % 2 = 0
    grind

theorem boundedRangeValues_explicit : boundedRangeValues.spec_triple := by
  unfold boundedRangeValues.spec_triple
  velvet_vcgen [boundedRangeValues]
  case last_nonnegative =>
    show
      0 ≤ 0
    grind
  case result_nonnegative =>
    show
      0 ≤ last
    grind
  case last_nonnegative =>
    show
      0 ≤ i
    grind

theorem twoVar_explicit : twoVar.spec_triple := by
  unfold twoVar.spec_triple
  velvet_vcgen [twoVar]
  case d =>
    rename_i n
    show
      0 = n ∧ 0 = n
    grind
  case xy =>
    show
      0 = i ∧ 0 = i
    rw [Std.Internal.ForIn.toList_list] at h_nonempty
    have := list_range_head h_nonempty
    omega
  case r_eq =>
    rename_i n
    show
      x = n
    grind
  case xy =>
    show
      x + 1 = next ∧ y + 1 = next
    rw [Std.Internal.ForIn.toList_list] at h_prefix
    have := list_range_next h_prefix
    omega
  case d =>
    rename_i n
    show
      x + 1 = n ∧ y + 1 = n
    rw [Std.Internal.ForIn.toList_list] at h_prefix
    have := list_range_last h_prefix
    omega

theorem sumList_explicit : sumList.spec_triple := by
  unfold sumList.spec_triple
  velvet_vcgen [sumList]
  case s_nonneg =>
    show
      0 ≤ 0
    grind
  case sum_nonneg =>
    show
      0 ≤ s
    grind
  case s_nonneg =>
    show
      0 ≤ s + x
    grind

theorem memberElementBound_explicit : memberElementBound.spec_triple := by
  unfold memberElementBound.spec_triple
  velvet_vcgen [memberElementBound]
  case nonneg =>
    show
      0 ≤ 0
    grind
  case sum_nonneg =>
    show
      0 ≤ s
    grind
  case h_in =>
    rename_i xs bound
    show
      x ∈ xs
    grind
  case nonneg =>
    show
      0 ≤ s + x
    grind

theorem isGreaterWithInvariants'_explicit : isGreaterWithInvariants'.spec_triple := by
  unfold isGreaterWithInvariants'.spec_triple
  velvet_vcgen [isGreaterWithInvariants']
  case size_gt_0 =>
    rename_i n a
    show
      0 < a.size
    grind
  case termination_semantics =>
    show
      False
    grind
  case ensures1 =>
    rename_i n a a_1
    show
      a_1 = true ↔ ∀ (i : Nat), i < a.size → a[i]! < n
    grind

theorem partialCount_explicit : partialCount.spec_triple := by
  unfold partialCount.spec_triple
  velvet_vcgen [partialCount]
  case i_le =>
    rename_i n
    show
      0 ≤ n
    grind
  case remaining =>
    rename_i n
    show
      n - (i + 1) < n - i
    grind
  case i_le =>
    rename_i n
    show
      i + 1 ≤ n
    grind
  case ensures1 =>
    rename_i n
    show
      i = n
    grind

theorem partialCountNoMeasure_explicit : partialCountNoMeasure.spec_triple := by
  unfold partialCountNoMeasure.spec_triple
  velvet_vcgen [partialCountNoMeasure]
  case i_le =>
    rename_i n
    show
      0 ≤ n
    grind
  case i_le =>
    rename_i n
    show
      i + 1 ≤ n
    grind
  case ensures1 =>
    rename_i n
    show
      i = n
    grind

theorem partialTick_explicit : partialTick.spec_triple := by
  unfold partialTick.spec_triple
  velvet_vcgen [partialTick]
  case i_nonneg =>
    show
      0 ≤ 0
    grind
  case i_nonneg =>
    show
      0 ≤ i + 1
    grind

