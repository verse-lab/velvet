import Velvet.Examples.Loops

/-!
# Loop examples — explicit VC discharge

Same contracts as `Loops.lean`, but each verification condition is discharged by
name (`case … => grind`) instead of the `finish` discharger. If `vcgen_` ever renames
or restructures its VCs, these proofs fail and catch the regression.
-/

set_option maxHeartbeats 10000000

theorem isGreaterInlineAnnotations_explicit : isGreaterInlineAnnotations.spec_triple := by
  unfold isGreaterInlineAnnotations.spec_triple
  vcgen_ [isGreaterInlineAnnotations]
  case idx_nonneg => grind
  case idx_bounded => grind
  case ok_iff_prefix => grind
  case postcond => grind
  case by_size => grind
  case idx_nonneg => grind
  case idx_bounded => grind
  case ok_iff_prefix => grind
  case by_size => grind
  case idx_nonneg => grind
  case idx_bounded => grind
  case ok_iff_prefix => grind
  case idx_nonneg => grind
  case idx_bounded => grind
  case ok_iff_prefix => grind
  case loop_done => grind

theorem sumDoubleRange_explicit : sumDoubleRange.spec_triple := by
  unfold sumDoubleRange.spec_triple
  vcgen_ [sumDoubleRange]
  case result_even => grind
  case accumulator_even => grind

theorem boundedRangeValues_explicit : boundedRangeValues.spec_triple := by
  unfold boundedRangeValues.spec_triple
  vcgen_ [boundedRangeValues]
  case last_nonnegative => grind
  case result_nonnegative => grind
  case last_nonnegative => grind

theorem twoVar_explicit : twoVar.spec_triple := by
  unfold twoVar.spec_triple
  vcgen_ [twoVar]
  case d => grind
  case xy =>
    rename_i b
    rw [Std.Internal.ForIn.toList_list] at b
    have := list_range_head b
    omega
  case r_eq => grind
  case xy =>
    rename_i b
    rw [Std.Internal.ForIn.toList_list] at b
    have := list_range_next b
    omega
  case d =>
    rename_i b
    rw [Std.Internal.ForIn.toList_list] at b
    have := list_range_last b
    omega

theorem sumList_explicit : sumList.spec_triple := by
  unfold sumList.spec_triple
  vcgen_ [sumList]
  case s_nonneg => grind
  case sum_nonneg => grind
  case s_nonneg => grind

theorem memberElementBound_explicit : memberElementBound.spec_triple := by
  unfold memberElementBound.spec_triple
  vcgen_ [memberElementBound]
  case nonneg => grind
  case sum_nonneg => grind
  case h_in => grind
  case nonneg => grind

theorem isGreaterWithInvariants'_explicit : isGreaterWithInvariants'.spec_triple := by
  unfold isGreaterWithInvariants'.spec_triple
  vcgen_ [isGreaterWithInvariants']
  case size_gt_0 => grind
  case termination_semantics => grind
  case ensures1 => grind

theorem partialCount_explicit : partialCount.spec_triple := by
  unfold partialCount.spec_triple
  vcgen_ [partialCount]
  case i_le => grind
  case ensures1 => grind
  case remaining => grind
  case i_le => grind
  case i_le => grind
  case h_done_with => grind

theorem partialCountNoMeasure_explicit : partialCountNoMeasure.spec_triple := by
  unfold partialCountNoMeasure.spec_triple
  vcgen_ [partialCountNoMeasure]
  case i_le => grind
  case ensures1 => grind
  case i_le => grind
  case i_le => grind
  case h_done_with => grind

theorem partialTick_explicit : partialTick.spec_triple := by
  unfold partialTick.spec_triple
  vcgen_ [partialTick]
  case i_nonneg => grind
  case i_nonneg => grind
