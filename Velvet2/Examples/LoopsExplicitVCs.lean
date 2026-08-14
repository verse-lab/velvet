import Velvet2.Examples.Loops

/-!
# Loop examples — explicit VC discharge

Same contracts as `Loops.lean`, but each verification condition is discharged by
name (`case … => grind`) instead of the `finish` discharger. If `vcgen_` ever renames
or restructures its VCs, these proofs fail and catch the regression.
-/

set_option maxHeartbeats 10000000

theorem isGreaterNativeWhile_correct_explicit (n : Int) (a : Array Int) :
    Std.Internal.Do.Triple (isGreaterNativeWhile n a)
      (Named.mk `precond Option.none True)
      (Named.mk `postcond Option.none (fun result => result = true ↔ ∀ i, i < a.size → a[i]! < n))
      True := by
  vcgen_ [isGreaterNativeWhile] invariants
  · fun
    | .inl b =>
        Named.mk `idx_nonneg Option.none (0 ≤ b.snd) ∧
        Named.mk `idx_bounded Option.none (b.snd ≤ a.size) ∧
        Named.mk `ok_iff_prefix Option.none
          (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)
    | .inr b =>
        (Named.mk `idx_nonneg Option.none (0 ≤ b.snd) ∧
         Named.mk `idx_bounded Option.none (b.snd ≤ a.size) ∧
         Named.mk `ok_iff_prefix Option.none
           (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)) ∧
        Named.mk `loop_done Option.none (a.size ≤ b.snd)
  · Std.Internal.Do.RepeatVariant.ofMeasure (Pred := Prop)
      (fun b => a.size - b.snd)
  case vc1 => grind
  case postcond => grind
  case vc3 => grind
  case vc4 => grind
  case vc5 => grind
  case vc6 => grind
  case vc7 => grind

theorem isGreaterInlineAnnotations_explicit : isGreaterInlineAnnotations.spec := by
  unfold isGreaterInlineAnnotations.spec
  vcgen_ [isGreaterInlineAnnotations]
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

theorem sumDoubleRange_explicit : sumDoubleRange.spec := by
  unfold sumDoubleRange.spec
  vcgen_ [sumDoubleRange]
  case result_even => grind
  case sum_done => grind
  case accumulator_even => grind

theorem boundedRangeValues_explicit : boundedRangeValues.spec := by
  unfold boundedRangeValues.spec
  vcgen_ [boundedRangeValues]
  case result_nonnegative => grind
  case last_done => grind
  case last_nonnegative => grind

theorem isGreaterWithInvariants'_explicit : isGreaterWithInvariants'.spec := by
  unfold isGreaterWithInvariants'.spec
  vcgen_ [isGreaterWithInvariants']
  case size_gt_0 => grind
  case signals1 => grind
  case ensures1 => grind
