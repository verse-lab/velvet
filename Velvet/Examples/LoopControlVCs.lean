module

public import Velvet.Examples.LoopControl
public meta import Velvet.Examples.LoopControl

/-!
# Loop control flow: verification conditions

The verification conditions `velvet_vcgen` produces for the methods in `LoopControl.lean`, in
order, each with its goal pinned by `show`. If `velvet_vcgen` changes how many VCs a loop
produces, what they are called, or what they ask for, these fail.
-/

namespace Velvet.Examples.LoopControl

example : breakAtFive.spec_triple := by
  unfold breakAtFive.spec_triple
  intro n
  velvet_vcgen [breakAtFive]
  case bound =>
    show
      0 ≤ n
    grind
  case res_le =>
    show
      i ≤ n
    grind
  case termination =>
    show
      n - (i + 1) < n - i
    grind
  case bound =>
    show
      i + 1 ≤ n
    grind
  case res_le =>
    show
      i ≤ n
    grind

example : twoBreaks.spec_triple := by
  unfold twoBreaks.spec_triple
  intro n
  velvet_vcgen [twoBreaks]
  case bound =>
    show
      0 ≤ n
    grind
  case res_le =>
    show
      i + 1 ≤ n + 1
    grind
  case res_le =>
    show
      i + 1 ≤ n + 1
    grind
  case termination =>
    show
      n - (i + 1) < n - i
    grind
  case bound =>
    show
      i + 1 ≤ n
    grind
  case res_le =>
    show
      i + 1 ≤ n + 1
    grind

example : countToTen.spec_triple := by
  unfold countToTen.spec_triple
  intro a
  velvet_vcgen [countToTen]
  case progress =>
    show
      0 + a = a
    grind
  case below =>
    show
      0 < 10
    grind
  case res_min =>
    show
      x + 1 = min a 10
    grind
  case progress =>
    show
      x + 1 + (t - 1) = a
    grind
  case below =>
    show
      x + 1 < 10
    grind
  case res_min =>
    show
      x = min a 10
    grind

example : skipEvens.spec_triple := by
  unfold skipEvens.spec_triple
  intro a
  velvet_vcgen [skipEvens]
  case progress =>
    show
      0 + a = a
    grind
  case res_eq =>
    show
      x = a
    grind
  case progress =>
    show
      x + t = a
    grind
  case progress =>
    show
      x + 1 + (t - 1) = a
    grind
  case progress =>
    show
      x + t = a
    grind
  case done =>
    show
      t = 0
    grind

example : findZero.spec_triple := by
  unfold findZero.spec_triple
  intro xs
  velvet_vcgen [findZero]
  case bound =>
    show
      0 ≤ xs.size
    grind
  case found =>
    show
      i < xs.size ∧ xs[i]! = 0
    grind
  case termination =>
    show
      xs.size - (i + 1) < xs.size - i
    grind
  case bound =>
    show
      i + 1 ≤ xs.size
    grind

example : findZeroDone.spec_triple := by
  unfold findZeroDone.spec_triple
  intro xs
  velvet_vcgen [findZeroDone]
  case bound =>
    show
      0 ≤ xs.size
    grind
  case found =>
    show
      i < xs.size ∧ xs[i]! = 0
    grind
  case bound =>
    show
      i ≤ xs.size
    grind
  case fin =>
    show
      i ≤ xs.size
    grind
  case termination =>
    show
      xs.size - (i + 1) < xs.size - i
    grind
  case bound =>
    show
      i + 1 ≤ xs.size
    grind
  case bound =>
    show
      i ≤ xs.size
    grind
  case fin =>
    show
      i ≤ xs.size
    grind

example : findZeroPartial.spec_triple := by
  unfold findZeroPartial.spec_triple
  intro xs
  velvet_vcgen [findZeroPartial]
  case bound =>
    show
      0 ≤ xs.size
    grind
  case found =>
    show
      i < xs.size ∧ xs[i]! = 0
    grind
  case bound =>
    show
      i + 1 ≤ xs.size
    grind

example : searchArray.spec_triple := by
  unfold searchArray.spec_triple
  intro a target
  velvet_vcgen [searchArray]
  case i_le =>
    show
      0 ≤ a.size
    grind
  case not_before =>
    show
      ∀ (j : Nat), j < 0 → ¬a[j]! = target
    grind
  case found_iff =>
    show
      true = true ↔ ∃ j, j < a.size ∧ a[j]! = target
    grind
  case i_le =>
    show
      i + 1 ≤ a.size
    grind
  case not_before =>
    show
      ∀ (j : Nat), j < i + 1 → ¬a[j]! = target
    grind
  case i_le =>
    show
      i ≤ a.size
    grind
  case not_before =>
    show
      ∀ (j : Nat), j < i → ¬a[j]! = target
    grind
  case all_checked =>
    show
      i = a.size
    grind
  case found_iff =>
    show
      false = true ↔ ∃ j, j < a.size ∧ a[j]! = target
    grind

example : nestedDoReturn.spec_triple := by
  unfold nestedDoReturn.spec_triple
  intro xs
  velvet_vcgen [nestedDoReturn]
  case bound =>
    show
      0 ≤ xs.size
    grind
  case res_cases =>
    show
      i = xs.size ∨ i < xs.size ∧ xs[i]! = 0
    grind
  case termination =>
    show
      xs.size - (i + 1) < xs.size - i
    grind
  case bound =>
    show
      i + 1 ≤ xs.size
    grind
  case res_cases =>
    show
      i = xs.size ∨ i < xs.size ∧ xs[i]! = 0
    grind
  case termination =>
    show
      xs.size - (i + 1) < xs.size - i
    grind
  case bound =>
    show
      i + 1 ≤ xs.size
    grind
  case res_cases =>
    show
      xs.size = xs.size ∨ xs.size < xs.size ∧ xs[xs.size]! = 0
    grind

example : seqLoops.spec_triple := by
  unfold seqLoops.spec_triple
  intro n
  velvet_vcgen [seqLoops]
  case b1 =>
    show
      0 ≤ n
    grind
  case b2 =>
    show
      0 ≤ n ∧ 0 ≤ 0
    grind
  case res_le =>
    show
      i + acc ≤ 2 * n
    grind
  case termination =>
    show
      n - (j + 1) < n - j
    grind
  case b2 =>
    show
      j + 1 ≤ n ∧ acc + 1 ≤ j + 1
    grind
  case res_le =>
    show
      i + acc ≤ 2 * n
    grind
  case termination =>
    show
      n - (i + 1) < n - i
    grind
  case b1 =>
    show
      i + 1 ≤ n
    grind
  case b2 =>
    show
      0 ≤ n ∧ 0 ≤ 0
    grind
  case res_le =>
    show
      i + acc ≤ 2 * n
    grind
  case termination =>
    show
      n - (j + 1) < n - j
    grind
  case b2 =>
    show
      j + 1 ≤ n ∧ acc + 1 ≤ j + 1
    grind
  case res_le =>
    show
      i + acc ≤ 2 * n
    grind

example : nestedFind.spec_triple := by
  unfold nestedFind.spec_triple
  intro xs
  velvet_vcgen [nestedFind]
  case bi =>
    show
      0 ≤ xs.size
    grind
  case bj =>
    show
      0 ≤ xs[i]!.size
    grind
  case found =>
    show
      i < xs.size ∧ j < xs[i]!.size ∧ xs[i]![j]! = 0
    grind
  case termination =>
    show
      xs.size - (i + 1) < xs.size - i
    grind
  case bi =>
    show
      i + 1 ≤ xs.size
    grind
  case termination =>
    show
      xs[i]!.size - (j + 1) < xs[i]!.size - j
    grind
  case bj =>
    show
      j + 1 ≤ xs[i]!.size
    grind
  case termination =>
    show
      xs.size - (i + 1) < xs.size - i
    grind
  case bi =>
    show
      i + 1 ≤ xs.size
    grind

example : findFirstPositive.spec_triple := by
  unfold findFirstPositive.spec_triple
  intro xs
  velvet_vcgen [findFirstPositive]
  case res_pos =>
    show
      ∀ (v : Int), some x = some v → 0 < v ∧ v ∈ xs
    grind
  case none_yet =>
    show
      found = none
    grind
  case res_pos =>
    show
      ∀ (v : Int), found = some v → 0 < v ∧ v ∈ xs
    grind

example : sumPositives.spec_triple := by
  unfold sumPositives.spec_triple
  intro xs
  velvet_vcgen [sumPositives]
  case s_nonneg =>
    show
      0 ≤ 0
    grind
  case s_nonneg =>
    show
      0 ≤ s
    grind
  case s_nonneg =>
    show
      0 ≤ s + x
    grind
  case sum_nonneg =>
    show
      0 ≤ s
    grind

example : forReturn.spec_triple := by
  unfold forReturn.spec_triple
  intro xs
  velvet_vcgen [forReturn]
  case seen_le =>
    show
      0 ≤ xs.length
    grind
  case res_cases =>
    show
      x = 0 ∨ 5 < x
    grind
  case seen_le =>
    show
      seen + 1 ≤ xs.length
    grind
  case seen_le =>
    show
      seen ≤ xs.length
    grind
  case res_cases =>
    show
      0 = 0 ∨ 5 < 0
    grind

example : containsZero.spec_triple := by
  unfold containsZero.spec_triple
  intro xs
  velvet_vcgen [containsZero]
  case all_checked =>
    show
      ∀ (y : Nat), y ∈ [] → ¬y = 0
    grind
  case none_yet =>
    show
      ∀ (y : Nat), y ∈ [] → ¬y = 0
    grind
  case found_iff =>
    show
      true = true ↔ 0 ∈ xs
    grind
  case none_yet =>
    show
      ∀ (y : Nat), y ∈ pref ++ [x] → ¬y = 0
    grind
  case found_iff =>
    show
      true = true ↔ 0 ∈ xs
    grind
  case all_checked =>
    show
      ∀ (y : Nat), y ∈ ForIn.toList xs → ¬y = 0
    grind
  case found_iff =>
    show
      false = true ↔ 0 ∈ xs
    grind

example : forDoneReturn.spec_triple := by
  unfold forDoneReturn.spec_triple
  intro n
  velvet_vcgen [forDoneReturn]
  case fin =>
    show
      0 ≤ n
    grind
  case s_le =>
    show
      0 ≤ [].length
    grind
  case res_le =>
    show
      i ≤ n
    grind
  case s_le =>
    show
      s + 1 ≤ (pref ++ [i]).length
    grind
  case res_le =>
    show
      i ≤ n
    grind
  case fin =>
    show
      s + 1 ≤ n
    grind
  case res_le =>
    show
      s ≤ n
    grind

example : forPlainReturn.spec_triple := by
  unfold forPlainReturn.spec_triple
  intro xs
  velvet_vcgen [forPlainReturn]
  case res_cases =>
    show
      0 = 0 ∨ 5 < 0
    grind
  case res_cases =>
    rename_i a
    show
      x = 0 ∨ 5 < x
    grind
  case res_cases =>
    rename_i a
    show
      0 = 0 ∨ 5 < 0
    grind

example : forPlainBreak.spec_triple := by
  unfold forPlainBreak.spec_triple
  intro xs
  velvet_vcgen [forPlainBreak]
  case res_cases =>
    show
      0 = 0 ∨ 5 < 0
    grind
  case res_cases =>
    show
      0 = 0 ∨ 5 < 0
    grind
  case res_cases =>
    rename_i b
    show
      x = 0 ∨ 5 < x
    grind
  case res_cases =>
    rename_i b
    show
      0 = 0 ∨ 5 < 0
    grind
  case res_cases =>
    rename_i b
    show
      b = 0 ∨ 5 < b
    grind
  case res_cases =>
    rename_i b
    show
      0 = 0 ∨ 5 < 0
    grind

end Velvet.Examples.LoopControl
