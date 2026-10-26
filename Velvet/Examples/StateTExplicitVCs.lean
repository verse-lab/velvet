module

public import Velvet.Examples.StateT
public meta import Velvet.Examples.StateT

open Std.WP

/-!
# StateT examples — explicit VC discharge

Same contracts as `StateT.lean`, but each verification condition is discharged by
name (`case … => …`) instead of the `finish` discharger, after stating its goal with `show`,
to catch regressions in the names, order and shape of `velvet_vcgen`'s VCs.
-/

namespace Velvet.Examples.StateT

theorem countState_explicit : countState.spec_triple := by
  unfold countState.spec_triple
  velvet_vcgen [countState]
  case state_tracks =>
    rename_i n s
    show
      0 ≤ n
    grind
  case ensures1 =>
    rename_i n s s_1
    show
      i = n ∧ s_1 = n
    grind
  case by_remaining =>
    rename_i n s s_1
    show
      n - (i + 1) < n - i
    grind
  case state_tracks =>
    rename_i n s s_1
    show
      i + 1 ≤ n
    grind
  case state_tracks =>
    rename_i n s s_1
    show
      s_1 = i ∧ i ≤ n
    grind
  case state_done =>
    rename_i n s s_1
    show
      i = n ∧ s_1 = n
    grind

theorem boundedIncrement_explicit (limit : Nat) :
    Triple (boundedIncrement limit) (fun s => s < limit)
      (fun current s => current < limit ∧ s = current + 1) (fun _ => False) := by
  velvet_vcgen [boundedIncrement]
  case within_limit =>
    show
      current < limit
    grind
  case vc2 =>
    show
      current < limit
    grind

theorem countRange_explicit (n : Nat) :
    Triple (countRange n) (fun _ => True) (fun r s => r = n ∧ s = n) (fun _ => False) := by
  velvet_vcgen [countRange]
  -- Facts lifted from the loop's precondition are plain propositions, not `⌜p⌝ s`.
  case count_done =>
    show
      0 = n ∧ 0 = n
    guard_hyp h_empty : ForIn.toList (List.range n) = []
    grind
  case count_tracks =>
    show
      0 = i ∧ 0 = i
    guard_hyp h_nonempty : ForIn.toList (List.range n) = i :: rest
    grind
  case vc3 =>
    rename_i s s_1
    show
      count = n ∧ s_1 = n
    grind
  case count_tracks =>
    show
      i + 1 = next ∧ i + 1 = next
    grind
  case count_done =>
    show
      i + 1 = n ∧ i + 1 = n
    grind

theorem checkedAdd_explicit : checkedAdd.spec_triple := by
  unfold checkedAdd.spec_triple
  velvet_vcgen [checkedAdd]
  case positive_delta =>
    rename_i delta
    show
      0 < delta
    grind

theorem countUnlessBlocked_explicit : countUnlessBlocked.spec_triple := by
  unfold countUnlessBlocked.spec_triple
  velvet_vcgen [countUnlessBlocked]
  case progress =>
    rename_i target blocked s
    show
      0 ≤ target
    grind
  case ensures1 =>
    rename_i target blocked s s_1
    show
      i = target ∧ s_1 = target
    grind
  case remaining =>
    rename_i target blocked s s_1
    show
      target - (i + 1) < target - i
    grind
  case progress =>
    rename_i target blocked s s_1
    show
      i + 1 ≤ target
    grind
  case progress =>
    rename_i target blocked s s_1
    show
      s_1 = i ∧ i ≤ target
    grind
  case reached_target =>
    rename_i target blocked s s_1
    show
      i = target ∧ s_1 = target
    grind

theorem countToReaderLimit_explicit :
    Triple countToReaderLimit (fun state limit => state ≤ limit)
      (fun result state limit => result = limit ∧ state = limit) estack⟨⟩ := by
  velvet_vcgen [countToReaderLimit]
  case initial_bound =>
    show
      start ≤ limit
    grind
  case reader_progress =>
    show
      start ≤ limit
    grind
  case vc3 =>
    rename_i a s s_1
    show
      i = s_1 ∧ s = s_1
    grind
  case reader_remaining =>
    show
      limit - (i + 1) < limit - i
    grind
  case reader_progress =>
    rename_i a s s_1
    show
      s_1 = limit ∧ i + 1 ≤ limit
    grind
  case reader_progress =>
    rename_i a s s_1
    show
      s_1 = limit ∧ s = i ∧ i ≤ limit
    grind
  case reader_done =>
    rename_i a s s_1
    show
      s_1 = limit ∧ i = limit ∧ s = limit
    grind

theorem countToReaderLimitMethod_explicit : countToReaderLimitMethod.spec_triple := by
  unfold countToReaderLimitMethod.spec_triple
  velvet_vcgen [countToReaderLimitMethod]

theorem addToReaderLimit_explicit :
    Triple addToReaderLimit (fun initial limit => initial ≤ limit)
      (fun initial final limit => initial ≤ limit ∧ final = initial + triangular limit)
      estack⟨⟩ := by
  velvet_vcgen [addToReaderLimit]
  all_goals try simp_all [triangular]
  all_goals try simp_all
  case accumulated_sum =>
    show
      initial + triangular i + (i + 1) = initial + (triangular i + (i + 1)) ∧ i + 1 ≤ limit
    constructor
    · simp [Nat.add_assoc]
    · omega
  case additions_remaining =>
    show
      limit - (i + 1) < limit - i
    grind
  case all_added =>
    show
      i = limit ∧ triangular i = triangular limit
    grind

theorem countStatePartial_explicit : countStatePartial.spec_triple := by
  unfold countStatePartial.spec_triple
  velvet_vcgen [countStatePartial]
  case state_tracks =>
    rename_i n s
    show
      0 ≤ n
    grind
  case ensures1 =>
    rename_i n s s_1
    show
      i = n ∧ s_1 = n
    grind
  case state_tracks =>
    rename_i n s s_1
    show
      i + 1 ≤ n
    grind
  case state_tracks =>
    rename_i n s s_1
    show
      s_1 = i ∧ i ≤ n
    grind
  case state_done =>
    rename_i n s s_1
    show
      i = n ∧ s_1 = n
    grind

end Velvet.Examples.StateT
