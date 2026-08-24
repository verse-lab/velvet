import Velvet2.Examples.StateT

/-!
# StateT examples — explicit VC discharge

Same contracts as `StateT.lean`, but each verification condition is discharged by
name (`case … => …`) instead of the `finish` discharger, to catch VC-name/restructure
regressions in `vcgen_`.
-/

open Std.Internal.Do

namespace Velvet2.Examples.StateT

theorem countState_explicit : countState.spec_triple := by
  unfold countState.spec_triple
  vcgen_ [countState]
  case state_tracks => grind
  case ensures1 => grind
  case by_remaining => grind
  case state_tracks => grind
  case state_tracks => grind
  case state_done => grind

theorem boundedIncrement_explicit (limit : Nat) :
    Triple (boundedIncrement limit) (fun s => s < limit)
      (fun current s => current < limit ∧ s = current + 1) True := by
  vcgen_ [boundedIncrement]
  case within_limit => grind
  case vc2 => grind

theorem countRange_explicit (n : Nat) :
    Triple (countRange n) (fun _ => True) (fun r s => r = n ∧ s = n) True := by
  vcgen_ [countRange]
  case count_done => grind
  case count_tracks =>
    rename_i s cur rest h
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_head h
    omega
  case vc3 => grind
  case count_tracks =>
    rename_i s pref cur next rest h b s'
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_next h
    omega
  case count_done =>
    rename_i s pref cur h b s'
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_last h
    omega

theorem checkedAdd_explicit : checkedAdd.spec_triple := by
  unfold checkedAdd.spec_triple
  vcgen_ [checkedAdd]
  case positive_delta => grind

theorem countUnlessBlocked_explicit : countUnlessBlocked.spec_triple := by
  unfold countUnlessBlocked.spec_triple
  vcgen_ [countUnlessBlocked]
  case progress => grind
  case ensures1 => grind
  case remaining => grind
  case progress => grind
  case progress => grind
  case reached_target => grind

theorem countToReaderLimit_explicit :
    Triple countToReaderLimit (fun state limit => state ≤ limit)
      (fun result state limit => result = limit ∧ state = limit) (⟨⟩ : EPost.Nil) := by
  vcgen_ [countToReaderLimit]
  case initial_bound => grind
  case reader_progress => grind
  case vc3 => grind
  case reader_remaining => grind
  case reader_progress => grind
  case reader_progress => grind
  case reader_done => grind

theorem countToReaderLimitMethod_explicit : countToReaderLimitMethod.spec_triple := by
  unfold countToReaderLimitMethod.spec_triple
  vcgen_ [countToReaderLimitMethod]

theorem addToReaderLimit_explicit :
    Triple addToReaderLimit (fun initial limit => initial ≤ limit)
      (fun initial final limit => initial ≤ limit ∧ final = initial + triangular limit)
      (⟨⟩ : EPost.Nil) := by
  vcgen_ [addToReaderLimit]
  all_goals try simp_all [triangular]
  all_goals try simp_all
  case accumulated_sum =>
    constructor
    · simp [Nat.add_assoc]
    · omega
  case additions_remaining => grind
  case all_added => grind

theorem countStatePartial_explicit : countStatePartial.spec_triple := by
  unfold countStatePartial.spec_triple
  vcgen_ [countStatePartial]
  all_goals grind

end Velvet2.Examples.StateT
