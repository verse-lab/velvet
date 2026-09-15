module

public import Velvet.Examples.StateT
public meta import Velvet.Examples.StateT

open Std.Internal.Do

/-!
# StateT examples — explicit VC discharge

Same contracts as `StateT.lean`, but each verification condition is discharged by
name (`case … => …`) instead of the `finish` discharger, to catch VC-name/restructure
regressions in `velvet_vcgen`.
-/

namespace Velvet.Examples.StateT

theorem countState_explicit : countState.spec_triple := by
  unfold countState.spec_triple
  velvet_vcgen [countState]
  case state_tracks => grind
  case ensures1 => grind
  case by_remaining => grind
  case state_tracks => grind
  case state_tracks => grind
  case state_done => grind

theorem boundedIncrement_explicit (limit : Nat) :
    Triple (boundedIncrement limit) (fun s => s < limit)
      (fun current s => current < limit ∧ s = current + 1) False := by
  velvet_vcgen [boundedIncrement]
  case within_limit => grind
  case vc2 => grind

theorem countRange_explicit (n : Nat) :
    Triple (countRange n) (fun _ => True) (fun r s => r = n ∧ s = n) False := by
  velvet_vcgen [countRange]
  case count_done => grind
  case count_tracks => grind
  case vc3 => grind
  case count_tracks => grind
  case count_done => grind

theorem checkedAdd_explicit : checkedAdd.spec_triple := by
  unfold checkedAdd.spec_triple
  velvet_vcgen [checkedAdd]
  case positive_delta => grind

theorem countUnlessBlocked_explicit : countUnlessBlocked.spec_triple := by
  unfold countUnlessBlocked.spec_triple
  velvet_vcgen [countUnlessBlocked]
  case progress => grind
  case ensures1 => grind
  case remaining => grind
  case progress => grind
  case progress => grind
  case reached_target => grind

theorem countToReaderLimit_explicit :
    Triple countToReaderLimit (fun state limit => state ≤ limit)
      (fun result state limit => result = limit ∧ state = limit) EPost.Nil.mk := by
  velvet_vcgen [countToReaderLimit]
  case initial_bound => grind
  case reader_progress => grind
  case vc3 => grind
  case reader_remaining => grind
  case reader_progress => grind
  case reader_progress => grind
  case reader_done => grind

theorem countToReaderLimitMethod_explicit : countToReaderLimitMethod.spec_triple := by
  unfold countToReaderLimitMethod.spec_triple
  velvet_vcgen [countToReaderLimitMethod]

theorem addToReaderLimit_explicit :
    Triple addToReaderLimit (fun initial limit => initial ≤ limit)
      (fun initial final limit => initial ≤ limit ∧ final = initial + triangular limit)
      EPost.Nil.mk := by
  velvet_vcgen [addToReaderLimit]
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
  velvet_vcgen [countStatePartial]
  all_goals grind

end Velvet.Examples.StateT
