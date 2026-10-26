module

public import Velvet.Examples.NonDet
public meta import Velvet.Examples.NonDet

/-!
# Non-deterministic loops: verification conditions

The verification conditions `velvet_vcgen` produces for the loops in section 6 of `NonDet.lean`,
one for each `while` spec over `NonDetT`, in order, each with its goal pinned by `show`. If
`velvet_vcgen` changes how many VCs a loop produces, what they are called, or what they ask for,
these fail.
-/

namespace Velvet.Examples.NonDet

example : batchedRead.spec_triple := by
  unfold batchedRead.spec_triple
  intro n
  velvet_vcgen [batchedRead]
  case progress =>
    show
      0 + n ≤ n
    grind
  case signals1 =>
    rename_i a
    show
      False
    grind
  case termination =>
    rename_i i
    show
      left - min i.val left < left
    grind
  case progress =>
    rename_i i
    show
      reads + 1 + (left - min i.val left) ≤ n
    grind
  case at_most_n =>
    show
      reads ≤ n
    grind

example : chunkedSend.spec_triple := by
  unfold chunkedSend.spec_triple
  intro total
  velvet_vcgen [chunkedSend]
  case sent_le =>
    show
      0 ≤ total
    grind
  case all_sent =>
    show
      sent = total
    grind
  case signals1 =>
    rename_i a
    show
      False
    grind
  case termination =>
    rename_i i
    show
      total - (sent + min i.val (total - sent)) < total - sent
    grind
  case sent_le =>
    rename_i i
    show
      sent + min i.val (total - sent) ≤ total
    grind
  case sent_le =>
    show
      sent ≤ total
    grind
  case finished =>
    show
      sent = total
    grind

example : retry.spec_triple := by
  unfold retry.spec_triple
  intro maxAttempts
  velvet_vcgen [retry]
  case bound =>
    show
      0 ≤ maxAttempts
    grind
  case signals1 =>
    rename_i a
    show
      False
    grind
  case within_budget =>
    rename_i i
    show
      ∀ (k : Nat), some attempt = some k → k < maxAttempts
    grind
  case termination =>
    rename_i i
    show
      maxAttempts - (attempt + 1) < maxAttempts - attempt
    grind
  case bound =>
    rename_i i
    show
      attempt + 1 ≤ maxAttempts
    grind
  case within_budget =>
    show
      ∀ (k : Nat), none = some k → k < maxAttempts
    grind

example : retryCount.spec_triple := by
  unfold retryCount.spec_triple
  intro maxAttempts
  velvet_vcgen [retryCount]
  case bound =>
    show
      0 ≤ maxAttempts
    grind
  case signals1 =>
    rename_i a
    show
      False
    grind
  case within_budget =>
    rename_i i
    show
      attempt + 1 ≤ maxAttempts
    grind
  case termination =>
    rename_i i
    show
      maxAttempts - (attempt + 1) < maxAttempts - attempt
    grind
  case bound =>
    rename_i i
    show
      attempt + 1 ≤ maxAttempts
    grind
  case bound =>
    show
      attempt ≤ maxAttempts
    grind
  case exhausted =>
    show
      attempt = maxAttempts
    grind
  case within_budget =>
    show
      attempt ≤ maxAttempts
    grind

set_option velvet.semantics.termination "partial" in
example : pollUntilReady.spec_triple := by
  unfold pollUntilReady.spec_triple
  velvet_vcgen [pollUntilReady]
  case counted =>
    show
      false = true → 1 ≤ 0
    grind
  case counted =>
    rename_i i
    show
      i.val = true → 1 ≤ polls + 1
    grind
  case polled =>
    show
      1 ≤ polls
    grind

set_option velvet.semantics.termination "partial" in
example : sampleAtLeast.spec_triple := by
  unfold sampleAtLeast.spec_triple
  intro t
  velvet_vcgen [sampleAtLeast]
  case accepted =>
    show
      t ≤ v
    grind
  case accepted =>
    show
      t ≤ x
    grind

set_option velvet.semantics.termination "partial" in
example : sampleAtLeastReturn.spec_triple := by
  unfold sampleAtLeastReturn.spec_triple
  intro t
  velvet_vcgen [sampleAtLeastReturn]
  case accepted =>
    rename_i i
    show
      t ≤ i.val
    grind
  case accepted =>
    show
      t ≤ t
    grind

set_option velvet.semantics.termination "partial" in
example : sampleInRange.spec_triple := by
  unfold sampleInRange.spec_triple
  velvet_vcgen [sampleInRange]
  case in_range =>
    rename_i lo hi i
    show
      lo ≤ lo ∧ lo ≤ hi
    grind
  case in_range =>
    rename_i lo hi
    show
      lo ≤ x ∧ x ≤ hi
    grind
  case in_range =>
    rename_i lo hi
    show
      lo ≤ v ∧ v ≤ hi
    grind

end Velvet.Examples.NonDet
