module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Group.Nat.Range

/-!
## Program description

Given an integer `n`, return an array `ans` of length `n + 1` such that for each
`i` (`0 ≤ i ≤ n`), `ans[i]` is the number of `1`'s in the binary representation
of `i`.

The program is expected to run in O(n) time and O(n) space.
-/

namespace CountingBits

section Specs

public def popcountUpTo (bnd : Nat) (i : Nat) : Nat :=
  ((Finset.range bnd).filter (fun k : Nat => i.testBit k = true)).card

public def precondition (_n : Nat) : Prop :=
  True

public def postcondition (n : Nat) (ans : Array Nat) : Prop :=
  ans.size = n + 1 ∧
  (∀ (i : Nat), i < ans.size → ans[i]! = popcountUpTo (n + 1) i)

end Specs

section Implementation

method countingBits (n : Nat)
  returns (ans : Array Nat)
  requires valid: precondition n
  ensures count_correct: postcondition n ans
do
  let mut res : Array Nat := Array.replicate (n + 1) 0
  let mut i : Nat := 1
  while scanning: i < res.size
    invariant res_size: res.size = n + 1
    invariant i_bounds: 1 ≤ i ∧ i ≤ res.size
    invariant prefix_correct: ∀ k : Nat, k < i → res[k]! = popcountUpTo (n + 1) k
    decreasing remaining: res.size - i
    done_with done: i = res.size
  do
    let half : Nat := i / 2
    let bit : Nat := i % 2
    let v : Nat := res[half]! + bit
    res := res.set! i v
    i := i + 1
  return res

end Implementation

section Proof

theorem popcountUpTo_zero_val (bnd : Nat) : popcountUpTo bnd 0 = 0 := by
  unfold popcountUpTo
  have : (Finset.range bnd).filter (fun k : Nat => (0 : Nat).testBit k = true) = ∅ := by
    ext k
    simp
  rw [this, Finset.card_empty]

theorem popcountUpTo_succ (bnd x : Nat) :
    popcountUpTo (bnd + 1) x = popcountUpTo bnd (x / 2) + (x % 2) := by
  classical
  unfold popcountUpTo
  have hrange : Finset.range (bnd + 1) =
      Finset.range 1 ∪ (Finset.range bnd).map (addLeftEmbedding 1) := by
    rw [← Finset.range_add 1 bnd]
    congr 1
    omega
  rw [hrange, Finset.filter_union]
  have hdisj : Disjoint (Finset.range 1) ((Finset.range bnd).map (addLeftEmbedding 1)) := by
    exact Finset.disjoint_range_addLeftEmbedding 1 (Finset.range bnd)
  have hdisj' :
      Disjoint ((Finset.range 1).filter (fun k : Nat => x.testBit k = true))
        (((Finset.range bnd).map (addLeftEmbedding 1)).filter (fun k : Nat => x.testBit k = true)) :=
    Finset.disjoint_filter_filter (p := fun k : Nat => x.testBit k = true)
      (q := fun k : Nat => x.testBit k = true) hdisj
  rw [Finset.card_union_of_disjoint hdisj']
  have hr1 : Finset.range 1 = ({0} : Finset Nat) := rfl
  have hlsb : ((Finset.range 1).filter (fun k : Nat => x.testBit k = true)).card = x % 2 := by
    have hx : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    cases hx with
    | inl h0 =>
        have ht : x.testBit 0 = false := (Nat.mod_two_eq_zero_iff_testBit_zero).1 h0
        have : ({0} : Finset Nat).filter (fun k : Nat => x.testBit k = true) = ∅ := by
          ext k
          by_cases hk : k = 0
          · subst hk; simp [ht]
          · simp [hk]
        simp [hr1, this, h0]
    | inr h1 =>
        have ht : x.testBit 0 = true := (Nat.mod_two_eq_one_iff_testBit_zero).1 h1
        have : ({0} : Finset Nat).filter (fun k : Nat => x.testBit k = true) = {0} := by
          ext k
          by_cases hk : k = 0
          · subst hk; simp [ht]
          · simp [hk]
        simp [hr1, this, h1]
  have hrest :
      (((Finset.range bnd).map (addLeftEmbedding 1)).filter (fun k : Nat => x.testBit k = true)).card =
        ((Finset.range bnd).filter (fun k : Nat => (x / 2).testBit k = true)).card := by
    rw [Finset.filter_map]
    have hcard :
        (((Finset.range bnd).filter ((fun k : Nat => x.testBit k = true) ∘ (addLeftEmbedding 1))).map (addLeftEmbedding 1)).card =
          ((Finset.range bnd).filter ((fun k : Nat => x.testBit k = true) ∘ (addLeftEmbedding 1))).card := by
      exact Finset.card_map (addLeftEmbedding 1)
    rw [hcard]
    apply congrArg Finset.card
    ext k
    simp [Function.comp, Nat.testBit_add_one, Nat.add_comm]
  rw [hlsb, hrest]
  omega

theorem popcountUpTo_succ_of_testBit_false (n x : Nat) (hx : x.testBit n = false) :
    popcountUpTo (n + 1) x = popcountUpTo n x := by
  classical
  unfold popcountUpTo
  have hrange : Finset.range (n + 1) = insert n (Finset.range n) := Finset.range_add_one
  rw [hrange, Finset.filter_insert]
  simp [hx]

theorem popcountUpTo_recurrence (n i : Nat) (hi_le : i ≤ n) :
    popcountUpTo (n + 1) i = popcountUpTo (n + 1) (i / 2) + i % 2 := by
  have hhalf_lt_pow : i / 2 < 2 ^ n := by
    have h1 : i / 2 ≤ n := by omega
    have h2 : n < 2 ^ n := Nat.lt_two_pow_self
    omega
  have hbit_false : (i / 2).testBit n = false := Nat.testBit_eq_false_of_lt hhalf_lt_pow
  have hhalf_pop : popcountUpTo (n + 1) (i / 2) = popcountUpTo n (i / 2) :=
    popcountUpTo_succ_of_testBit_false n (i / 2) hbit_false
  rw [popcountUpTo_succ n i, hhalf_pop]

prove_correct countingBits by
  velvet_vcgen [countingBits, postcondition]
  case res_size => simp
  case i_bounds => simp
  case prefix_correct =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp [popcountUpTo_zero_val]
  case count_correct =>
    rename_i n
    subst done
    unfold postcondition
    refine ⟨res_size, ?_⟩
    intro k hk
    exact prefix_correct k (by omega)
  case remaining =>
    have : (res.set! i (res[i / 2]! + i % 2)).size = res.size := Array.size_set! res i (res[i / 2]! + i % 2)
    omega
  case res_size =>
    have : (res.set! i (res[i / 2]! + i % 2)).size = res.size := Array.size_set! res i (res[i / 2]! + i % 2)
    omega
  case i_bounds =>
    have : (res.set! i (res[i / 2]! + i % 2)).size = res.size := Array.size_set! res i (res[i / 2]! + i % 2)
    omega
  case prefix_correct =>
    rename_i n
    intro k hk
    by_cases hki : k = i
    · subst hki
      have hk_bound : k < res.size := scanning
      have hk_le : k ≤ n := by omega
      have hhalf_lt : k / 2 < k := by omega
      have hhalf_val : res[k / 2]! = popcountUpTo (n + 1) (k / 2) := prefix_correct (k / 2) hhalf_lt
      have hrec : popcountUpTo (n + 1) k = popcountUpTo (n + 1) (k / 2) + k % 2 :=
        popcountUpTo_recurrence n k hk_le
      rw [Array.getElem!_set!_self res k (res[k / 2]! + k % 2) hk_bound]
      rw [hhalf_val, hrec]
    · have hne : i ≠ k := Ne.symm hki
      rw [Array.getElem!_set!_ne res i k (res[i / 2]! + i % 2) hne]
      exact prefix_correct k (by omega)
  case res_size => exact res_size
  case i_bounds => exact i_bounds
  case prefix_correct => exact prefix_correct
  case done => omega

end Proof

end CountingBits
