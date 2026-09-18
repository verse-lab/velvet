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

Return the number of set bits in the binary representation of a natural number `n`.

The program is expected to run in O(k) time and O(1) extra space, where k is the
number of set bits in `n`.
-/

namespace NumberOf1Bits

section Specs

public def precondition (_n : Nat) : Prop :=
  True

public def postcondition (n : Nat) (result : Nat) : Prop :=
  result = ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ∧
  result ≤ n.size

end Specs

section Implementation

method numberOf1Bits (n : Nat)
  returns (result : Nat)
  requires valid: precondition n
  ensures count_correct: postcondition n result
do
  let mut x := n
  let mut cnt : Nat := 0
  while clearing: x > 0
    invariant x_le: x ≤ n
    invariant cnt_plus_weight:
      cnt + ((Finset.range n.size).filter (fun (i : Nat) => x.testBit i = true)).card =
        ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card
    invariant cnt_le_size: cnt ≤ n.size
    decreasing remaining: x
    done_with done: x = 0
  do
    x := x &&& (x - 1)
    cnt := cnt + 1
  return cnt

end Implementation

section Proof

public def popcountUpTo (bnd : Nat) (x : Nat) : Nat :=
  ((Finset.range bnd).filter (fun k : Nat => x.testBit k = true)).card

theorem popcountUpTo_zero (x : Nat) : popcountUpTo 0 x = 0 := by
  simp [popcountUpTo]

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

theorem testBit_zero_two_mul_add_one (k : Nat) : (2 * k + 1).testBit 0 = true := by
  have : (2 * k + 1) % 2 = 1 := by omega
  exact (Nat.mod_two_eq_one_iff_testBit_zero).1 this

theorem testBit_zero_two_mul (k : Nat) : (2 * k).testBit 0 = false := by
  have : (2 * k) % 2 = 0 := by omega
  exact (Nat.mod_two_eq_zero_iff_testBit_zero).1 this

theorem testBit_succ_two_mul_add_one (k i : Nat) : (2 * k + 1).testBit (i + 1) = k.testBit i := by
  rw [Nat.testBit_add_one]
  have : (2 * k + 1) / 2 = k := by omega
  rw [this]

theorem testBit_succ_two_mul (k i : Nat) : (2 * k).testBit (i + 1) = k.testBit i := by
  rw [Nat.testBit_add_one]
  have : (2 * k) / 2 = k := by omega
  rw [this]

theorem and_sub_one_odd (k : Nat) : (2 * k + 1) &&& (2 * k) = 2 * k := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_land, testBit_zero_two_mul_add_one, testBit_zero_two_mul]
    rfl
  | succ j =>
    rw [Nat.testBit_land, testBit_succ_two_mul_add_one, testBit_succ_two_mul, Bool.and_self]

theorem and_sub_one_even (k : Nat) (hk : 0 < k) : (2 * k) &&& (2 * k - 1) = 2 * (k &&& (k - 1)) := by
  have hsub : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [hsub]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_land, testBit_zero_two_mul, testBit_zero_two_mul]
    rfl
  | succ j =>
    rw [Nat.testBit_land, testBit_succ_two_mul, testBit_succ_two_mul_add_one, testBit_succ_two_mul, Nat.testBit_land]

theorem popcountUpTo_and_sub_one (bnd x : Nat) (hx : 0 < x) (hbound : x < 2 ^ bnd) :
    popcountUpTo bnd x = popcountUpTo bnd (x &&& (x - 1)) + 1 := by
  induction x using Nat.strong_induction_on generalizing bnd with
  | h x ih =>
    have hbnd_pos : 0 < bnd := by
      by_contra h0
      have : bnd = 0 := by omega
      subst this
      have : x < 1 := hbound
      omega
    rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hbnd_pos) with ⟨b', rfl⟩
    rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
    · obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
      have hk_pos : 0 < k := by omega
      have hk_bound : k < 2 ^ b' := by
        have hpow : 2 ^ (b' + 1) = 2 * 2 ^ b' := by rw [Nat.pow_succ', Nat.mul_comm]
        omega
      have ih_k := ih k (by omega) b' hk_pos hk_bound
      have hand_even := and_sub_one_even k hk_pos
      have h1 : popcountUpTo (b' + 1) (2 * k) = popcountUpTo b' k := by
        rw [popcountUpTo_succ]
        have : (2 * k) / 2 = k := by omega
        have : (2 * k) % 2 = 0 := by omega
        rw [this, ‹(2 * k) / 2 = k›]
        omega
      have h2 : popcountUpTo (b' + 1) ((2 * k) &&& (2 * k - 1)) = popcountUpTo b' (k &&& (k - 1)) := by
        rw [hand_even, popcountUpTo_succ]
        have : (2 * (k &&& (k - 1))) / 2 = k &&& (k - 1) := by omega
        have : (2 * (k &&& (k - 1))) % 2 = 0 := by omega
        rw [this, ‹(2 * (k &&& (k - 1))) / 2 = k &&& (k - 1)›]
        omega
      rw [h1, h2, ih_k]
    · obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
      have hsub : 2 * k + 1 - 1 = 2 * k := by omega
      have hand_odd := and_sub_one_odd k
      have h1 : popcountUpTo (b' + 1) (2 * k + 1) = popcountUpTo b' k + 1 := by
        rw [popcountUpTo_succ]
        have : (2 * k + 1) / 2 = k := by omega
        have : (2 * k + 1) % 2 = 1 := by omega
        rw [this, ‹(2 * k + 1) / 2 = k›]
      have h2 : popcountUpTo (b' + 1) ((2 * k + 1) &&& (2 * k + 1 - 1)) = popcountUpTo b' k := by
        rw [hsub, hand_odd, popcountUpTo_succ]
        have : (2 * k) / 2 = k := by omega
        have : (2 * k) % 2 = 0 := by omega
        rw [this, ‹(2 * k) / 2 = k›]
        omega
      rw [h1, h2]

theorem popcountUpTo_zero_val (bnd : Nat) : popcountUpTo bnd 0 = 0 := by
  unfold popcountUpTo
  have : (Finset.range bnd).filter (fun k : Nat => (0 : Nat).testBit k = true) = ∅ := by
    ext k
    simp
  rw [this, Finset.card_empty]

theorem popcountUpTo_le_bnd (bnd x : Nat) : popcountUpTo bnd x ≤ bnd := by
  unfold popcountUpTo
  have : ((Finset.range bnd).filter (fun k : Nat => x.testBit k = true)).card ≤ (Finset.range bnd).card :=
    Finset.card_filter_le _ _
  simpa using this

theorem and_sub_one_lt (x : Nat) (hx : 0 < x) : x &&& (x - 1) < x := by
  have hle : x &&& (x - 1) ≤ x - 1 := Nat.and_le_right
  omega

theorem and_sub_one_le (x : Nat) : x &&& (x - 1) ≤ x := Nat.and_le_left

prove_correct numberOf1Bits by
  velvet_vcgen [numberOf1Bits, postcondition]
  case x_le => omega
  case cnt_plus_weight => omega
  case cnt_le_size => omega
  case count_correct =>
    rename_i n
    subst done
    unfold postcondition
    have hzero : ((Finset.range n.size).filter (fun (i : Nat) => (0 : Nat).testBit i = true)).card = 0 :=
      popcountUpTo_zero_val n.size
    omega
  case remaining =>
    exact and_sub_one_lt x clearing
  case x_le =>
    exact (and_sub_one_le x).trans x_le
  case cnt_plus_weight =>
    rename_i n
    have hbound : x < 2 ^ n.size := by
      have : n < 2 ^ n.size := Nat.lt_size_self n
      omega
    have hstep : popcountUpTo n.size x = popcountUpTo n.size (x &&& (x - 1)) + 1 :=
      popcountUpTo_and_sub_one n.size x clearing hbound
    unfold popcountUpTo at hstep
    omega
  case cnt_le_size =>
    rename_i n
    have hbound : x < 2 ^ n.size := by
      have : n < 2 ^ n.size := Nat.lt_size_self n
      omega
    have hstep : popcountUpTo n.size x = popcountUpTo n.size (x &&& (x - 1)) + 1 :=
      popcountUpTo_and_sub_one n.size x clearing hbound
    unfold popcountUpTo at hstep
    have htotal_le : ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ≤ n.size :=
      popcountUpTo_le_bnd n.size n
    omega
  case x_le => exact x_le
  case cnt_plus_weight => exact cnt_plus_weight
  case cnt_le_size => exact cnt_le_size
  case done => omega

end Proof

end NumberOf1Bits
