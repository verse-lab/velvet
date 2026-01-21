import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000







def isCommonSubseq (s : List Int) (a : List Int) (b : List Int) : Prop :=
  s.Sublist a ∧ s.Sublist b


def isLCSLength (a : List Int) (b : List Int) (n : Nat) : Prop :=
  (∃ s : List Int, isCommonSubseq s a b ∧ s.length = n) ∧
  (∀ s : List Int, isCommonSubseq s a b → s.length ≤ n)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  isLCSLength a.toList b.toList result.toNat


def test1_a : Array Int := #[1, 2, 3]

def test1_b : Array Int := #[1, 2, 3]

def test1_Expected : Int := 3

def test2_a : Array Int := #[1, 3, 5, 7]

def test2_b : Array Int := #[1, 2, 3, 4, 5, 6, 7]

def test2_Expected : Int := 4

def test5_a : Array Int := #[1, 2, 3, 4]

def test5_b : Array Int := #[2, 4, 6, 8]

def test5_Expected : Int := 2







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition test1_a test1_b test1_Expected
  constructor
  · -- 3 ≥ 0
    omega
  · -- isLCSLength [1, 2, 3] [1, 2, 3] 3
    unfold isLCSLength
    constructor
    · -- existence: there exists a common subsequence of length 3
      use [1, 2, 3]
      constructor
      · -- [1, 2, 3] is a common subsequence
        unfold isCommonSubseq
        constructor
        · exact List.Sublist.refl _
        · exact List.Sublist.refl _
      · -- length is 3
        native_decide
    · -- maximality: all common subsequences have length ≤ 3
      intro s hs
      unfold isCommonSubseq at hs
      have h1 : s.Sublist [1, 2, 3] := hs.1
      have hlen : s.length ≤ [1, 2, 3].length := List.Sublist.length_le h1
      simp at hlen
      exact hlen

theorem test2_precondition :
  precondition test2_a test2_b := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  unfold postcondition test2_a test2_b test2_Expected
  constructor
  · omega
  · unfold isLCSLength
    constructor
    · -- Existence: [1, 3, 5, 7] is a common subsequence of length 4
      use [1, 3, 5, 7]
      constructor
      · unfold isCommonSubseq
        constructor
        · -- [1, 3, 5, 7] is sublist of [1, 3, 5, 7]
          exact List.Sublist.refl _
        · -- [1, 3, 5, 7] is sublist of [1, 2, 3, 4, 5, 6, 7]
          native_decide
      · native_decide
    · -- Maximality: any common subsequence has length ≤ 4
      intro s hs
      unfold isCommonSubseq at hs
      obtain ⟨ha, _⟩ := hs
      have h := List.Sublist.length_le ha
      simp at h
      exact h

theorem test5_precondition :
  precondition test5_a test5_b := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition_0
    (h_existence : ∃ s, isCommonSubseq s [1, 2, 3, 4] [2, 4, 6, 8] ∧ s.length = 2)
    (s : List ℤ)
    (ha : s.Sublist [1, 2, 3, 4])
    (hb : s.Sublist [2, 4, 6, 8])
    (h_nonneg : True)
    (h_witness : True)
    (h_sublist_a : True)
    (h_sublist_b : True)
    (h_len : True)
    (h_bound_a : s.length ≤ 4)
    (h_bound_b : s.length ≤ 4)
    (h_elements_from_a : ∀ x ∈ s, x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4)
    (h_elements_from_b : ∀ x ∈ s, x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8)
    : s.length ≤ 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  unfold postcondition test5_a test5_b test5_Expected
  have h_nonneg : (2 : Int) ≥ 0 := by (try simp at *; expose_names); exact Int.zero_le_ofNat 2; done
  have h_lcs : isLCSLength [1, 2, 3, 4] [2, 4, 6, 8] 2 := by
    unfold isLCSLength
    have h_witness : [2, 4] = [2, 4] := by (try simp at *; expose_names); exact rfl; done
    have h_sublist_a : ([2, 4] : List Int).Sublist [1, 2, 3, 4] := by (try simp at *; expose_names); exact (List.isSublist_iff_sublist.mp rfl); done
    have h_sublist_b : ([2, 4] : List Int).Sublist [2, 4, 6, 8] := by (try simp at *; expose_names); exact (List.isSublist_iff_sublist.mp rfl); done
    have h_len : ([2, 4] : List Int).length = 2 := by (try simp at *; expose_names); exact rfl; done
    have h_existence : ∃ s : List Int, isCommonSubseq s [1, 2, 3, 4] [2, 4, 6, 8] ∧ s.length = 2 := by
      use [2, 4]
      unfold isCommonSubseq
      exact ⟨⟨h_sublist_a, h_sublist_b⟩, h_len⟩
    have h_maximality : ∀ s : List Int, isCommonSubseq s [1, 2, 3, 4] [2, 4, 6, 8] → s.length ≤ 2 := by
      intro s hs
      unfold isCommonSubseq at hs
      obtain ⟨ha, hb⟩ := hs
      have h_bound_a : s.length ≤ [1, 2, 3, 4].length := List.Sublist.length_le ha
      have h_bound_b : s.length ≤ [2, 4, 6, 8].length := List.Sublist.length_le hb
      have h_elements_from_a : ∀ x, x ∈ s → x ∈ [1, 2, 3, 4] := fun x hx => ha.mem hx
      have h_elements_from_b : ∀ x, x ∈ s → x ∈ [2, 4, 6, 8] := fun x hx => hb.mem hx
      (try simp at *; expose_names); exact (test5_postcondition_0 h_existence s ha hb h_nonneg h_witness h_sublist_a h_sublist_b h_len h_bound_a h_bound_b h_elements_from_a h_elements_from_b); done
    exact ⟨h_existence, h_maximality⟩
  exact ⟨h_nonneg, h_lcs⟩

theorem uniqueness (a : Array Int) (b : Array Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨h1_nonneg, h1_lcs⟩ := hpost1
  obtain ⟨h2_nonneg, h2_lcs⟩ := hpost2
  unfold isLCSLength at h1_lcs h2_lcs
  obtain ⟨⟨s1, hs1_common, hs1_len⟩, h1_bound⟩ := h1_lcs
  obtain ⟨⟨s2, hs2_common, hs2_len⟩, h2_bound⟩ := h2_lcs
  -- s1 is a common subsequence with length ret1.toNat
  -- s2 is a common subsequence with length ret2.toNat
  -- All common subsequences have length ≤ ret1.toNat (from h1_bound)
  -- All common subsequences have length ≤ ret2.toNat (from h2_bound)
  -- So ret1.toNat ≤ ret2.toNat (apply h2_bound to s1)
  -- And ret2.toNat ≤ ret1.toNat (apply h1_bound to s2)
  have h_le1 : ret1.toNat ≤ ret2.toNat := by
    have := h2_bound s1 hs1_common
    omega
  have h_le2 : ret2.toNat ≤ ret1.toNat := by
    have := h1_bound s2 hs2_common
    omega
  have h_eq_nat : ret1.toNat = ret2.toNat := Nat.le_antisymm h_le1 h_le2
  -- Now use that ret1 ≥ 0 and ret2 ≥ 0 to conclude ret1 = ret2
  have h1_cast : (ret1.toNat : Int) = ret1 := by
    rw [Int.toNat_of_nonneg h1_nonneg]
  have h2_cast : (ret2.toNat : Int) = ret2 := by
    rw [Int.toNat_of_nonneg h2_nonneg]
  calc ret1 = (ret1.toNat : Int) := h1_cast.symm
    _ = (ret2.toNat : Int) := by rw [h_eq_nat]
    _ = ret2 := h2_cast
end Proof
