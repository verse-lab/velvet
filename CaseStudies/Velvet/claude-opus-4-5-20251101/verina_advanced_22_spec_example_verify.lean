import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! < lst[k + 1]!

def isStrictlyDecreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! > lst[k + 1]!

def hasPeakValleyStructure (lst : List Int) : Prop :=
  ∃ peakIdx : Nat, 
    peakIdx > 0 ∧ 
    peakIdx < lst.length - 1 ∧
    isStrictlyIncreasingRange lst 0 peakIdx ∧
    isStrictlyDecreasingRange lst peakIdx (lst.length - 1)

def precondition (lst : List Int) :=
  True

def postcondition (lst : List Int) (result : Bool) :=
  result = true ↔ hasPeakValleyStructure lst


def test1_lst : List Int := [1, 3, 5, 2, 1]

def test1_Expected : Bool := true

def test6_lst : List Int := [1, 10, 100, 1]

def test6_Expected : Bool := true

def test9_lst : List Int := [1, 3, 2]

def test9_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_lst := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_lst test1_Expected := by
  unfold postcondition test1_Expected test1_lst
  simp only [true_iff]
  unfold hasPeakValleyStructure
  use 2
  refine ⟨by decide, ?_, ?_, ?_⟩
  · native_decide
  · unfold isStrictlyIncreasingRange
    refine ⟨by decide, by native_decide, ?_⟩
    intro k hk1 hk2
    have hk_bound : k < 2 := hk2
    have hk_lower : 0 ≤ k := hk1
    match k with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega
  · unfold isStrictlyDecreasingRange
    refine ⟨by decide, by native_decide, ?_⟩
    intro k hk1 hk2
    have hk_bound : k < 4 := hk2
    have hk_lower : 2 ≤ k := hk1
    match k with
    | 0 => omega
    | 1 => omega
    | 2 => native_decide
    | 3 => native_decide
    | n + 4 => omega

theorem test6_precondition :
  precondition test6_lst := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_lst test6_Expected := by
  unfold postcondition test6_Expected test6_lst
  simp only [eq_self_iff_true, true_iff]
  unfold hasPeakValleyStructure
  use 2
  constructor
  · decide
  · constructor
    · native_decide
    · constructor
      · unfold isStrictlyIncreasingRange
        constructor
        · decide
        · constructor
          · native_decide
          · intro k hk1 hk2
            have hk_bound : k < 2 := hk2
            have hk_low : 0 ≤ k := hk1
            match k with
            | 0 => native_decide
            | 1 => native_decide
            | n + 2 => omega
      · unfold isStrictlyDecreasingRange
        constructor
        · decide
        · constructor
          · native_decide
          · intro k hk1 hk2
            have hk_bound : k < 3 := hk2
            have hk_low : 2 ≤ k := hk1
            match k with
            | 0 => omega
            | 1 => omega
            | 2 => native_decide
            | n + 3 => omega

theorem test9_precondition :
  precondition test9_lst := by
  intros; expose_names; exact (trivial); done

theorem test9_postcondition_0
    (h_expected_true : test9_Expected = true)
    (h_peak_bound : 1 < test9_lst.length - 1)
    (h_length : test9_lst.length = 3)
    (h_unfold : postcondition test9_lst test9_Expected ↔ (test9_Expected = true ↔ hasPeakValleyStructure test9_lst))
    (h_simp : True)
    (h_peak_idx : True)
    (h_inc_bounds : 1 < test9_lst.length)
    (h_inc_at_0 : test9_lst[0]?.getD 0 < test9_lst[1]?.getD 0)
    (h_dec_bounds : 2 < test9_lst.length)
    (h_dec_at_1 : test9_lst[2]?.getD 0 < test9_lst[1]?.getD 0)
    : isStrictlyIncreasingRange test9_lst 0 1 := by
    unfold isStrictlyIncreasingRange
    constructor
    · -- 0 < 1
      omega
    constructor
    · -- 1 < test9_lst.length
      simp [test9_lst]
    · -- ∀ k, 0 ≤ k → k < 1 → test9_lst[k]! < test9_lst[k + 1]!
      intro k hk_ge hk_lt
      -- k must be 0 since 0 ≤ k < 1
      have hk_eq : k = 0 := by omega
      subst hk_eq
      native_decide

theorem test9_postcondition_1
    (h_expected_true : test9_Expected = true)
    (h_peak_bound : 1 < test9_lst.length - 1)
    (h_length : test9_lst.length = 3)
    (h_strictly_inc : isStrictlyIncreasingRange test9_lst 0 1)
    (h_unfold : postcondition test9_lst test9_Expected ↔ (test9_Expected = true ↔ hasPeakValleyStructure test9_lst))
    (h_simp : True)
    (h_peak_idx : True)
    (h_inc_bounds : 1 < test9_lst.length)
    (h_inc_at_0 : test9_lst[0]?.getD 0 < test9_lst[1]?.getD 0)
    (h_dec_bounds : 2 < test9_lst.length)
    (h_dec_at_1 : test9_lst[2]?.getD 0 < test9_lst[1]?.getD 0)
    : isStrictlyDecreasingRange test9_lst 1 2 := by
    unfold isStrictlyDecreasingRange
    constructor
    · omega
    constructor
    · simp [test9_lst]
    · intro k hk_ge hk_lt
      have hk_eq : k = 1 := by omega
      subst hk_eq
      native_decide

theorem test9_postcondition_2
    (h_expected_true : test9_Expected = true)
    (h_peak_bound : 1 < test9_lst.length - 1)
    (h_length : test9_lst.length = 3)
    (h_strictly_inc : isStrictlyIncreasingRange test9_lst 0 1)
    (h_strictly_dec : isStrictlyDecreasingRange test9_lst 1 2)
    (h_unfold : postcondition test9_lst test9_Expected ↔ (test9_Expected = true ↔ hasPeakValleyStructure test9_lst))
    (h_simp : True)
    (h_peak_idx : True)
    (h_inc_bounds : 1 < test9_lst.length)
    (h_inc_at_0 : test9_lst[0]?.getD 0 < test9_lst[1]?.getD 0)
    (h_dec_bounds : 2 < test9_lst.length)
    (h_dec_at_1 : test9_lst[2]?.getD 0 < test9_lst[1]?.getD 0)
    : hasPeakValleyStructure test9_lst := by
    unfold hasPeakValleyStructure
    use 1
    constructor
    · omega
    constructor
    · simp [test9_lst]
    constructor
    · exact h_strictly_inc
    · simp [test9_lst] at h_strictly_dec ⊢
      exact h_strictly_dec

theorem test9_postcondition :
  postcondition test9_lst test9_Expected := by
  -- Step 1: Unfold the definitions to expose the structure
  have h_unfold : postcondition test9_lst test9_Expected = (test9_Expected = true ↔ hasPeakValleyStructure test9_lst) := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Step 2: Since test9_Expected = true, the LHS of biconditional is trivially true
  have h_expected_true : test9_Expected = true := by (try simp at *; expose_names); exact rfl; done
  -- Step 3: The biconditional with true = true simplifies to just proving hasPeakValleyStructure
  have h_simp : (true = true ↔ hasPeakValleyStructure test9_lst) ↔ hasPeakValleyStructure test9_lst := by (try simp at *; expose_names); exact (iff_true_left h_expected_true); done
  -- Step 4: We use peakIdx = 1 as our witness
  have h_peak_idx : (1 : Nat) > 0 := by (try simp at *; expose_names); exact Nat.one_pos; done
  -- Step 5: Check that peakIdx < lst.length - 1, i.e., 1 < 3 - 1 = 2
  have h_peak_bound : (1 : Nat) < test9_lst.length - 1 := by (try simp at *; expose_names); exact (Nat.one_lt_succ_succ 0); done
  -- Step 6: Check list length is 3
  have h_length : test9_lst.length = 3 := by (try simp at *; expose_names); exact rfl; done
  -- Step 7: Verify the strictly increasing range from 0 to 1
  have h_inc_bounds : (0 : Nat) < 1 ∧ 1 < test9_lst.length := by (try simp at *; expose_names); exact (Nat.one_lt_succ_succ [2].length); done
  -- Step 8: Check lst[0]! < lst[1]! i.e., 1 < 3
  have h_inc_at_0 : test9_lst[0]! < test9_lst[1]! := by (try simp at *; expose_names); exact (Int.lt_of_toNat_lt h_inc_bounds); done
  -- Step 9: Verify the strictly decreasing range from 1 to 2
  have h_dec_bounds : (1 : Nat) < 2 ∧ 2 < test9_lst.length := by (try simp at *; expose_names); exact (Nat.lt_add_one 2); done
  -- Step 10: Check lst[1]! > lst[2]! i.e., 3 > 2
  have h_dec_at_1 : test9_lst[1]! > test9_lst[2]! := by (try simp at *; expose_names); exact (Int.lt_of_toNat_lt h_dec_bounds); done
  -- Step 11: Construct isStrictlyIncreasingRange
  have h_strictly_inc : isStrictlyIncreasingRange test9_lst 0 1 := by (try simp at *; expose_names); exact (test9_postcondition_0 h_expected_true h_peak_bound h_length h_unfold h_simp h_peak_idx h_inc_bounds h_inc_at_0 h_dec_bounds h_dec_at_1); done
  -- Step 12: Construct isStrictlyDecreasingRange
  have h_strictly_dec : isStrictlyDecreasingRange test9_lst 1 2 := by (try simp at *; expose_names); exact (test9_postcondition_1 h_expected_true h_peak_bound h_length h_strictly_inc h_unfold h_simp h_peak_idx h_inc_bounds h_inc_at_0 h_dec_bounds h_dec_at_1); done
  -- Step 13: Construct hasPeakValleyStructure with witness 1
  have h_peak_valley : hasPeakValleyStructure test9_lst := by (try simp at *; expose_names); exact (test9_postcondition_2 h_expected_true h_peak_bound h_length h_strictly_inc h_strictly_dec h_unfold h_simp h_peak_idx h_inc_bounds h_inc_at_0 h_dec_bounds h_dec_at_1); done
  -- Final: Combine to prove postcondition
  unfold postcondition test9_Expected test9_lst
  simp only [true_iff]
  exact h_peak_valley

theorem uniqueness (lst : List Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  intro _h_pre
  intro ret1 ret2 h1 h2
  -- h1 : postcondition lst ret1, i.e., ret1 = true ↔ hasPeakValleyStructure lst
  -- h2 : postcondition lst ret2, i.e., ret2 = true ↔ hasPeakValleyStructure lst
  unfold postcondition at h1 h2
  -- Now h1 : ret1 = true ↔ hasPeakValleyStructure lst
  -- And h2 : ret2 = true ↔ hasPeakValleyStructure lst
  -- We need to show ret1 = ret2
  -- Using Bool.eq_iff_iff: a = b ↔ (a = true ↔ b = true)
  rw [Bool.eq_iff_iff]
  -- Now goal is: ret1 = true ↔ ret2 = true
  -- From h1 and h2, we have ret1 = true ↔ hasPeakValleyStructure lst ↔ ret2 = true
  exact Iff.trans h1 (Iff.symm h2)
end Proof
