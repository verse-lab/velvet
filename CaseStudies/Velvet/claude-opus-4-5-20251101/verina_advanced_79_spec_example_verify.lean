import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isValidPair (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target


def lexLt (p1 : Nat × Nat) (p2 : Nat × Nat) : Prop :=
  p1.1 < p2.1 ∨ (p1.1 = p2.1 ∧ p1.2 < p2.2)


def ensuresSome (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  isValidPair nums target i j ∧
  (∀ i' j', isValidPair nums target i' j' → ¬lexLt (i', j') (i, j))


def ensuresNone (nums : List Int) (target : Int) : Prop :=
  ∀ i j, ¬isValidPair nums target i j

def precondition (nums : List Int) (target : Int) :=
  True

def postcondition (nums : List Int) (target : Int) (result : Option (Nat × Nat)) :=
  match result with
  | none => ensuresNone nums target
  | some (i, j) => ensuresSome nums target i j


def test1_nums : List Int := [2, 7, 11, 15]

def test1_target : Int := 9

def test1_Expected : Option (Nat × Nat) := some (0, 1)

def test3_nums : List Int := [3, 3]

def test3_target : Int := 6

def test3_Expected : Option (Nat × Nat) := some (0, 1)

def test5_nums : List Int := [0, 4, 3, 0]

def test5_target : Int := 0

def test5_Expected : Option (Nat × Nat) := some (0, 3)







section Proof
theorem test1_precondition :
  precondition test1_nums test1_target := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_nums test1_target test1_Expected := by
  unfold postcondition test1_Expected ensuresSome
  constructor
  · -- Prove isValidPair test1_nums test1_target 0 1
    unfold isValidPair test1_nums test1_target
    native_decide
  · -- Prove minimality: no valid pair is lexicographically smaller
    intro i' j' hvalid hlexlt
    unfold lexLt at hlexlt
    unfold isValidPair at hvalid
    cases hlexlt with
    | inl h => 
      -- i' < 0 is impossible for Nat
      exact Nat.not_lt_zero i' h
    | inr h =>
      -- i' = 0 and j' < 1, so j' = 0, but we need i' < j'
      obtain ⟨hi'_eq, hj'_lt⟩ := h
      simp only at hi'_eq hj'_lt
      have hj'_zero : j' = 0 := Nat.lt_one_iff.mp hj'_lt
      rw [hi'_eq, hj'_zero] at hvalid
      -- Now hvalid says 0 < 0, which is false
      exact Nat.lt_irrefl 0 hvalid.1

theorem test3_precondition :
  precondition test3_nums test3_target := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_nums test3_target test3_Expected := by
  unfold postcondition test3_Expected ensuresSome
  constructor
  · -- Prove isValidPair test3_nums test3_target 0 1
    unfold isValidPair test3_nums test3_target
    native_decide
  · -- Prove minimality: no valid pair is lexicographically smaller than (0, 1)
    intro i' j' hValid
    unfold lexLt
    intro hLex
    cases hLex with
    | inl h_i'_lt_0 =>
      exact Nat.not_lt_zero i' h_i'_lt_0
    | inr h_eq_and_lt =>
      obtain ⟨h_i'_eq_0, h_j'_lt_1⟩ := h_eq_and_lt
      simp only at h_i'_eq_0 h_j'_lt_1
      rw [Nat.lt_one_iff] at h_j'_lt_1
      unfold isValidPair at hValid
      obtain ⟨h_i'_lt_j', _, _⟩ := hValid
      rw [h_i'_eq_0, h_j'_lt_1] at h_i'_lt_j'
      exact Nat.lt_irrefl 0 h_i'_lt_j'

theorem test5_precondition :
  precondition test5_nums test5_target := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition_0
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    : isValidPair test5_nums test5_target 0 3 := by
    unfold isValidPair test5_nums test5_target
    native_decide

theorem test5_postcondition_1
    (h_valid : isValidPair test5_nums test5_target 0 3)
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_no_neg : True)
    : ¬isValidPair test5_nums test5_target 0 0 := by
  intro h
  unfold isValidPair at h
  obtain ⟨h_lt, _, _⟩ := h
  exact Nat.lt_irrefl 0 h_lt

theorem test5_postcondition_2
    (h_valid : isValidPair test5_nums test5_target 0 3)
    (h_j0_invalid : ¬isValidPair test5_nums test5_target 0 0)
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_no_neg : True)
    : ¬isValidPair test5_nums test5_target 0 1 := by
    unfold isValidPair test5_nums test5_target
    simp only [List.length_cons, List.getElem!_cons_zero, List.getElem!_cons_succ]
    omega

theorem test5_postcondition_3
    (h_valid : isValidPair test5_nums test5_target 0 3)
    (h_j0_invalid : ¬isValidPair test5_nums test5_target 0 0)
    (h_j1_invalid : ¬isValidPair test5_nums test5_target 0 1)
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_no_neg : True)
    : ¬isValidPair test5_nums test5_target 0 2 := by
    unfold isValidPair test5_nums test5_target
    simp only [List.length_cons, List.getElem!_cons_zero, List.getElem!_cons_succ]
    omega

theorem test5_postcondition_4
    (h_valid : isValidPair test5_nums test5_target 0 3)
    (h_j0_invalid : ¬isValidPair test5_nums test5_target 0 0)
    (h_j1_invalid : ¬isValidPair test5_nums test5_target 0 1)
    (h_j2_invalid : ¬isValidPair test5_nums test5_target 0 2)
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_no_neg : True)
    : ∀ j' < 3, ¬isValidPair test5_nums test5_target 0 j' := by
    intro j' hj'
    match j' with
    | 0 => exact h_j0_invalid
    | 1 => exact h_j1_invalid
    | 2 => exact h_j2_invalid
    | n + 3 => omega

theorem test5_postcondition_5
    (h_valid : isValidPair test5_nums test5_target 0 3)
    (h_j0_invalid : ¬isValidPair test5_nums test5_target 0 0)
    (h_j1_invalid : ¬isValidPair test5_nums test5_target 0 1)
    (h_j2_invalid : ¬isValidPair test5_nums test5_target 0 2)
    (h_i0_j_lt3 : ∀ j' < 3, ¬isValidPair test5_nums test5_target 0 j')
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_no_neg : True)
    : ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3) := by
    intro i' j' h_valid_ij h_lex
    unfold lexLt at h_lex
    simp at h_lex
    obtain ⟨h_i_eq, h_j_lt⟩ := h_lex
    subst h_i_eq
    have h_neg := h_i0_j_lt3 j' h_j_lt
    exact h_neg h_valid_ij

theorem test5_postcondition_6
    (h_valid : isValidPair test5_nums test5_target 0 3)
    (h_j0_invalid : ¬isValidPair test5_nums test5_target 0 0)
    (h_j1_invalid : ¬isValidPair test5_nums test5_target 0 1)
    (h_j2_invalid : ¬isValidPair test5_nums test5_target 0 2)
    (h_i0_j_lt3 : ∀ j' < 3, ¬isValidPair test5_nums test5_target 0 j')
    (h_minimal : ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_unfold_post : postcondition test5_nums test5_target test5_Expected ↔ ensuresSome test5_nums test5_target 0 3)
    (h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 ↔ isValidPair test5_nums test5_target 0 3 ∧ ∀ (i' j' : ℕ), isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))
    (h_no_neg : True)
    : ensuresSome test5_nums test5_target 0 3 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition :
  postcondition test5_nums test5_target test5_Expected := by
  -- Unfold the main definitions to expose the structure
  have h_unfold_post : postcondition test5_nums test5_target test5_Expected = ensuresSome test5_nums test5_target 0 3 := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- Unfold ensuresSome to get the conjunction we need to prove
  have h_unfold_ensures : ensuresSome test5_nums test5_target 0 3 = (isValidPair test5_nums test5_target 0 3 ∧ (∀ i' j', isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3))) := by (try simp at *; expose_names); exact (h_unfold_post); done
  -- Prove the first part: (0, 3) is a valid pair
  have h_valid : isValidPair test5_nums test5_target 0 3 := by (try simp at *; expose_names); exact (test5_postcondition_0 h_unfold_post h_unfold_ensures); done
  -- For minimality, we need to show no valid pair is lex smaller than (0, 3)
  -- lexLt (i', j') (0, 3) means i' < 0 OR (i' = 0 AND j' < 3)
  -- Case 1: i' < 0 is impossible for natural numbers
  have h_no_neg : ∀ i' : Nat, ¬(i' < 0) := by (try simp at *; expose_names); exact fun i' ↦ (Nat.not_lt_zero i'); done
  -- Case 2: If i' = 0 and j' < 3, then j' ∈ {0, 1, 2}
  -- Subcase j' = 0: violates i' < j' requirement of isValidPair
  have h_j0_invalid : ¬isValidPair test5_nums test5_target 0 0 := by (try simp at *; expose_names); exact (test5_postcondition_1 h_valid h_unfold_post h_unfold_ensures h_no_neg); done
  -- Subcase j' = 1: nums[0] + nums[1] = 0 + 4 = 4 ≠ 0
  have h_j1_invalid : ¬isValidPair test5_nums test5_target 0 1 := by (try simp at *; expose_names); exact (test5_postcondition_2 h_valid h_j0_invalid h_unfold_post h_unfold_ensures h_no_neg); done
  -- Subcase j' = 2: nums[0] + nums[2] = 0 + 3 = 3 ≠ 0
  have h_j2_invalid : ¬isValidPair test5_nums test5_target 0 2 := by (try simp at *; expose_names); exact (test5_postcondition_3 h_valid h_j0_invalid h_j1_invalid h_unfold_post h_unfold_ensures h_no_neg); done
  -- Combine: for i' = 0 and j' < 3, there's no valid pair
  have h_i0_j_lt3 : ∀ j' : Nat, j' < 3 → ¬isValidPair test5_nums test5_target 0 j' := by (try simp at *; expose_names); exact (test5_postcondition_4 h_valid h_j0_invalid h_j1_invalid h_j2_invalid h_unfold_post h_unfold_ensures h_no_neg); done
  -- Prove minimality: no valid pair is lexicographically smaller than (0, 3)
  have h_minimal : ∀ i' j', isValidPair test5_nums test5_target i' j' → ¬lexLt (i', j') (0, 3) := by (try simp at *; expose_names); exact (test5_postcondition_5 h_valid h_j0_invalid h_j1_invalid h_j2_invalid h_i0_j_lt3 h_unfold_post h_unfold_ensures h_no_neg); done
  -- Combine validity and minimality to get ensuresSome
  have h_ensures : ensuresSome test5_nums test5_target 0 3 := by (try simp at *; expose_names); exact (test5_postcondition_6 h_valid h_j0_invalid h_j1_invalid h_j2_invalid h_i0_j_lt3 h_minimal h_unfold_post h_unfold_ensures h_no_neg); done
  -- Final step: use h_ensures to prove postcondition
  unfold postcondition test5_Expected
  exact h_ensures

theorem uniqueness (nums : List Int) (target : Int):
  precondition nums target →
  (∀ ret1 ret2,
    postcondition nums target ret1 →
    postcondition nums target ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  -- Case analysis on ret1 and ret2
  cases ret1 with
  | none =>
    cases ret2 with
    | none => rfl
    | some p2 =>
      -- ret1 = none means ensuresNone, ret2 = some means ensuresSome
      unfold postcondition at hpost1 hpost2
      unfold ensuresNone at hpost1
      unfold ensuresSome at hpost2
      obtain ⟨hvalid2, _⟩ := hpost2
      -- hpost1 says no valid pairs, but hvalid2 says p2 is valid
      have := hpost1 p2.1 p2.2
      exact absurd hvalid2 this
  | some p1 =>
    cases ret2 with
    | none =>
      -- Symmetric case
      unfold postcondition at hpost1 hpost2
      unfold ensuresNone at hpost2
      unfold ensuresSome at hpost1
      obtain ⟨hvalid1, _⟩ := hpost1
      have := hpost2 p1.1 p1.2
      exact absurd hvalid1 this
    | some p2 =>
      -- Both are some, need to show p1 = p2
      unfold postcondition at hpost1 hpost2
      unfold ensuresSome at hpost1 hpost2
      obtain ⟨hvalid1, hmin1⟩ := hpost1
      obtain ⟨hvalid2, hmin2⟩ := hpost2
      -- hmin1 says no valid pair is lexLt p1
      -- hmin2 says no valid pair is lexLt p2
      have hnotlt12 : ¬lexLt (p1.1, p1.2) (p2.1, p2.2) := hmin2 p1.1 p1.2 hvalid1
      have hnotlt21 : ¬lexLt (p2.1, p2.2) (p1.1, p1.2) := hmin1 p2.1 p2.2 hvalid2
      -- From these, derive p1 = p2
      unfold lexLt at hnotlt12 hnotlt21
      push_neg at hnotlt12 hnotlt21
      obtain ⟨hge12, himp12⟩ := hnotlt12
      obtain ⟨hge21, himp21⟩ := hnotlt21
      -- hge12 : p2.1 ≤ p1.1, hge21 : p1.1 ≤ p2.1
      have heq1 : p1.1 = p2.1 := Nat.le_antisymm hge21 hge12
      -- Now use himp12 and himp21 with heq1
      have hge12' : p2.2 ≤ p1.2 := himp12 heq1
      have hge21' : p1.2 ≤ p2.2 := himp21 heq1.symm
      have heq2 : p1.2 = p2.2 := Nat.le_antisymm hge21' hge12'
      -- Conclude p1 = p2
      have : p1 = p2 := Prod.ext heq1 heq2
      simp [this]
end Proof
