import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasingSubarray (nums : List Int) (start : Nat) (len : Nat) : Prop :=
  start + len ≤ nums.length ∧
  len ≥ 1 ∧
  ∀ i : Nat, i + 1 < len → nums[start + i]! < nums[start + i + 1]!

def existsStrictlyIncreasingOfLength (nums : List Int) (len : Nat) : Prop :=
  ∃ start : Nat, isStrictlyIncreasingSubarray nums start len

def noLongerStrictlyIncreasing (nums : List Int) (maxLen : Nat) : Prop :=
  ∀ len : Nat, len > maxLen → ¬existsStrictlyIncreasingOfLength nums len



def precondition (nums : List Int) : Prop :=
  True



def postcondition (nums : List Int) (result : Nat) : Prop :=

  (nums.length = 0 → result = 0) ∧

  (nums.length > 0 → result ≥ 1) ∧

  result ≤ nums.length ∧

  (nums.length > 0 → existsStrictlyIncreasingOfLength nums result) ∧

  noLongerStrictlyIncreasing nums result


def test1_nums : List Int := [1, 2, 3, 2, 4, 5, 6]

def test1_Expected : Nat := 4

def test5_nums : List Int := []

def test5_Expected : Nat := 0

def test6_nums : List Int := [1, 2, 1, 2, 3, 0, 1, 2, 3, 4]

def test6_Expected : Nat := 5







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition test1_nums test1_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- 1. nums.length = 0 → result = 0 (vacuously true since length = 7)
  · intro h
    simp at h
  -- 2. nums.length > 0 → result ≥ 1 (4 ≥ 1)
  · intro _
    omega
  -- 3. result ≤ nums.length (4 ≤ 7)
  · native_decide
  -- 4. nums.length > 0 → existsStrictlyIncreasingOfLength nums result
  · intro _
    unfold existsStrictlyIncreasingOfLength isStrictlyIncreasingSubarray
    use 3
    refine ⟨?_, ?_, ?_⟩
    · native_decide
    · omega
    · intro i hi
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | n + 3 => omega
  -- 5. noLongerStrictlyIncreasing nums result
  · unfold noLongerStrictlyIncreasing existsStrictlyIncreasingOfLength isStrictlyIncreasingSubarray
    intro len hlen
    intro ⟨start, hstart, hlen1, hincr⟩
    -- Use simp to normalize the list length
    simp only [List.length] at hstart
    -- For each valid len and start, we show a contradiction
    match len with
    | 5 =>
      match start with
      | 0 => have := hincr 2 (by omega); simp [test1_nums] at this
      | 1 => have := hincr 1 (by omega); simp [test1_nums] at this
      | 2 => have := hincr 0 (by omega); simp [test1_nums] at this
      | n + 3 => omega
    | 6 =>
      match start with
      | 0 => have := hincr 2 (by omega); simp [test1_nums] at this
      | 1 => have := hincr 1 (by omega); simp [test1_nums] at this
      | n + 2 => omega
    | 7 =>
      match start with
      | 0 => have := hincr 2 (by omega); simp [test1_nums] at this
      | n + 1 => omega
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | n + 8 => omega

theorem test5_precondition :
  precondition test5_nums := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_nums test5_Expected := by
  unfold postcondition test5_nums test5_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- First: [].length = 0 → 0 = 0
    intro _
    rfl
  · -- Second: [].length > 0 → 0 ≥ 1 (vacuously true)
    intro h
    simp at h
  · -- Third: 0 ≤ [].length
    simp
  · -- Fourth: [].length > 0 → existsStrictlyIncreasingOfLength [] 0 (vacuously true)
    intro h
    simp at h
  · -- Fifth: noLongerStrictlyIncreasing [] 0
    unfold noLongerStrictlyIncreasing
    intro len hlen
    unfold existsStrictlyIncreasingOfLength isStrictlyIncreasingSubarray
    intro ⟨start, hstart⟩
    simp at hstart
    obtain ⟨h1, h2, _⟩ := hstart
    omega

theorem test6_precondition :
  precondition test6_nums := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_nums test6_Expected := by
  unfold postcondition test6_nums test6_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- 1. nums.length = 0 → result = 0 (vacuously true since length = 10)
  · intro h
    simp at h
  -- 2. nums.length > 0 → result ≥ 1 (5 ≥ 1)
  · intro _
    omega
  -- 3. result ≤ nums.length (5 ≤ 10)
  · native_decide
  -- 4. nums.length > 0 → existsStrictlyIncreasingOfLength nums result
  · intro _
    unfold existsStrictlyIncreasingOfLength isStrictlyIncreasingSubarray
    use 5
    refine ⟨?_, ?_, ?_⟩
    · native_decide
    · omega
    · intro i hi
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | 3 => native_decide
      | n + 4 => omega
  -- 5. noLongerStrictlyIncreasing nums result
  · unfold noLongerStrictlyIncreasing existsStrictlyIncreasingOfLength isStrictlyIncreasingSubarray
    intro len hlen
    intro ⟨start, hstart, hlen1, hincr⟩
    simp only [List.length] at hstart
    match len with
    | 6 =>
      match start with
      | 0 => have := hincr 1 (by omega); simp [test6_nums] at this
      | 1 => have := hincr 0 (by omega); simp [test6_nums] at this
      | 2 => have := hincr 2 (by omega); simp [test6_nums] at this
      | 3 => have := hincr 1 (by omega); simp [test6_nums] at this
      | 4 => have := hincr 0 (by omega); simp [test6_nums] at this
      | n + 5 => omega
    | 7 =>
      match start with
      | 0 => have := hincr 1 (by omega); simp [test6_nums] at this
      | 1 => have := hincr 0 (by omega); simp [test6_nums] at this
      | 2 => have := hincr 2 (by omega); simp [test6_nums] at this
      | 3 => have := hincr 1 (by omega); simp [test6_nums] at this
      | n + 4 => omega
    | 8 =>
      match start with
      | 0 => have := hincr 1 (by omega); simp [test6_nums] at this
      | 1 => have := hincr 0 (by omega); simp [test6_nums] at this
      | 2 => have := hincr 2 (by omega); simp [test6_nums] at this
      | n + 3 => omega
    | 9 =>
      match start with
      | 0 => have := hincr 1 (by omega); simp [test6_nums] at this
      | 1 => have := hincr 0 (by omega); simp [test6_nums] at this
      | n + 2 => omega
    | 10 =>
      match start with
      | 0 => have := hincr 1 (by omega); simp [test6_nums] at this
      | n + 1 => omega
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | n + 11 => omega

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨h1_empty, h1_nonempty, h1_bound, h1_exists, h1_nolong⟩ := hpost1
  obtain ⟨h2_empty, h2_nonempty, h2_bound, h2_exists, h2_nolong⟩ := hpost2
  -- Case split on whether the list is empty
  rcases Nat.eq_zero_or_pos nums.length with hlen | hlen
  · -- Empty list case
    have hr1 : ret1 = 0 := h1_empty hlen
    have hr2 : ret2 = 0 := h2_empty hlen
    omega
  · -- Non-empty list case
    apply Nat.le_antisymm
    · -- Show ret1 ≤ ret2
      by_contra hcontra
      push_neg at hcontra
      -- ret1 > ret2, so noLongerStrictlyIncreasing nums ret2 says ¬existsStrictlyIncreasingOfLength nums ret1
      have hno := h2_nolong ret1 hcontra
      have hexists := h1_exists hlen
      exact hno hexists
    · -- Show ret2 ≤ ret1
      by_contra hcontra
      push_neg at hcontra
      -- ret2 > ret1, so noLongerStrictlyIncreasing nums ret1 says ¬existsStrictlyIncreasingOfLength nums ret2
      have hno := h1_nolong ret2 hcontra
      have hexists := h2_exists hlen
      exact hno hexists
end Proof
