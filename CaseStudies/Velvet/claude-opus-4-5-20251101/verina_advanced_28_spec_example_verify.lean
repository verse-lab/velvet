import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def allInRange (nums : List Int) (start : Int) (len : Nat) : Prop :=
  ∀ i : Nat, i < len → (start + i) ∈ nums

def hasConsecutiveSeq (nums : List Int) (start : Int) (len : Nat) : Prop :=
  allInRange nums start len



def precondition (nums : List Int) : Prop :=
  nums.Nodup







def postcondition (nums : List Int) (result : Nat) : Prop :=

  (nums = [] → result = 0) ∧

  (nums ≠ [] → result ≥ 1) ∧

  (result > 0 → ∃ start : Int, hasConsecutiveSeq nums start result) ∧

  (∀ start : Int, ∀ len : Nat, len > result → ¬hasConsecutiveSeq nums start len)


def test1_nums : List Int := [100, 4, 200, 1, 3, 2]

def test1_Expected : Nat := 4

def test4_nums : List Int := []

def test4_Expected : Nat := 0

def test8_nums : List Int := [-3, -1, -2, 0, 1]

def test8_Expected : Nat := 5







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums
  native_decide

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition test1_nums test1_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- nums = [] → result = 0 (vacuously true)
    intro h
    simp at h
  · -- nums ≠ [] → result ≥ 1
    intro _
    omega
  · -- result > 0 → ∃ start, hasConsecutiveSeq nums start result
    intro _
    use 1
    unfold hasConsecutiveSeq allInRange
    intro i hi
    interval_cases i
    · simp [List.mem_cons]
    · simp [List.mem_cons]
    · simp [List.mem_cons]
    · simp [List.mem_cons]
  · -- ∀ start len, len > result → ¬hasConsecutiveSeq nums start len
    intro start len hlen
    unfold hasConsecutiveSeq allInRange
    intro hall
    -- len > 4, so we need to find some i < len where start + i ∉ list
    -- The list contains {100, 4, 200, 1, 3, 2}
    have h0 := hall 0 (by omega)
    have h1 := hall 1 (by omega)
    have h2 := hall 2 (by omega)
    have h3 := hall 3 (by omega)
    have h4 := hall 4 (by omega)
    simp only [Int.add_zero] at h0
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h0 h1 h2 h3 h4
    -- Now h0 : start = 100 ∨ start = 4 ∨ start = 200 ∨ start = 1 ∨ start = 3 ∨ start = 2
    -- and similar for h1, h2, h3, h4 with start+1, start+2, etc.
    rcases h0 with heq | heq | heq | heq | heq | heq <;>
    rcases h1 with heq1 | heq1 | heq1 | heq1 | heq1 | heq1 <;>
    omega

theorem test4_precondition :
  precondition test4_nums := by
  unfold precondition test4_nums
  native_decide

theorem test4_postcondition :
  postcondition test4_nums test4_Expected := by
  unfold postcondition test4_nums test4_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- [] = [] → 0 = 0
    intro _
    rfl
  · -- [] ≠ [] → 0 ≥ 1
    intro h
    exact absurd rfl h
  · -- 0 > 0 → ∃ start, hasConsecutiveSeq [] start 0
    intro h
    omega
  · -- ∀ start len, len > 0 → ¬hasConsecutiveSeq [] start len
    intro start len hlen
    unfold hasConsecutiveSeq allInRange
    intro h
    -- h says ∀ i < len, (start + i) ∈ []
    -- Since len > 0, we can use i = 0
    have h0 := h 0 hlen
    exact List.not_mem_nil h0

theorem test8_precondition :
  precondition test8_nums := by
  unfold precondition test8_nums
  native_decide

theorem test8_postcondition :
  postcondition test8_nums test8_Expected := by
  unfold postcondition test8_nums test8_Expected
  constructor
  · -- nums = [] → result = 0
    intro h
    simp at h
  constructor
  · -- nums ≠ [] → result ≥ 1
    intro _
    omega
  constructor
  · -- result > 0 → ∃ start, hasConsecutiveSeq nums start result
    intro _
    use -3
    unfold hasConsecutiveSeq allInRange
    intro i hi
    match i with
    | 0 => simp [List.mem_cons]
    | 1 => simp [List.mem_cons]
    | 2 => simp [List.mem_cons]
    | 3 => simp [List.mem_cons]
    | 4 => simp [List.mem_cons]
    | n + 5 => omega
  · -- ∀ start len, len > result → ¬hasConsecutiveSeq nums start len
    intro start len hlen
    unfold hasConsecutiveSeq allInRange
    intro h
    have h0 : (start + 0) ∈ [-3, -1, -2, 0, 1] := h 0 (by omega)
    have h5 : (start + 5) ∈ [-3, -1, -2, 0, 1] := h 5 (by omega)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h0 h5
    -- h0 : start + 0 = -3 ∨ start + 0 = -1 ∨ start + 0 = -2 ∨ start + 0 = 0 ∨ start + 0 = 1
    -- h5 : start + 5 = -3 ∨ start + 5 = -1 ∨ start + 5 = -2 ∨ start + 5 = 0 ∨ start + 5 = 1
    rcases h0 with h0 | h0 | h0 | h0 | h0 <;>
    rcases h5 with h5 | h5 | h5 | h5 | h5 <;>
    omega

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨h1_empty, h1_nonempty, h1_exists, h1_max⟩ := hpost1
  obtain ⟨h2_empty, h2_nonempty, h2_exists, h2_max⟩ := hpost2
  by_cases hempty : nums = []
  · -- Case: nums is empty
    have hr1 : ret1 = 0 := h1_empty hempty
    have hr2 : ret2 = 0 := h2_empty hempty
    omega
  · -- Case: nums is nonempty
    -- Use trichotomy on ret1 and ret2
    rcases Nat.lt_trichotomy ret1 ret2 with hlt | heq | hgt
    · -- Case ret1 < ret2
      -- From h2_exists, since ret2 > 0 (because ret2 > ret1 ≥ 1), there exists start2 with consecutive seq of length ret2
      have hret2_pos : ret2 > 0 := by
        have := h1_nonempty hempty
        omega
      obtain ⟨start2, hseq2⟩ := h2_exists hret2_pos
      -- But h1_max says no consecutive sequence of length > ret1 exists
      have hcontra := h1_max start2 ret2 hlt
      exact absurd hseq2 hcontra
    · -- Case ret1 = ret2
      exact heq
    · -- Case ret2 < ret1
      -- From h1_exists, since ret1 > 0, there exists start1 with consecutive seq of length ret1
      have hret1_pos : ret1 > 0 := by
        have := h2_nonempty hempty
        omega
      obtain ⟨start1, hseq1⟩ := h1_exists hret1_pos
      -- But h2_max says no consecutive sequence of length > ret2 exists
      have hcontra := h2_max start1 ret1 hgt
      exact absurd hseq1 hcontra
end Proof
