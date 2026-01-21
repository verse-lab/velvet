import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def subarraySum (seq : List Int) (start : Nat) (stop : Nat) : Int :=
  (seq.drop start).take (stop - start) |>.foldl (· + ·) 0


def isValidSubarray (seq : List Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ seq.length


def isAchievable (seq : List Int) (result : Int) : Prop :=
  ∃ start stop, isValidSubarray seq start stop ∧ subarraySum seq start stop = result


def isMaximal (seq : List Int) (result : Int) : Prop :=
  ∀ start stop, isValidSubarray seq start stop → subarraySum seq start stop ≤ result



def precondition (sequence : List Int) : Prop :=
  sequence.length > 0



def postcondition (sequence : List Int) (result : Int) : Prop :=
  isAchievable sequence result ∧ isMaximal sequence result


def test1_sequence : List Int := [10, -4, 3, 1, 5, 6, -35, 12, 21, -1]

def test1_Expected : Int := 33

def test3_sequence : List Int := [-1, -2, -3, -4, -5]

def test3_Expected : Int := -1

def test4_sequence : List Int := [7]

def test4_Expected : Int := 7







section Proof
theorem test1_precondition :
  precondition test1_sequence := by
  unfold precondition test1_sequence
  decide

theorem test1_postcondition_0 : ∃ start stop, isValidSubarray test1_sequence start stop ∧ subarraySum test1_sequence start stop = test1_Expected := by
    use 7, 9
    constructor
    · unfold isValidSubarray test1_sequence
      simp
    · native_decide

theorem test1_postcondition_1
    (start : ℕ)
    (stop : ℕ)
    (h_valid : start < stop ∧ stop ≤ test1_sequence.length)
    (h_seq_length : test1_sequence.length = 10)
    : start < 10 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_2
    (start : ℕ)
    (stop : ℕ)
    (h_valid : start < stop ∧ stop ≤ test1_sequence.length)
    (h_seq_length : test1_sequence.length = 10)
    (h_start_bound : start < 10)
    : stop ≤ 10 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_3
    (start : ℕ)
    (stop : ℕ)
    (h_valid : start < stop ∧ stop ≤ test1_sequence.length)
    (h_seq_length : test1_sequence.length = 10)
    (h_start_bound : start < 10)
    (h_stop_bound : stop ≤ 10)
    : ∀ (s t : ℕ), s < t → t ≤ 10 → subarraySum test1_sequence s t ≤ test1_Expected := by
    intro s t hst ht
    -- Now we have bounded s and t, so we can use decide on a finite check
    have hs : s < 10 := Nat.lt_of_lt_of_le hst ht
    interval_cases s <;> interval_cases t <;> native_decide

theorem test1_postcondition :
  postcondition test1_sequence test1_Expected := by
  -- Unfold the main definition
  unfold postcondition
  -- We need to prove: isAchievable test1_sequence test1_Expected ∧ isMaximal test1_sequence test1_Expected
  constructor
  -- Part 1: Prove isAchievable
  · -- Need to show there exists start, stop with valid subarray summing to 33
    unfold isAchievable
    -- Use witnesses start = 7, stop = 9
    have h_witness : ∃ start stop, isValidSubarray test1_sequence start stop ∧ subarraySum test1_sequence start stop = test1_Expected := by
      (try simp at *; expose_names); exact (test1_postcondition_0); done
    exact h_witness
  -- Part 2: Prove isMaximal
  · -- Need to show all valid subarrays have sum ≤ 33
    unfold isMaximal
    intro start stop h_valid
    -- This is a finite check over concrete values
    have h_seq_length : test1_sequence.length = 10 := by (try simp at *; expose_names); exact (rfl); done
    -- The validity constraint gives us start < stop ≤ 10
    unfold isValidSubarray at h_valid
    have h_start_bound : start < 10 := by (try simp at *; expose_names); exact (test1_postcondition_1 start stop h_valid h_seq_length); done
    have h_stop_bound : stop ≤ 10 := by (try simp at *; expose_names); exact (test1_postcondition_2 start stop h_valid h_seq_length h_start_bound); done
    -- For each valid (start, stop) pair, verify subarraySum ≤ 33
    -- This can be done by exhaustive computation
    have h_max_check : ∀ (s t : Nat), s < t → t ≤ 10 → subarraySum test1_sequence s t ≤ test1_Expected := by
      (try simp at *; expose_names); exact (test1_postcondition_3 start stop h_valid h_seq_length h_start_bound h_stop_bound); done
    exact h_max_check start stop h_valid.1 h_valid.2

theorem test3_precondition :
  precondition test3_sequence := by
  unfold precondition test3_sequence
  decide

theorem test3_postcondition :
  postcondition test3_sequence test3_Expected := by
  unfold postcondition
  constructor
  · -- isAchievable: witness start=0, stop=1 gives [-1] with sum -1
    unfold isAchievable
    use 0, 1
    constructor
    · unfold isValidSubarray
      constructor
      · omega
      · native_decide
    · native_decide
  · -- isMaximal: all valid subarrays have sum ≤ -1
    unfold isMaximal
    intro start stop h_valid
    unfold isValidSubarray at h_valid
    have h_seq_length : test3_sequence.length = 5 := by native_decide
    have h_start_bound : start < 5 := by omega
    have h_stop_bound : stop ≤ 5 := by omega
    -- Exhaustive case analysis
    interval_cases start <;> interval_cases stop <;>
    (first | omega | native_decide)

theorem test4_precondition :
  precondition test4_sequence := by
  unfold precondition test4_sequence
  decide

theorem test4_postcondition :
  postcondition test4_sequence test4_Expected := by
  unfold postcondition
  constructor
  · -- isAchievable: show there exists start, stop with valid subarray summing to 7
    unfold isAchievable
    use 0, 1
    constructor
    · -- isValidSubarray [7] 0 1
      unfold isValidSubarray
      simp [test4_sequence]
    · -- subarraySum [7] 0 1 = 7
      native_decide
  · -- isMaximal: show all valid subarrays have sum ≤ 7
    unfold isMaximal
    intro start stop h_valid
    unfold isValidSubarray at h_valid
    simp [test4_sequence] at h_valid
    -- h_valid : start < stop ∧ stop ≤ 1
    -- This means stop = 1 and start = 0
    have h_stop : stop = 1 := by omega
    have h_start : start = 0 := by omega
    subst h_stop h_start
    native_decide

theorem uniqueness (sequence : List Int):
  precondition sequence →
  (∀ ret1 ret2,
    postcondition sequence ret1 →
    postcondition sequence ret2 →
    ret1 = ret2) := by
  intro _h_pre
  intro ret1 ret2 h_post1 h_post2
  -- Unpack postconditions
  obtain ⟨h_achieve1, h_maximal1⟩ := h_post1
  obtain ⟨h_achieve2, h_maximal2⟩ := h_post2
  -- Unpack achievability - get witnesses for the subarrays
  obtain ⟨start1, stop1, h_valid1, h_sum1⟩ := h_achieve1
  obtain ⟨start2, stop2, h_valid2, h_sum2⟩ := h_achieve2
  -- Show ret1 ≤ ret2: the subarray achieving ret1 has sum ≤ ret2 by maximality of ret2
  have h_le1 : ret1 ≤ ret2 := by
    have := h_maximal2 start1 stop1 h_valid1
    rw [h_sum1] at this
    exact this
  -- Show ret2 ≤ ret1: the subarray achieving ret2 has sum ≤ ret1 by maximality of ret1
  have h_le2 : ret2 ≤ ret1 := by
    have := h_maximal1 start2 stop2 h_valid2
    rw [h_sum2] at this
    exact this
  -- Conclude equality by antisymmetry
  exact Int.le_antisymm h_le1 h_le2
end Proof
