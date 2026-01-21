import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def subarraySum (arr : Array Int) (start : Nat) (stop : Nat) : Int :=
  if stop ≤ start then 0
  else if stop > arr.size then 0
  else (arr.toList.drop start).take (stop - start) |>.foldl (· + ·) 0

def isValidSubarray (arr : Array Int) (k : Int) (start : Nat) (stop : Nat) : Bool :=
  start ≤ stop ∧ stop ≤ arr.size ∧ k > 0 ∧ (stop - start) % k.toNat = 0

def validSubarrayWithSum (arr : Array Int) (k : Int) (s : Int) : Prop :=
  ∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ 
    (stop - start) % k.toNat = 0 ∧ subarraySum arr start stop = s



def precondition (arr : Array Int) (k : Int) : Prop :=
  k ≥ 1



def postcondition (arr : Array Int) (k : Int) (result : Int) : Prop :=

  ((¬∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0) → result = 0) ∧

  ((∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0) →

    ((result = 0 ∧ ∀ start stop : Nat, start < stop → stop ≤ arr.size → 
      (stop - start) % k.toNat = 0 → subarraySum arr start stop ≤ 0) ∨
     (result > 0 ∧ validSubarrayWithSum arr k result ∧
      ∀ start stop : Nat, start < stop → stop ≤ arr.size → 
        (stop - start) % k.toNat = 0 → subarraySum arr start stop ≤ result)))


def test1_arr : Array Int := #[1, 2, 3, 4, 5]

def test1_k : Int := 2

def test1_Expected : Int := 14

def test2_arr : Array Int := #[1, -2, 3, -4, 5]

def test2_k : Int := 3

def test2_Expected : Int := 4

def test5_arr : Array Int := #[-2, 7, 1, 3]

def test5_k : Int := 2

def test5_Expected : Int := 9







section Proof
theorem test1_precondition :
  precondition test1_arr test1_k := by
  unfold precondition test1_k
  decide

theorem test1_postcondition_0
    (h_arr : test1_arr = #[1, 2, 3, 4, 5])
    (h_k : test1_k = 2)
    (h_expected : test1_Expected = 14)
    (h_size : test1_arr.size = 5)
    : ∃ start stop, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0 := by
    use 0, 2
    constructor
    · omega
    constructor
    · simp only [h_size]
      omega
    · simp only [test1_k]
      native_decide

theorem test1_postcondition_1
    (h_arr : test1_arr = #[1, 2, 3, 4, 5])
    (h_k : test1_k = 2)
    (h_expected : test1_Expected = 14)
    (h_size : test1_arr.size = 5)
    (h_valid_exists : ∃ start stop, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0)
    (h_sum_14 : subarraySum test1_arr 1 5 = 14)
    (h_positive : 0 < test1_Expected)
    (h_witness_valid : 5 ≤ test1_arr.size ∧ 4 % test1_k.toNat = 0)
    : validSubarrayWithSum test1_arr test1_k test1_Expected := by
    unfold validSubarrayWithSum
    refine ⟨1, 5, ?_, ?_, ?_, ?_⟩
    · -- 1 < 5
      omega
    · -- 5 ≤ test1_arr.size
      simp [h_size]
    · -- (5 - 1) % test1_k.toNat = 0
      simp [h_k]
    · -- subarraySum test1_arr 1 5 = test1_Expected
      rw [h_expected]
      exact h_sum_14

theorem test1_postcondition_2
    (h_arr : test1_arr = #[1, 2, 3, 4, 5])
    (h_k : test1_k = 2)
    (h_expected : test1_Expected = 14)
    (h_size : test1_arr.size = 5)
    (h_valid_exists : ∃ start stop, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0)
    (h_sum_14 : subarraySum test1_arr 1 5 = 14)
    (h_valid_subarray_sum : validSubarrayWithSum test1_arr test1_k test1_Expected)
    (h_positive : 0 < test1_Expected)
    (h_witness_valid : 5 ≤ test1_arr.size ∧ 4 % test1_k.toNat = 0)
    : ∀ (start stop : ℕ), start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ test1_Expected := by
    intro start stop h_lt h_le h_mod
    simp only [test1_arr, test1_k, test1_Expected] at *
    simp only [subarraySum]
    have hs : stop ≤ 5 := h_le
    have hm : (stop - start) % 2 = 0 := h_mod
    have hstart : start < 5 := Nat.lt_of_lt_of_le h_lt hs
    interval_cases start <;> interval_cases stop <;> simp_all <;> native_decide

theorem test1_postcondition_3
    (h_arr : test1_arr = #[1, 2, 3, 4, 5])
    (h_k : test1_k = 2)
    (h_expected : test1_Expected = 14)
    (h_size : test1_arr.size = 5)
    (h_valid_exists : ∃ start stop, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0)
    (h_sum_14 : subarraySum test1_arr 1 5 = 14)
    (h_valid_subarray_sum : validSubarrayWithSum test1_arr test1_k test1_Expected)
    (h_max_sum : ∀ (start stop : ℕ), start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ test1_Expected)
    (h_positive : 0 < test1_Expected)
    (h_witness_valid : 5 ≤ test1_arr.size ∧ 4 % test1_k.toNat = 0)
    : (∀ (x x_1 : ℕ), x < x_1 → x_1 ≤ test1_arr.size → ¬(x_1 - x) % test1_k.toNat = 0) → test1_Expected = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_4
    (h_arr : test1_arr = #[1, 2, 3, 4, 5])
    (h_k : test1_k = 2)
    (h_expected : test1_Expected = 14)
    (h_size : test1_arr.size = 5)
    (h_valid_exists : ∃ start stop, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0)
    (h_sum_14 : subarraySum test1_arr 1 5 = 14)
    (h_valid_subarray_sum : validSubarrayWithSum test1_arr test1_k test1_Expected)
    (h_max_sum : ∀ (start stop : ℕ), start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ test1_Expected)
    (h_positive : 0 < test1_Expected)
    (h_witness_valid : 5 ≤ test1_arr.size ∧ 4 % test1_k.toNat = 0)
    (h_part1 : (∀ (x x_1 : ℕ), x < x_1 → x_1 ≤ test1_arr.size → ¬(x_1 - x) % test1_k.toNat = 0) → test1_Expected = 0)
    : ∀ (x x_1 : ℕ), x < x_1 → x_1 ≤ test1_arr.size → (x_1 - x) % test1_k.toNat = 0 → (test1_Expected = 0 ∧ ∀ (start stop : ℕ), start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ 0) ∨ 0 < test1_Expected ∧ validSubarrayWithSum test1_arr test1_k test1_Expected ∧ ∀ (start stop : ℕ), start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ test1_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition :
  postcondition test1_arr test1_k test1_Expected := by
  -- First, establish what the concrete values are
  have h_arr : test1_arr = #[1, 2, 3, 4, 5] := by (try simp at *; expose_names); exact rfl; done
  have h_k : test1_k = 2 := by (try simp at *; expose_names); exact rfl; done
  have h_expected : test1_Expected = 14 := by (try simp at *; expose_names); exact rfl; done
  have h_size : test1_arr.size = 5 := by (try simp at *; expose_names); exact rfl; done
  -- Show that valid subarrays exist (e.g., start=0, stop=2)
  have h_valid_exists : ∃ start stop : Nat, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0 := by (try simp at *; expose_names); exact (test1_postcondition_0 h_arr h_k h_expected h_size); done
  -- Show that 14 > 0
  have h_positive : test1_Expected > 0 := by (try simp at *; expose_names); exact (Int.sign_eq_one_iff_pos.mp rfl); done
  -- Show there exists a subarray with sum 14 (start=1, stop=5)
  have h_witness_valid : 1 < 5 ∧ 5 ≤ test1_arr.size ∧ (5 - 1) % test1_k.toNat = 0 := by (try simp at *; expose_names); exact (if_false_right.mp rfl); done
  -- Show that subarraySum for (1, 5) equals 14
  have h_sum_14 : subarraySum test1_arr 1 5 = 14 := by (try simp at *; expose_names); exact (h_expected); done
  -- Combine to show validSubarrayWithSum
  have h_valid_subarray_sum : validSubarrayWithSum test1_arr test1_k test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_1 h_arr h_k h_expected h_size h_valid_exists h_sum_14 h_positive h_witness_valid); done
  -- Show that 14 is the maximum sum among all valid subarrays
  have h_max_sum : ∀ start stop : Nat, start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_2 h_arr h_k h_expected h_size h_valid_exists h_sum_14 h_valid_subarray_sum h_positive h_witness_valid); done
  -- The first part of postcondition is vacuously true since valid subarrays exist
  have h_part1 : (¬∃ start stop : Nat, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0) → test1_Expected = 0 := by (try simp at *; expose_names); exact (test1_postcondition_3 h_arr h_k h_expected h_size h_valid_exists h_sum_14 h_valid_subarray_sum h_max_sum h_positive h_witness_valid); done
  -- The second part holds via the right disjunct
  have h_part2 : (∃ start stop : Nat, start < stop ∧ stop ≤ test1_arr.size ∧ (stop - start) % test1_k.toNat = 0) → ((test1_Expected = 0 ∧ ∀ start stop : Nat, start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ 0) ∨ (test1_Expected > 0 ∧ validSubarrayWithSum test1_arr test1_k test1_Expected ∧ ∀ start stop : Nat, start < stop → stop ≤ test1_arr.size → (stop - start) % test1_k.toNat = 0 → subarraySum test1_arr start stop ≤ test1_Expected)) := by (try simp at *; expose_names); exact (test1_postcondition_4 h_arr h_k h_expected h_size h_valid_exists h_sum_14 h_valid_subarray_sum h_max_sum h_positive h_witness_valid h_part1); done
  -- Combine both parts to prove the postcondition
  unfold postcondition
  exact ⟨h_part1, h_part2⟩

theorem test2_precondition : precondition test2_arr test2_k := by
  unfold precondition test2_k
  decide

theorem test2_postcondition :
  postcondition test2_arr test2_k test2_Expected := by
  unfold postcondition
  constructor
  · intro h; exfalso; apply h; exact ⟨0, 3, by omega, by native_decide, by native_decide⟩
  · intro _
    right
    refine ⟨by native_decide, ?_, ?_⟩
    · unfold validSubarrayWithSum
      exact ⟨2, 5, by omega, by native_decide, by native_decide, by native_decide⟩
    · intro start stop h_lt h_le h_mod
      have h_size : test2_arr.size = 5 := by native_decide
      have h_k : test2_k.toNat = 3 := by native_decide
      simp only [h_size] at h_le
      simp only [h_k] at h_mod
      have h_diff_pos : stop - start > 0 := by omega
      have h_diff_bound : stop - start ≤ 5 := by omega
      have h_diff_div3 : (stop - start) % 3 = 0 := h_mod
      -- stop - start must be 3 (since 0 < stop - start ≤ 5 and divisible by 3)
      have h_diff_eq : stop - start = 3 := by omega
      -- Now start can be 0, 1, or 2 (since start + 3 = stop ≤ 5, so start ≤ 2)
      have h_start_le : start ≤ 2 := by omega
      have h_stop_eq : stop = start + 3 := by omega
      match start with
      | 0 => simp only [h_stop_eq]; native_decide
      | 1 => simp only [h_stop_eq]; native_decide
      | 2 => simp only [h_stop_eq]; native_decide
      | n + 3 => omega

theorem test5_precondition : precondition test5_arr test5_k := by
  unfold precondition test5_k
  decide

theorem test5_postcondition :
  postcondition test5_arr test5_k test5_Expected := by
  unfold postcondition
  constructor
  · intro h
    exfalso
    apply h
    exact ⟨0, 2, by omega, by native_decide, by native_decide⟩
  · intro _
    right
    refine ⟨by native_decide, ⟨0, 4, by omega, by native_decide, by native_decide, by native_decide⟩, ?_⟩
    intro start stop h_lt h_le h_mod
    have h_size : test5_arr.size = 4 := by native_decide
    have h_stop_le : stop ≤ 4 := by simp only [h_size] at h_le; exact h_le
    have h_k : test5_k.toNat = 2 := by native_decide
    simp only [h_k] at h_mod
    have h_exp : test5_Expected = 9 := by native_decide
    simp only [h_exp]
    -- Valid subarrays: (0,2), (1,3), (2,4), (0,4)
    -- Their sums: 5, 8, 4, 9
    have h_start_lt : start < 4 := by omega
    match start, stop with
    | 0, 0 => omega
    | 0, 1 => omega
    | 0, 2 => native_decide
    | 0, 3 => simp_all
    | 0, 4 => native_decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => simp_all
    | 1, 3 => native_decide
    | 1, 4 => simp_all
    | 2, 0 => omega
    | 2, 1 => omega
    | 2, 2 => omega
    | 2, 3 => simp_all
    | 2, 4 => native_decide
    | 3, 0 => omega
    | 3, 1 => omega
    | 3, 2 => omega
    | 3, 3 => omega
    | 3, 4 => simp_all
    | n + 4, _ => omega

theorem uniqueness (arr : Array Int) (k : Int):
  precondition arr k →
  (∀ ret1 ret2,
    postcondition arr k ret1 →
    postcondition arr k ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  -- Case split on whether valid subarrays exist
  by_cases h_exists : ∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0
  · -- Valid subarrays exist
    have h1 := hpost1.2 h_exists
    have h2 := hpost2.2 h_exists
    -- Now h1 and h2 are the disjunctions for ret1 and ret2
    cases h1 with
    | inl h1_left =>
      -- ret1 = 0 and all sums ≤ 0
      cases h2 with
      | inl h2_left =>
        -- ret2 = 0 too
        exact h1_left.1.trans h2_left.1.symm
      | inr h2_right =>
        -- ret2 > 0 and achieved by some subarray
        -- But all sums ≤ 0, so ret2 should be ≤ 0, contradiction with ret2 > 0
        obtain ⟨h2_pos, ⟨start, stop, hlt, hle, hmod, hsum⟩, _⟩ := h2_right
        have hle0 := h1_left.2 start stop hlt hle hmod
        rw [hsum] at hle0
        omega
    | inr h1_right =>
      -- ret1 > 0 and achieved and maximal
      cases h2 with
      | inl h2_left =>
        -- ret2 = 0 and all sums ≤ 0
        -- But ret1 is achieved by some subarray with positive sum
        obtain ⟨h1_pos, ⟨start, stop, hlt, hle, hmod, hsum⟩, _⟩ := h1_right
        have hle0 := h2_left.2 start stop hlt hle hmod
        rw [hsum] at hle0
        omega
      | inr h2_right =>
        -- Both ret1 > 0 and ret2 > 0, both achieved and maximal
        obtain ⟨_, ⟨s1, t1, hlt1, hle1, hmod1, hsum1⟩, hmax1⟩ := h1_right
        obtain ⟨_, ⟨s2, t2, hlt2, hle2, hmod2, hsum2⟩, hmax2⟩ := h2_right
        -- ret1 is achieved at (s1, t1), so ret1 ≤ ret2 by maximality of ret2
        have h_le1 : ret1 ≤ ret2 := by
          have := hmax2 s1 t1 hlt1 hle1 hmod1
          rw [hsum1] at this
          exact this
        -- ret2 is achieved at (s2, t2), so ret2 ≤ ret1 by maximality of ret1
        have h_le2 : ret2 ≤ ret1 := by
          have := hmax1 s2 t2 hlt2 hle2 hmod2
          rw [hsum2] at this
          exact this
        exact Int.le_antisymm h_le1 h_le2
  · -- No valid subarrays exist
    have hne : ¬∃ start stop : Nat, start < stop ∧ stop ≤ arr.size ∧ (stop - start) % k.toNat = 0 := h_exists
    have h1 := hpost1.1 hne
    have h2 := hpost2.1 hne
    exact h1.trans h2.symm
end Proof
