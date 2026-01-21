import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def allDistinct (nums : List Nat) : Prop :=
  nums.Nodup

def allInRange (nums : List Nat) (n : Nat) : Prop :=
  ∀ x, x ∈ nums → x ≤ n



def precondition (nums : List Nat) :=
  allDistinct nums ∧ allInRange nums nums.length



def ensures1 (nums : List Nat) (result : Nat) :=
  result ∉ nums


def ensures2 (nums : List Nat) (result : Nat) :=
  result ≤ nums.length


def ensures3 (nums : List Nat) (result : Nat) :=
  ∀ k, k ≤ nums.length → k ≠ result → k ∈ nums

def postcondition (nums : List Nat) (result : Nat) :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result


def test1_nums : List Nat := [3, 0, 1]

def test1_Expected : Nat := 2

def test4_nums : List Nat := [0]

def test4_Expected : Nat := 1

def test5_nums : List Nat := [1]

def test5_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums allDistinct allInRange
  constructor
  · -- Prove [3, 0, 1].Nodup
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil]
    decide
  · -- Prove ∀ x, x ∈ [3, 0, 1] → x ≤ 3
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · -- x = 3
      decide
    · -- x = 0
      decide
    · -- x = 1
      decide

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test1_nums test1_Expected
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro k hk hne
    simp only [List.length] at hk
    interval_cases k
    · simp [List.mem_cons]
    · simp [List.mem_cons]
    · omega
    · simp [List.mem_cons]

theorem test4_precondition : precondition test4_nums := by
  unfold precondition test4_nums allDistinct allInRange
  constructor
  · -- Prove [0].Nodup
    exact List.nodup_singleton 0
  · -- Prove ∀ x, x ∈ [0] → x ≤ [0].length
    intro x hx
    simp [List.length_singleton]
    rw [List.mem_singleton] at hx
    omega

theorem test4_postcondition :
  postcondition test4_nums test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test4_nums test4_Expected
  refine ⟨?_, ?_, ?_⟩
  · -- ensures1: 1 ∉ [0]
    simp [List.mem_singleton]
  · -- ensures2: 1 ≤ 1
    simp [List.length_singleton]
  · -- ensures3: ∀ k, k ≤ 1 → k ≠ 1 → k ∈ [0]
    intro k hk hne
    simp only [List.length_singleton] at hk
    have : k = 0 := by omega
    simp [this, List.mem_singleton]

theorem test5_precondition :
  precondition test5_nums := by
  unfold precondition test5_nums allDistinct allInRange
  constructor
  · -- allDistinct [1] means [1].Nodup
    exact List.nodup_singleton 1
  · -- allInRange [1] 1 means ∀ x, x ∈ [1] → x ≤ 1
    intro x hx
    simp only [List.length_singleton]
    rw [List.mem_singleton] at hx
    simp [hx]

theorem test5_postcondition :
  postcondition test5_nums test5_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test5_nums test5_Expected
  refine ⟨?_, ?_, ?_⟩
  · -- ensures1: 0 ∉ [1]
    simp [List.mem_singleton]
  · -- ensures2: 0 ≤ [1].length = 1
    simp [List.length_singleton]
  · -- ensures3: ∀ k, k ≤ 1 → k ≠ 0 → k ∈ [1]
    intro k hk hne
    simp [List.length_singleton] at hk
    simp [List.mem_singleton]
    omega

theorem uniqueness (nums : List Nat):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  -- Extract the components of postcondition
  unfold postcondition at hpost1 hpost2
  obtain ⟨hnotin1, hle1, hall1⟩ := hpost1
  obtain ⟨hnotin2, hle2, hall2⟩ := hpost2
  unfold ensures1 at hnotin1 hnotin2
  unfold ensures2 at hle1 hle2
  unfold ensures3 at hall1 hall2
  -- Use decidable equality on Nat to case split
  by_cases h : ret1 = ret2
  · exact h
  · -- If ret1 ≠ ret2, we derive a contradiction
    -- Since ret1 ≤ nums.length and ret1 ≠ ret2, by hall2: ret1 ∈ nums
    have hret1_in : ret1 ∈ nums := hall2 ret1 hle1 h
    -- But hnotin1 says ret1 ∉ nums
    exact absurd hret1_in hnotin1
end Proof
