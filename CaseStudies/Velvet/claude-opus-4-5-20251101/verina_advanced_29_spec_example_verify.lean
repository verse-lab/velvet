import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isGoodList (l : List Nat) (k : Nat) : Bool :=
  l.all (fun x => l.count x ≤ k)

def sublist (l : List Nat) (start : Nat) (stop : Nat) : List Nat :=
  (l.drop start).take (stop - start)

def existsGoodSubarrayOfLength (nums : List Nat) (k : Nat) (len : Nat) : Prop :=
  ∃ start : Nat, start + len ≤ nums.length ∧ isGoodList (sublist nums start (start + len)) k = true



def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0 ∧ nums.length > 0



def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=

  result ≥ 1 ∧
  result ≤ nums.length ∧

  existsGoodSubarrayOfLength nums k result ∧

  (∀ len : Nat, len > result → len ≤ nums.length → ¬existsGoodSubarrayOfLength nums k len)


def test1_nums : List Nat := [1, 2, 3, 1, 2, 3, 1, 2]

def test1_k : Nat := 2

def test1_Expected : Nat := 6

def test2_nums : List Nat := [1, 2, 1, 2, 1, 2, 1, 2]

def test2_k : Nat := 1

def test2_Expected : Nat := 2

def test3_nums : List Nat := [5, 5, 5, 5, 5, 5, 5]

def test3_k : Nat := 4

def test3_Expected : Nat := 4







section Proof
theorem test1_precondition :
  precondition test1_nums test1_k := by
  unfold precondition test1_nums test1_k
  simp

theorem test1_postcondition :
  postcondition test1_nums test1_k test1_Expected := by
  unfold postcondition test1_nums test1_k test1_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 6 ≥ 1
    decide
  · -- 6 ≤ 8
    decide
  · -- exists good subarray of length 6
    unfold existsGoodSubarrayOfLength
    use 0
    constructor
    · decide
    · native_decide
  · -- no good subarray of length > 6
    unfold existsGoodSubarrayOfLength
    intro len hlen hlen2
    simp only [not_exists, not_and]
    intro start hstart
    -- Need to compute that the list length is 8
    simp only [List.length_cons, List.length_nil] at hlen2 hstart
    -- len > 6 and len ≤ 8, so len ∈ {7, 8}
    -- start + len ≤ 8, so start ≤ 8 - len
    have hlen_bound : len = 7 ∨ len = 8 := by omega
    rcases hlen_bound with rfl | rfl
    · -- len = 7
      have hstart_bound : start ≤ 1 := by omega
      interval_cases start <;> native_decide
    · -- len = 8
      have hstart_bound : start = 0 := by omega
      subst hstart_bound
      native_decide

theorem test2_precondition :
  precondition test2_nums test2_k := by
  unfold precondition test2_nums test2_k
  simp

theorem test2_postcondition :
  postcondition test2_nums test2_k test2_Expected := by
  unfold postcondition test2_nums test2_k test2_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · unfold existsGoodSubarrayOfLength
    use 0
    native_decide
  · intro len hlen hlen'
    unfold existsGoodSubarrayOfLength
    simp only [List.length] at hlen'
    intro ⟨start, hstart, hgood⟩
    have h1 : len ≤ 8 := hlen'
    have h2 : len > 2 := hlen
    have h3 : start + len ≤ 8 := hstart
    simp only [List.length] at hstart
    match len with
    | 3 => 
      match start with
      | 0 | 1 | 2 | 3 | 4 | 5 => simp [sublist, isGoodList, List.drop, List.take, List.all, List.count] at hgood
      | n + 6 => omega
    | 4 =>
      match start with
      | 0 | 1 | 2 | 3 | 4 => simp [sublist, isGoodList, List.drop, List.take, List.all, List.count] at hgood
      | n + 5 => omega
    | 5 =>
      match start with
      | 0 | 1 | 2 | 3 => simp [sublist, isGoodList, List.drop, List.take, List.all, List.count] at hgood
      | n + 4 => omega
    | 6 =>
      match start with
      | 0 | 1 | 2 => simp [sublist, isGoodList, List.drop, List.take, List.all, List.count] at hgood
      | n + 3 => omega
    | 7 =>
      match start with
      | 0 | 1 => simp [sublist, isGoodList, List.drop, List.take, List.all, List.count] at hgood
      | n + 2 => omega
    | 8 =>
      match start with
      | 0 => simp [sublist, isGoodList, List.drop, List.take, List.all, List.count] at hgood
      | n + 1 => omega
    | 0 | 1 | 2 => omega
    | n + 9 => omega

theorem test3_precondition :
  precondition test3_nums test3_k := by
  unfold precondition test3_nums test3_k
  simp

theorem test3_postcondition :
  postcondition test3_nums test3_k test3_Expected := by
  unfold postcondition test3_nums test3_k test3_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · native_decide
  · unfold existsGoodSubarrayOfLength
    exact ⟨0, by native_decide, by native_decide⟩
  · intro len hlen hlen_bound
    unfold existsGoodSubarrayOfLength
    simp only [not_exists, not_and]
    intro start hstart
    have hlist_len : [5, 5, 5, 5, 5, 5, 5].length = 7 := by native_decide
    rw [hlist_len] at hlen_bound hstart
    have hlen' : len > 4 := hlen
    have hlen_bound' : len ≤ 7 := hlen_bound
    interval_cases len
    · -- len = 5
      have hs : start ≤ 2 := by omega
      interval_cases start <;> native_decide
    · -- len = 6
      have hs : start ≤ 1 := by omega
      interval_cases start <;> native_decide
    · -- len = 7
      have hs : start ≤ 0 := by omega
      interval_cases start <;> native_decide

theorem uniqueness (nums : List Nat) (k : Nat):
  precondition nums k →
  (∀ ret1 ret2,
    postcondition nums k ret1 →
    postcondition nums k ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract components from postconditions
  obtain ⟨_hge1_1, hle1, hexists1, hmax1⟩ := hpost1
  obtain ⟨_hge2_1, hle2, hexists2, hmax2⟩ := hpost2
  -- Use trichotomy to case split
  rcases Nat.lt_trichotomy ret1 ret2 with hlt | heq | hgt
  · -- Case: ret1 < ret2
    -- ret2 > ret1 and ret2 ≤ nums.length, so by hmax1, no good subarray of length ret2
    have hno : ¬existsGoodSubarrayOfLength nums k ret2 := hmax1 ret2 hlt hle2
    exact absurd hexists2 hno
  · -- Case: ret1 = ret2
    exact heq
  · -- Case: ret1 > ret2 (i.e., ret2 < ret1)
    -- ret1 > ret2 and ret1 ≤ nums.length, so by hmax2, no good subarray of length ret1
    have hno : ¬existsGoodSubarrayOfLength nums k ret1 := hmax2 ret1 hgt hle1
    exact absurd hexists1 hno
end Proof
