import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlySorted (l : List Nat) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! < l[j]!



def precondition (l : List Nat) : Prop :=
  isStrictlySorted l



def ensures1 (l : List Nat) (result : Nat) : Prop :=
  result ∉ l


def ensures2 (l : List Nat) (result : Nat) : Prop :=
  ∀ k : Nat, k < result → k ∈ l

def postcondition (l : List Nat) (result : Nat) : Prop :=
  ensures1 l result ∧ ensures2 l result


def test1_l : List Nat := [0, 1, 2, 4, 5]

def test1_Expected : Nat := 3

def test2_l : List Nat := []

def test2_Expected : Nat := 0

def test4_l : List Nat := [0, 1, 2, 3, 4]

def test4_Expected : Nat := 5







section Proof
theorem test1_precondition :
  precondition test1_l := by
  unfold precondition isStrictlySorted test1_l
  intro i j hij hj
  -- We need to show [0, 1, 2, 4, 5][i]! < [0, 1, 2, 4, 5][j]!
  -- where i < j and j < 5
  simp only [List.length] at hj
  -- j < 5, so j ∈ {0, 1, 2, 3, 4}
  -- i < j, so depending on j, i has limited values
  match j with
  | 0 => omega  -- impossible since i < 0
  | 1 => 
    match i with
    | 0 => native_decide
    | _ + 1 => omega
  | 2 =>
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | _ + 2 => omega
  | 3 =>
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | _ + 3 => omega
  | 4 =>
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | _ + 4 => omega
  | _ + 5 => omega

theorem test1_postcondition :
  postcondition test1_l test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_l test1_Expected
  constructor
  · -- ensures1: 3 ∉ [0, 1, 2, 4, 5]
    decide
  · -- ensures2: ∀ k, k < 3 → k ∈ [0, 1, 2, 4, 5]
    intro k hk
    interval_cases k <;> decide

theorem test2_precondition :
  precondition test2_l := by
  unfold precondition isStrictlySorted test2_l
  intro i j _ hj
  simp at hj

theorem test2_postcondition :
  postcondition test2_l test2_Expected := by
  unfold postcondition ensures1 ensures2 test2_l test2_Expected
  constructor
  · exact List.not_mem_nil
  · intro k hk
    exact absurd hk (Nat.not_lt_zero k)

theorem test4_precondition :
  precondition test4_l := by
  unfold precondition isStrictlySorted test4_l
  intro i j hij hj
  simp only [List.length] at hj
  -- For the list [0, 1, 2, 3, 4], element at index k is k
  -- So we need i < j, which is exactly hij
  match j with
  | 0 => omega  -- impossible since i < 0
  | 1 => 
    match i with
    | 0 => native_decide
    | _ + 1 => omega
  | 2 =>
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | _ + 2 => omega
  | 3 =>
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | _ + 3 => omega
  | 4 =>
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | _ + 4 => omega
  | _ + 5 => omega

theorem test4_postcondition :
  postcondition test4_l test4_Expected := by
  unfold postcondition ensures1 ensures2 test4_l test4_Expected
  constructor
  · decide
  · intro k hk
    interval_cases k <;> decide

theorem uniqueness (l : List Nat):
  precondition l →
  (∀ ret1 ret2,
    postcondition l ret1 →
    postcondition l ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract the components of postcondition
  have h1_notin : ret1 ∉ l := hpost1.1
  have h1_all : ∀ k : Nat, k < ret1 → k ∈ l := hpost1.2
  have h2_notin : ret2 ∉ l := hpost2.1
  have h2_all : ∀ k : Nat, k < ret2 → k ∈ l := hpost2.2
  -- Use trichotomy to case split on ret1 vs ret2
  rcases Nat.lt_trichotomy ret1 ret2 with hlt | heq | hgt
  · -- Case: ret1 < ret2
    -- By h2_all, since ret1 < ret2, we have ret1 ∈ l
    have : ret1 ∈ l := h2_all ret1 hlt
    -- But h1_notin says ret1 ∉ l, contradiction
    exact absurd this h1_notin
  · -- Case: ret1 = ret2
    exact heq
  · -- Case: ret2 < ret1
    -- By h1_all, since ret2 < ret1, we have ret2 ∈ l
    have : ret2 ∈ l := h1_all ret2 hgt
    -- But h2_notin says ret2 ∉ l, contradiction
    exact absurd this h2_notin
end Proof
