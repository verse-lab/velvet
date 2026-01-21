import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def countFreq (x : Int) (xs : List Int) : Nat :=
  xs.count x


def hasMaxFrequency (x : Int) (xs : List Int) : Prop :=
  ∀ y ∈ xs, countFreq y xs ≤ countFreq x xs


def firstOccurrenceIdx (x : Int) (xs : List Int) : Nat :=
  match xs.findIdx? (· == x) with
  | some idx => idx
  | none => xs.length


def appearsBeforeOrEqual (x : Int) (y : Int) (xs : List Int) : Prop :=
  firstOccurrenceIdx x xs ≤ firstOccurrenceIdx y xs



def precondition (xs : List Int) :=
  xs ≠ []



def ensures1 (xs : List Int) (result : Int) :=
  result ∈ xs


def ensures2 (xs : List Int) (result : Int) :=
  hasMaxFrequency result xs


def ensures3 (xs : List Int) (result : Int) :=
  ∀ y ∈ xs, countFreq y xs = countFreq result xs → appearsBeforeOrEqual result y xs

def postcondition (xs : List Int) (result : Int) :=
  ensures1 xs result ∧ ensures2 xs result ∧ ensures3 xs result


def test1_xs : List Int := [1, 2, 2, 3]

def test1_Expected : Int := 2

def test3_xs : List Int := [9]

def test3_Expected : Int := 9

def test7_xs : List Int := [1, 2, 1, 2]

def test7_Expected : Int := 1







section Proof
theorem test1_precondition :
  precondition test1_xs := by
  unfold precondition test1_xs
  exact List.cons_ne_nil 1 [2, 2, 3]

theorem test1_postcondition_0
    (h_unfold : postcondition test1_xs test1_Expected ↔ ensures1 test1_xs test1_Expected ∧ ensures2 test1_xs test1_Expected ∧ ensures3 test1_xs test1_Expected)
    : ensures1 test1_xs test1_Expected := by
    unfold ensures1 test1_xs test1_Expected
    native_decide

theorem test1_postcondition_1
    (h_ensures1 : ensures1 test1_xs test1_Expected)
    (h_count_2 : countFreq 2 test1_xs = 2)
    (h_count_1 : countFreq 1 test1_xs = 1)
    (h_count_3 : countFreq 3 test1_xs = 1)
    (h_unfold : postcondition test1_xs test1_Expected ↔ ensures1 test1_xs test1_Expected ∧ ensures2 test1_xs test1_Expected ∧ ensures3 test1_xs test1_Expected)
    : ensures2 test1_xs test1_Expected := by
    unfold ensures2 hasMaxFrequency test1_xs test1_Expected
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | rfl | h
    · -- y = 1
      simp only [countFreq] at h_count_1 h_count_2
      unfold countFreq
      simp only [test1_xs] at h_count_1 h_count_2
      omega
    · -- y = 2
      simp only [countFreq] at h_count_2
      unfold countFreq
      simp only [test1_xs] at h_count_2
      omega
    · -- y = 2 again
      simp only [countFreq] at h_count_2
      unfold countFreq
      simp only [test1_xs] at h_count_2
      omega
    · -- y = 3
      simp only [countFreq] at h_count_2 h_count_3
      unfold countFreq
      simp only [test1_xs] at h_count_2 h_count_3
      omega
    · -- empty case (contradiction)
      simp at h

theorem test1_postcondition_2
    (h_ensures1 : ensures1 test1_xs test1_Expected)
    (h_count_2 : countFreq 2 test1_xs = 2)
    (h_count_1 : countFreq 1 test1_xs = 1)
    (h_count_3 : countFreq 3 test1_xs = 1)
    (h_ensures2 : ensures2 test1_xs test1_Expected)
    (h_idx_2 : firstOccurrenceIdx 2 test1_xs = 1)
    (h_idx_1 : firstOccurrenceIdx 1 test1_xs = 0)
    (h_idx_3 : firstOccurrenceIdx 3 test1_xs = 3)
    (h_unfold : postcondition test1_xs test1_Expected ↔ ensures1 test1_xs test1_Expected ∧ ensures2 test1_xs test1_Expected ∧ ensures3 test1_xs test1_Expected)
    : ensures3 test1_xs test1_Expected := by
    unfold ensures3 test1_xs test1_Expected
    intro y hy heq
    unfold appearsBeforeOrEqual
    -- y must be in [1, 2, 2, 3]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · -- y = 1: countFreq 1 xs = 2 contradicts h_count_1
      simp only [test1_xs, test1_Expected] at heq h_count_1 h_count_2
      omega
    · -- y = 2: need firstOccurrenceIdx 2 xs ≤ firstOccurrenceIdx 2 xs
      simp only [test1_xs, test1_Expected] at h_idx_2
      rw [h_idx_2]
    · -- y = 2 again (second occurrence)
      simp only [test1_xs, test1_Expected] at h_idx_2
      rw [h_idx_2]
    · -- y = 3: countFreq 3 xs = 2 contradicts h_count_3
      simp only [test1_xs, test1_Expected] at heq h_count_3 h_count_2
      omega

theorem test1_postcondition :
  postcondition test1_xs test1_Expected := by
  -- First, unfold the main definitions to see what we need to prove
  have h_unfold : postcondition test1_xs test1_Expected = 
    (ensures1 test1_xs test1_Expected ∧ ensures2 test1_xs test1_Expected ∧ ensures3 test1_xs test1_Expected) := by
    (try simp at *; expose_names); exact Eq.to_iff rfl; done
  -- Prove ensures1: 2 ∈ [1, 2, 2, 3]
  have h_ensures1 : ensures1 test1_xs test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_0 h_unfold); done
  -- Compute countFreq 2 [1, 2, 2, 3] = 2
  have h_count_2 : countFreq 2 test1_xs = 2 := by
    (try simp at *; expose_names); exact rfl; done
  -- Compute countFreq 1 [1, 2, 2, 3] = 1
  have h_count_1 : countFreq 1 test1_xs = 1 := by
    (try simp at *; expose_names); exact rfl; done
  -- Compute countFreq 3 [1, 2, 2, 3] = 1
  have h_count_3 : countFreq 3 test1_xs = 1 := by
    (try simp at *; expose_names); exact h_count_1; done
  -- Prove ensures2: hasMaxFrequency 2 [1, 2, 2, 3]
  -- For all y in xs, countFreq y xs ≤ countFreq 2 xs
  have h_ensures2 : ensures2 test1_xs test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_1 h_ensures1 h_count_2 h_count_1 h_count_3 h_unfold); done
  -- Compute firstOccurrenceIdx 2 [1, 2, 2, 3] = 1
  have h_idx_2 : firstOccurrenceIdx 2 test1_xs = 1 := by
    (try simp at *; expose_names); exact h_count_1; done
  -- Compute firstOccurrenceIdx 1 [1, 2, 2, 3] = 0
  have h_idx_1 : firstOccurrenceIdx 1 test1_xs = 0 := by
    (try simp at *; expose_names); exact rfl; done
  -- Compute firstOccurrenceIdx 3 [1, 2, 2, 3] = 3
  have h_idx_3 : firstOccurrenceIdx 3 test1_xs = 3 := by
    (try simp at *; expose_names); exact rfl; done
  -- Prove ensures3: for all y in xs with same frequency as 2, 2 appears before or equal to y
  have h_ensures3 : ensures3 test1_xs test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_2 h_ensures1 h_count_2 h_count_1 h_count_3 h_ensures2 h_idx_2 h_idx_1 h_idx_3 h_unfold); done
  -- Combine all three ensures to prove the postcondition
  exact ⟨h_ensures1, h_ensures2, h_ensures3⟩

theorem test3_precondition :
  precondition test3_xs := by
  unfold precondition test3_xs
  exact List.cons_ne_nil 9 []

theorem test3_postcondition :
  postcondition test3_xs test3_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test3_xs test3_Expected
  constructor
  · -- ensures1: 9 ∈ [9]
    simp [List.mem_singleton]
  · constructor
    · -- ensures2: hasMaxFrequency 9 [9]
      unfold hasMaxFrequency countFreq
      intro y hy
      simp [List.mem_singleton] at hy
      subst hy
      simp
    · -- ensures3: ∀ y ∈ [9], countFreq y [9] = countFreq 9 [9] → appearsBeforeOrEqual 9 y [9]
      intro y hy _
      simp [List.mem_singleton] at hy
      subst hy
      unfold appearsBeforeOrEqual
      simp

theorem test7_precondition :
  precondition test7_xs := by
  unfold precondition test7_xs
  exact List.cons_ne_nil 1 [2, 1, 2]

theorem test7_postcondition :
  postcondition test7_xs test7_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test7_xs test7_Expected
  unfold hasMaxFrequency countFreq appearsBeforeOrEqual firstOccurrenceIdx
  constructor
  · -- ensures1: 1 ∈ [1, 2, 1, 2]
    simp [List.mem_cons]
  · constructor
    · -- ensures2: hasMaxFrequency
      intro y hy
      simp [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | rfl | hfalse
      all_goals native_decide
    · -- ensures3: appearsBeforeOrEqual
      intro y hy hfreq
      simp [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | rfl | hfalse
      all_goals native_decide

theorem uniqueness (xs : List Int):
  precondition xs →
  (∀ ret1 ret2,
    postcondition xs ret1 →
    postcondition xs ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  -- Extract components from postconditions
  unfold postcondition at hpost1 hpost2
  obtain ⟨h1_in, h1_max, h1_first⟩ := hpost1
  obtain ⟨h2_in, h2_max, h2_first⟩ := hpost2
  -- Show frequencies are equal
  unfold ensures2 hasMaxFrequency at h1_max h2_max
  unfold ensures1 at h1_in h2_in
  have hfreq1 : countFreq ret1 xs ≤ countFreq ret2 xs := h2_max ret1 h1_in
  have hfreq2 : countFreq ret2 xs ≤ countFreq ret1 xs := h1_max ret2 h2_in
  have hfreq_eq : countFreq ret1 xs = countFreq ret2 xs := Nat.le_antisymm hfreq1 hfreq2
  -- Apply ensures3 to get both appear before each other
  unfold ensures3 at h1_first h2_first
  have h1_before : appearsBeforeOrEqual ret1 ret2 xs := h1_first ret2 h2_in hfreq_eq.symm
  have h2_before : appearsBeforeOrEqual ret2 ret1 xs := h2_first ret1 h1_in hfreq_eq
  -- Show first occurrence indices are equal
  unfold appearsBeforeOrEqual at h1_before h2_before
  have hidx_eq : firstOccurrenceIdx ret1 xs = firstOccurrenceIdx ret2 xs := 
    Nat.le_antisymm h1_before h2_before
  -- Now show that equal first occurrence index implies equal elements
  unfold firstOccurrenceIdx at hidx_eq
  -- Case analysis on findIdx? results
  cases h1 : xs.findIdx? (· == ret1) with
  | none =>
    -- If ret1 not found, contradiction with ret1 ∈ xs
    have hex1 : ∃ x ∈ xs, (x == ret1) = true := ⟨ret1, h1_in, by simp [BEq.beq]⟩
    have hsome1 := List.findIdx?_eq_some_of_exists hex1
    rw [h1] at hsome1
    exact absurd hsome1.symm (Option.noConfusion)
  | some i1 =>
    cases h2 : xs.findIdx? (· == ret2) with
    | none =>
      -- If ret2 not found, contradiction with ret2 ∈ xs
      have hex2 : ∃ x ∈ xs, (x == ret2) = true := ⟨ret2, h2_in, by simp [BEq.beq]⟩
      have hsome2 := List.findIdx?_eq_some_of_exists hex2
      rw [h2] at hsome2
      exact absurd hsome2.symm (Option.noConfusion)
    | some i2 =>
      -- Both found at indices i1 and i2
      simp only [h1, h2] at hidx_eq
      -- i1 = i2
      have hinfo1 := List.findIdx?_eq_some_iff_getElem.mp h1
      have hinfo2 := List.findIdx?_eq_some_iff_getElem.mp h2
      obtain ⟨hlt1, hsat1, _⟩ := hinfo1
      obtain ⟨hlt2, hsat2, _⟩ := hinfo2
      -- xs[i1] == ret1 and xs[i2] == ret2, and i1 = i2
      simp only [beq_iff_eq] at hsat1 hsat2
      -- hsat1 : xs[i1] = ret1, hsat2 : xs[i2] = ret2
      -- Since i1 = i2, xs[i1] = xs[i2]
      have heq_idx : xs[i1] = xs[i2] := by
        subst hidx_eq
        rfl
      -- Now ret1 = xs[i1] = xs[i2] = ret2
      calc ret1 = xs[i1] := hsat1.symm
        _ = xs[i2] := heq_idx
        _ = ret2 := hsat2
end Proof
