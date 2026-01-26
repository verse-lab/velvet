import CaseStudies.Velvet.Std
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    verina_basic_24: difference between first even and first odd integers in an array.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. The array is assumed non-empty and contains at least one even element and at least one odd element.
    3. “First even” means the element at the smallest index `i` such that `Even (a[i]!)`.
    4. “First odd” means the element at the smallest index `j` such that `Odd (a[j]!)`.
    5. The output is an integer equal to (first even element) minus (first odd element).
    6. The result should be uniquely determined by the minimality of these indices.
-/

section Specs
-- Helper: predicate that an index is the first index satisfying a property.
-- We phrase it using Nat indices and `a[i]!` access, with explicit bounds.
def IsFirstIdx (a : Array Int) (p : Int → Prop) (i : Nat) : Prop :=
  i < a.size ∧ p (a[i]!) ∧ ∀ k : Nat, k < i → ¬ p (a[k]!)

-- Preconditions: array must contain at least one even and at least one odd element.
def precondition (a : Array Int) : Prop :=
  (∃ i : Nat, i < a.size ∧ Even (a[i]!)) ∧
  (∃ j : Nat, j < a.size ∧ Odd (a[j]!))

-- Postcondition: there exist minimal indices of first even and first odd,
-- and result is their difference.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ i : Nat, ∃ j : Nat,
    IsFirstIdx a (fun x => Even x) i ∧
    IsFirstIdx a (fun x => Odd x) j ∧
    result = a[i]! - a[j]!
end Specs

section Impl
method firstEvenOddDifference (a : Array Int) return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  let mut i : Nat := 0
  let mut foundEven : Bool := false
  let mut evenVal : Int := 0
  while (i < a.size ∧ foundEven = false)
    -- Invariant: i is always within [0, a.size]; needed for safe access and for reasoning about termination.
    -- Init: i=0. Preserved: only incremented under guard i < a.size.
    invariant "feod_i_bounds" i ≤ a.size
    -- Invariant: all indices scanned so far (< i) are not even; this gives the minimality part for the first-even witness.
    -- Init: vacuously true at i=0. Preserved: if a[i] is not even we increment i, extending the range by one.
    invariant "feod_no_even_before_i" (∀ k : Nat, k < i → ¬ Even (a[k]!))
    -- Invariant: once foundEven is true, current i points to an even element, evenVal matches it, and it's the first such index.
    -- Established when setting foundEven := true; preserved since loop stops when foundEven becomes true.
    invariant "feod_found_even_first" (foundEven = true → (i < a.size ∧ Even (a[i]!) ∧ evenVal = a[i]! ∧ ∀ k : Nat, k < i → ¬ Even (a[k]!)))
    -- Invariant: if we haven't found an even yet, there still exists an even at some index t ≥ i (from precondition).
    -- This prevents the loop from exiting by i=a.size with foundEven=false.
    invariant "feod_even_exists_ahead" (foundEven = false → ∃ t : Nat, i ≤ t ∧ t < a.size ∧ Even (a[t]!))
    -- Invariant: if we reach/past the end, then we must have found an even.
    invariant "feod_end_implies_foundEven" (a.size ≤ i → foundEven = true)
    done_with (i >= a.size ∨ foundEven = true)
  do
    if Even (a[i]!) then
      evenVal := a[i]!
      foundEven := true
    else
      i := i + 1
  let mut j : Nat := 0
  let mut foundOdd : Bool := false
  let mut oddVal : Int := 0
  while (j < a.size ∧ foundOdd = false)
    -- Invariant: j is always within [0, a.size]; needed for safe access and for reasoning about termination.
    -- Init: j=0. Preserved: only incremented under guard j < a.size.
    invariant "feod_j_bounds" j ≤ a.size
    -- Invariant: all indices scanned so far (< j) are not odd; this gives the minimality part for the first-odd witness.
    -- Init: vacuously true at j=0. Preserved: if a[j] is not odd we increment j, extending the range by one.
    invariant "feod_no_odd_before_j" (∀ k : Nat, k < j → ¬ Odd (a[k]!))
    -- Invariant: once foundOdd is true, current j points to an odd element, oddVal matches it, and it's the first such index.
    -- Established when setting foundOdd := true; preserved since loop stops when foundOdd becomes true.
    invariant "feod_found_odd_first" (foundOdd = true → (j < a.size ∧ Odd (a[j]!) ∧ oddVal = a[j]! ∧ ∀ k : Nat, k < j → ¬ Odd (a[k]!)))
    -- Invariant: if we haven't found an odd yet, there still exists an odd at some index t ≥ j (from precondition).
    -- This prevents the loop from exiting by j=a.size with foundOdd=false.
    invariant "feod_odd_exists_ahead" (foundOdd = false → ∃ t : Nat, j ≤ t ∧ t < a.size ∧ Odd (a[t]!))
    -- Invariant: if we reach/past the end, then we must have found an odd.
    invariant "feod_end_implies_foundOdd" (a.size ≤ j → foundOdd = true)
    done_with (j >= a.size ∨ foundOdd = true)
  do
    if Odd (a[j]!) then
      oddVal := a[j]!
      foundOdd := true
    else
      j := j + 1
  return evenVal - oddVal
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct firstEvenOddDifference by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    : ∃ t < a.size, Even a[t]! := by
    rcases require_1.1 with ⟨i, hi_lt, hi_even⟩
    exact ⟨i, hi_lt, hi_even⟩

theorem goal_1
    (a : Array ℤ)
    (require_1 : precondition a)
    : ¬a = #[] := by
    rcases require_1.1 with ⟨i, hi_lt, hi_even⟩
    intro h
    have : i < 0 := by
      simpa [h] using hi_lt
    exact (Nat.not_lt_zero i) this

theorem goal_2
    (a : Array ℤ)
    (require_1 : precondition a)
    (evenVal : ℤ)
    (foundEven : Bool)
    (i : ℕ)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    : ∃ t < a.size, Odd a[t]! := by
  rcases require_1.2 with ⟨t, ht, hodd⟩
  exact ⟨t, ht, hodd⟩

theorem goal_3
    (a : Array ℤ)
    (evenVal : ℤ)
    (foundEven : Bool)
    (i : ℕ)
    (invariant_feod_end_implies_foundEven : a.size ≤ i → foundEven = true)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (foundOdd : Bool)
    (j : ℕ)
    (oddVal : ℤ)
    (invariant_feod_end_implies_foundOdd : a.size ≤ j → foundOdd = true)
    (i_5 : Bool)
    (i_6 : ℕ)
    (oddVal_1 : ℤ)
    (invariant_feod_found_even_first : foundEven = true → i < a.size ∧ Even a[i]! ∧ evenVal = a[i]! ∧ ∀ k < i, Odd a[k]!)
    (done_1 : a.size ≤ i ∨ foundEven = true)
    (i_4 : evenVal = i_1 ∧ foundEven = i_2 ∧ i = i_3)
    (invariant_feod_found_odd_first : foundOdd = true → j < a.size ∧ Odd a[j]! ∧ oddVal = a[j]! ∧ ∀ k < j, Even a[k]!)
    (done_2 : a.size ≤ j ∨ foundOdd = true)
    (i_7 : foundOdd = i_5 ∧ j = i_6 ∧ oddVal = oddVal_1)
    : postcondition a (i_1 - oddVal_1) := by
    -- derive foundEven = true
    have hFoundEven : foundEven = true := by
      cases done_1 with
      | inl hsz => exact invariant_feod_end_implies_foundEven hsz
      | inr hfe => exact hfe

    -- derive foundOdd = true
    have hFoundOdd : foundOdd = true := by
      cases done_2 with
      | inl hsz => exact invariant_feod_end_implies_foundOdd hsz
      | inr hfo => exact hfo

    -- unpack "found first" invariants
    have hEvenFirst :
        i < a.size ∧ Even a[i]! ∧ evenVal = a[i]! ∧ ∀ k < i, Odd a[k]! :=
      invariant_feod_found_even_first hFoundEven
    have hOddFirst :
        j < a.size ∧ Odd a[j]! ∧ oddVal = a[j]! ∧ ∀ k < j, Even a[k]! :=
      invariant_feod_found_odd_first hFoundOdd

    rcases hEvenFirst with ⟨hi_lt, hi_even, hevenVal_eq, hi_prevOdd⟩
    rcases hOddFirst with ⟨hj_lt, hj_odd, hoddVal_eq, hj_prevEven⟩

    -- connect final returned values to loop vars
    rcases i_4 with ⟨h_evenVal_i1, _h_foundEven_i2, _h_i_i3⟩
    rcases i_7 with ⟨_h_foundOdd_i5, _h_j_i6, h_oddVal_oddVal1⟩

    refine ⟨i, j, ?_, ?_, ?_⟩
    · -- IsFirstIdx for Even at i
      refine And.intro hi_lt (And.intro hi_even ?_)
      intro k hk
      have hok : Odd a[k]! := hi_prevOdd k hk
      -- Odd x → ¬ Even x
      exact (Int.not_even_iff_odd.mpr hok)
    · -- IsFirstIdx for Odd at j
      refine And.intro hj_lt (And.intro hj_odd ?_)
      intro k hk
      have hek : Even a[k]! := hj_prevEven k hk
      -- Even x → ¬ Odd x
      exact (Int.not_odd_iff_even.mpr hek)
    · -- result equation: i_1 - oddVal_1 = a[i]! - a[j]!
      have hi1 : i_1 = evenVal := by simpa using h_evenVal_i1.symm
      have hod1 : oddVal_1 = oddVal := by simpa using h_oddVal_oddVal1.symm
      calc
        i_1 - oddVal_1
            = evenVal - oddVal := by simp [hi1, hod1]
        _   = a[i]! - oddVal := by simp [hevenVal_eq]
        _   = a[i]! - a[j]! := by simp [hoddVal_eq]

prove_correct firstEvenOddDifference by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1)
  exact (goal_1 a require_1)
  exact (goal_2 a require_1 evenVal foundEven i i_1 i_2 i_3)
  exact (goal_3 a evenVal foundEven i invariant_feod_end_implies_foundEven i_1 i_2 i_3 foundOdd j oddVal invariant_feod_end_implies_foundOdd i_5 i_6 oddVal_1 invariant_feod_found_even_first done_1 i_4 invariant_feod_found_odd_first done_2 i_7)
end Proof
