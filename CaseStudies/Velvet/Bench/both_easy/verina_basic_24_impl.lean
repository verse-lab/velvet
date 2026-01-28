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

abbrev Int.isEven (n : Int) : Prop :=
  n % 2 = 0
abbrev Int.isOdd (n : Int) : Prop :=
  n % 2 ≠ 0

-- Helper: predicate that an index is the first index satisfying a property.
-- We phrase it using Nat indices and `a[i]!` access, with explicit bounds.
@[grind]
def IsFirstIdx (a : Array Int) (p : Int → Prop) (i : Nat) : Prop :=
  i < a.size ∧ p (a[i]!) ∧ ∀ k : Nat, k < i → ¬ p (a[k]!)

end Specs

section Impl
method firstEvenOddDifference (a : Array Int) return (result : Int)
  require ∃ i : Nat, i < a.size ∧ a[i]!.isEven
  require ∃ j : Nat, j < a.size ∧ a[j]!.isOdd
  ensures ∃ i : Nat, ∃ j : Nat,
    IsFirstIdx a (fun x => x.isEven) i ∧
    IsFirstIdx a (fun x => x.isOdd) j ∧
    result = a[i]! - a[j]!
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
    invariant "feod_no_even_before_i" (∀ k : Nat, k < i → ¬ a[k]!.isEven)
    -- Invariant: once foundEven is true, current i points to an even element, evenVal matches it, and it's the first such index.
    -- Established when setting foundEven := true; preserved since loop stops when foundEven becomes true.
    invariant "feod_found_even_first" (foundEven = true → (i < a.size ∧ a[i]!.isEven ∧ evenVal = a[i]! ∧ ∀ k : Nat, k < i → ¬ a[k]!.isEven))
    -- Invariant: if we haven't found an even yet, there still exists an even at some index t ≥ i (from precondition).
    -- This prevents the loop from exiting by i=a.size with foundEven=false.
    invariant "feod_even_exists_ahead" (foundEven = false → ∃ t : Nat, i ≤ t ∧ t < a.size ∧ a[t]!.isEven)
    -- Invariant: if we reach/past the end, then we must have found an even.
    invariant "feod_end_implies_foundEven" (a.size ≤ i → foundEven = true)
    done_with (i >= a.size ∨ foundEven = true)
  do
    if a[i]!.isEven then
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
    invariant "feod_no_odd_before_j" (∀ k : Nat, k < j → ¬ a[k]!.isOdd)
    -- Invariant: once foundOdd is true, current j points to an odd element, oddVal matches it, and it's the first such index.
    -- Established when setting foundOdd := true; preserved since loop stops when foundOdd becomes true.
    invariant "feod_found_odd_first" (foundOdd = true → (j < a.size ∧ a[j]!.isOdd ∧ oddVal = a[j]! ∧ ∀ k : Nat, k < j → ¬ a[k]!.isOdd))
    -- Invariant: if we haven't found an odd yet, there still exists an odd at some index t ≥ j (from precondition).
    -- This prevents the loop from exiting by j=a.size with foundOdd=false.
    invariant "feod_odd_exists_ahead" (foundOdd = false → ∃ t : Nat, j ≤ t ∧ t < a.size ∧ a[t]!.isOdd)
    -- Invariant: if we reach/past the end, then we must have found an odd.
    invariant "feod_end_implies_foundOdd" (a.size ≤ j → foundOdd = true)
    done_with (j >= a.size ∨ foundOdd = true)
  do
    if a[j]!.isOdd then
      oddVal := a[j]!
      foundOdd := true
    else
      j := j + 1
  return evenVal - oddVal
end Impl

section Proof
set_option maxHeartbeats 10000000


prove_correct firstEvenOddDifference by
  loom_solve <;> (try simp at *; expose_names)


end Proof
