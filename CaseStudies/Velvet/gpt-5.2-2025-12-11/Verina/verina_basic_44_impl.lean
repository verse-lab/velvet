import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isOddAtIndexOdd: verify that every odd index in an array of integers holds an odd integer.
    Natural language breakdown:
    1. Input is an array `a` of integers.
    2. Indices are natural numbers from 0 to `a.size - 1`.
    3. An index `i` is considered an odd index when `i % 2 = 1`.
    4. An integer value `x` is considered odd when `x % 2 ≠ 0`.
    5. The function returns true exactly when: for every valid index `i`, if `i` is odd then `a[i]!` is odd.
    6. If there exists a valid odd index whose element is not odd, the function returns false.
    7. There are no preconditions; the function must work for any input array.
    8. For an empty array, the condition is vacuously true.
-/

section Specs
-- Helper predicate: all elements at odd indices are odd.
-- We use the concrete index condition `i % 2 = 1` and the concrete Int oddness condition `x % 2 ≠ 0`.
-- Note: `i` is a Nat index, while `a[i]!` is an Int value.
def OddIndexElementsOdd (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → i % 2 = 1 → (a[i]!) % 2 ≠ 0

-- No preconditions.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ OddIndexElementsOdd a
end Specs

section Impl
method isOddAtIndexOdd (a : Array Int) return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
    let mut ok := true
    let mut i : Nat := 0

    while i < a.size ∧ ok
      -- Invariant: loop index stays within array bounds.
      -- Init: i = 0. Pres: i := i+1 and guard gives i < a.size. Exit: with i ≥ a.size we have scanned all indices.
      invariant "inv_bounds" i ≤ a.size
      -- Invariant (success case): if ok is still true, then all previously visited odd indices satisfy oddness.
      -- This matches OddIndexElementsOdd on the processed prefix [0,i).
      invariant "inv_prefix_ok" (ok = true → ∀ j : Nat, j < i → j < a.size → j % 2 = 1 → (a[j]!) % 2 ≠ 0)
      -- Invariant (failure case): if ok is false, we have found a concrete counterexample in the processed prefix.
      -- This enables proving the converse direction of the postcondition: OddIndexElementsOdd a → ok = true.
      invariant "inv_prefix_bad" (ok = false → ∃ j : Nat, j < i ∧ j < a.size ∧ j % 2 = 1 ∧ (a[j]!) % 2 = 0)
      done_with (i ≥ a.size ∨ ok = false)
    do
      if i % 2 = 1 then
        if (a[i]!) % 2 = 0 then
          ok := false
        else
          pure ()
      else
        pure ()
      i := i + 1

    return ok
end Impl

section TestCases
-- Test case 1: example from prompt
-- Odd indices are 1 and 3; elements are 2 and 4, which are not odd.
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := false

-- Test case 2: all odd numbers; odd indices contain odd elements
-- Odd indices: 1 ↦ 3, 3 ↦ 7.
def test2_a : Array Int := #[1, 3, 5, 7, 9]
def test2_Expected : Bool := true

-- Test case 3: all even numbers; odd indices contain even elements
-- Odd indices: 1 ↦ 4, 3 ↦ 8.
def test3_a : Array Int := #[2, 4, 6, 8, 10]
def test3_Expected : Bool := false

-- Test case 4: empty array; vacuously true
def test4_a : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: single element; there are no odd indices
def test5_a : Array Int := #[7]
def test5_Expected : Bool := true

-- Test case 6: alternating even/odd so odd indices contain odd elements
def test6_a : Array Int := #[0, 1, 0, 1]
def test6_Expected : Bool := true

-- Test case 7: odd indices contain even elements
def test7_a : Array Int := #[0, 2, 4, 6]
def test7_Expected : Bool := false

-- Test case 8: includes negative odds at odd indices
-- Odd indices: 1 ↦ -3 (odd), 3 ↦ 5 (odd).
def test8_a : Array Int := #[2, -3, 4, 5]
def test8_Expected : Bool := true

-- Test case 9: size 2 array where index 1 exists and violates oddness
-- Odd index: 1 ↦ 0 (not odd).
def test9_a : Array Int := #[11, 0]
def test9_Expected : Bool := false

-- Recommend to validate: test1, test2, test4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isOddAtIndexOdd test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isOddAtIndexOdd test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isOddAtIndexOdd test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isOddAtIndexOdd test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isOddAtIndexOdd test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isOddAtIndexOdd test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isOddAtIndexOdd test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isOddAtIndexOdd test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isOddAtIndexOdd test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for isOddAtIndexOdd
prove_precondition_decidable_for isOddAtIndexOdd
prove_postcondition_decidable_for isOddAtIndexOdd
derive_tester_for isOddAtIndexOdd
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := isOddAtIndexOddTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isOddAtIndexOdd by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (ok : Bool)
    (invariant_inv_bounds : i ≤ a.size)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (invariant_inv_prefix_ok : ok = true → ∀ j < i, j < a.size → j % 2 = 1 → a[j]! % 2 = 1)
    (invariant_inv_prefix_bad : ok = false → ∃ j < i, j < a.size ∧ j % 2 = 1 ∧ 2 ∣ a[j]!)
    (done_1 : a.size ≤ i ∨ ok = false)
    (i_2 : i = i_1 ∧ ok = ok_1)
    : postcondition a ok_1 := by
    unfold postcondition
    rcases i_2 with ⟨hi, hok⟩
    constructor
    · intro hok1true
      -- transfer ok_1=true to ok=true
      have hoktrue : ok = true := by
        calc
          ok = ok_1 := hok
          _ = true := hok1true
      -- from done_1, since ok ≠ false, we must have a.size ≤ i
      have hsize_le_i : a.size ≤ i := by
        cases done_1 with
        | inl h => exact h
        | inr hokfalse =>
            exfalso
            exact (ne_false_of_eq_true hoktrue) hokfalse
      -- prove OddIndexElementsOdd a
      unfold OddIndexElementsOdd
      intro k hk_lt hk_mod
      have hk_lt_i : k < i := Nat.lt_of_lt_of_le hk_lt hsize_le_i
      have hmod1 : a[k]! % 2 = 1 :=
        invariant_inv_prefix_ok hoktrue k hk_lt_i hk_lt hk_mod
      -- from %2=1, conclude %2 ≠ 0
      intro hzero
      have : (1 : ℤ) = 0 := by
        calc
          (1 : ℤ) = a[k]! % 2 := by simpa [hmod1]
          _ = 0 := hzero
      exact one_ne_zero this
    · intro hOdd
      -- prove ok_1=true by contradiction
      by_contra hok1ne
      have hok1false : ok_1 = false := by
        cases ok_1 <;> simp at hok1ne ⊢
      have hokfalse : ok = false := by
        -- use ok = ok_1
        calc
          ok = ok_1 := hok
          _ = false := hok1false
      rcases invariant_inv_prefix_bad hokfalse with ⟨j, hj_lt_i, hj_lt_i'⟩
      rcases hj_lt_i' with ⟨hj_lt_size, hj_mod, hj_even⟩
      have hj_odd : a[j]! % 2 ≠ 0 := hOdd j hj_lt_size hj_mod
      have hmod0 : a[j]! % 2 = 0 := by
        -- from 2 ∣ a[j]!, get emod = 0
        simpa using (Int.emod_eq_zero_of_dvd hj_even)
      exact hj_odd hmod0


prove_correct isOddAtIndexOdd by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1 i ok invariant_inv_bounds i_1 ok_1 invariant_inv_prefix_ok invariant_inv_prefix_bad done_1 i_2)
end Proof
