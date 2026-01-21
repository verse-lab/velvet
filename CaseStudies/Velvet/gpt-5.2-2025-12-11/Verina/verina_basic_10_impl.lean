import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isGreater: determine if an integer is strictly greater than every element in an array
    Natural language breakdown:
    1. Inputs are an integer n and an array a of integers.
    2. The method returns a Boolean.
    3. The result is true exactly when n is strictly greater than every element in a.
    4. The result is false when there exists at least one element x in a with x ≥ n.
    5. Empty arrays are rejected (see reject input).
-/

section Specs
-- Preconditions: reject empty arrays.
def precondition (n : Int) (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: Boolean meaning of being strictly greater than every element.
-- We specify using index-wise comparison over the array.
def postcondition (n : Int) (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n))
end Specs

section Impl
method isGreater (n : Int) (a : Array Int)
  return (result : Bool)
  require precondition n a
  ensures postcondition n a result
  do
    let mut ok := true
    let mut i : Nat := 0
    while i < a.size
      -- Invariant 1 (bounds): i stays within the array bounds, so a[i]! is safe when the guard holds.
      -- Init: i=0 so 0 ≤ i ≤ a.size. Preserved: i increases by 1 but loop guard ensures i < a.size.
      invariant "inv_bounds" (0 ≤ i ∧ i ≤ a.size)
      -- Invariant 2 (meaning of ok): ok is true iff all elements seen so far are < n.
      -- Init: i=0, the range is empty so the ∀ is true, hence ok=true matches. Preserved: each step updates ok
      -- to false exactly when encountering a counterexample at index i.
      invariant "inv_ok_prefix" (ok = true ↔ (∀ j : Nat, j < i → a[j]! < n))
    do
      if a[i]! < n then
        ok := ok
      else
        ok := false
      i := i + 1
    return ok
end Impl

section TestCases
-- Test case 1: example provided (n larger than all elements)
def test1_n : Int := 6
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: n is not larger than all elements (some elements ≥ n)
def test2_n : Int := 3
def test2_a : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Bool := false

-- Test case 3: equal elements, strictness matters
def test3_n : Int := 5
def test3_a : Array Int := #[5, 5, 5]
def test3_Expected : Bool := false

-- Test case 4: negatives, true case
def test4_n : Int := -1
def test4_a : Array Int := #[-10, -5, -3]
def test4_Expected : Bool := true

-- Test case 5: negatives, false due to element ≥ n
def test5_n : Int := -3
def test5_a : Array Int := #[-1, -2, -3]
def test5_Expected : Bool := false

-- Test case 6: includes 0, strictness against 0
def test6_n : Int := 0
def test6_a : Array Int := #[0, -1, -2]
def test6_Expected : Bool := false

-- Test case 7: unsorted array, true case
def test7_n : Int := 10
def test7_a : Array Int := #[1, 2, 9, 3]
def test7_Expected : Bool := true

-- Test case 8: single-element array, true
def test8_n : Int := 2
def test8_a : Array Int := #[1]
def test8_Expected : Bool := true

-- Test case 9: single-element array, false (equal)
def test9_n : Int := 1
def test9_a : Array Int := #[1]
def test9_Expected : Bool := false

-- Recommend to validate: test1, test2, test3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isGreater test1_n test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isGreater test2_n test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isGreater test3_n test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isGreater test4_n test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isGreater test5_n test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isGreater test6_n test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isGreater test7_n test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isGreater test8_n test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isGreater test9_n test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for isGreater
prove_precondition_decidable_for isGreater
prove_postcondition_decidable_for isGreater
derive_tester_for isGreater
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := isGreaterTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isGreater by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (n : ℤ)
    (a : Array ℤ)
    (require_1 : precondition n a)
    (i : ℕ)
    (ok : Bool)
    (a_2 : i ≤ a.size)
    (invariant_inv_ok_prefix : ok = true ↔ ∀ j < i, a[j]! < n)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (a_1 : True)
    (done_1 : a.size ≤ i)
    (i_2 : i = i_1 ∧ ok = ok_1) : postcondition n a ok_1 := by
  unfold postcondition
  -- use ok = ok_1
  have hok : ok = ok_1 := i_2.2
  constructor
  · intro hok1true
    have hoktrue : ok = true := by simpa [hok] using hok1true
    have hprefix : ∀ j < i, a[j]! < n := (invariant_inv_ok_prefix.mp hoktrue)
    intro k hk
    have hki : k < i := Nat.lt_of_lt_of_le hk done_1
    exact hprefix k hki
  · intro hall
    have hprefix : ∀ j < i, a[j]! < n := by
      intro j hj
      have hjsize : j < a.size := Nat.lt_of_lt_of_le hj a_2
      exact hall j hjsize
    have hoktrue : ok = true := invariant_inv_ok_prefix.mpr hprefix
    -- convert back to ok_1 = true
    simpa [hok] using hoktrue


prove_correct isGreater by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
