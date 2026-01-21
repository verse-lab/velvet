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
    findFirstOdd: locate the first odd integer in an array.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. We search indices from left to right.
    3. If there exists an index `i` with `i < a.size` and `a[i]!` is odd, we return `some i`.
    4. The returned index must be the smallest (first) index where an odd element occurs.
    5. If no odd element exists in the array, we return `none`.
    6. Arrays are assumed non-null by the language runtime.
    7. For this task, empty arrays are rejected inputs (precondition requires `a.size > 0`).
-/

section Specs
-- Helper: define oddness for integers via modulo.
-- An integer is odd iff it is not divisible by 2.

def isOdd (x : Int) : Prop := x % 2 ≠ 0

def IsOddAt (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ isOdd (a[i]!)

-- `IsFirstOddIndex a i` means `i` is a valid index, `a[i]!` is odd,
-- and there is no earlier index with an odd element.

def IsFirstOddIndex (a : Array Int) (i : Nat) : Prop :=
  (i < a.size) ∧ isOdd (a[i]!) ∧ ∀ j : Nat, j < i → ¬ isOdd (a[j]!)

-- We reject empty arrays as specified in REJECT_INPUTS.

def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition:
-- - If result = none, then no element in the array is odd.
-- - If result = some i, then i is the first index whose element is odd.

def postcondition (a : Array Int) (result : Option Nat) : Prop :=
  match result with
  | none =>
      ∀ i : Nat, i < a.size → ¬ isOdd (a[i]!)
  | some i =>
      IsFirstOddIndex a i
end Specs

section Impl
method findFirstOdd (a : Array Int)
  return (result : Option Nat)
  require precondition a
  ensures postcondition a result
  do
    let mut i : Nat := 0
    let mut ans : Option Nat := none
    let mut found : Bool := false

    while (i < a.size ∧ found = false)
      -- Invariant 1: i stays within array bounds (init 0; only incremented; guard gives i < size)
      -- Init: i=0. Preserved: only incremented by 1 under i < a.size.
      invariant "inv_bounds" i ≤ a.size
      -- Invariant 2: found is exactly whether ans is some.
      -- Needed so postcondition case-split on ans gives corresponding found fact.
      -- Init: found=false, ans=none. Preserved: in odd branch set both; else branch leaves both.
      invariant "inv_found_iff_ans" (found = true ↔ ∃ k : Nat, ans = some k)
      -- Invariant 3: if we have not found an odd yet, then all examined elements [0, i) are not odd.
      -- Init: i=0 vacuous. Preserved: when not found, we only advance i after seeing even at i.
      invariant "inv_prefix_no_odd" (found = false → ∀ j : Nat, j < i → ¬ isOdd (a[j]!))
      -- Invariant 4: if found is true, ans is exactly the first odd index.
      -- Init: vacuous. Preserved: once found becomes true, it stays true and ans stays fixed.
      invariant "inv_found_correct" (found = true → ∃ k : Nat, ans = some k ∧ IsFirstOddIndex a k)
      done_with (i >= a.size ∨ found = true)
    do
      if (a[i]! % 2 != 0) then
        ans := some i
        found := true
      else
        i := i + 1

    return ans
end Impl

section TestCases
-- Test case 1 (from prompt): all even -> none
-- Most important example: validates the "none" branch.
def test1_a : Array Int := #[2, 4, 6, 8]
def test1_Expected : Option Nat := none

-- Test case 2 (from prompt): first element odd -> some 0
-- Most important example: validates smallest index = 0.
def test2_a : Array Int := #[3, 4, 6, 8]
def test2_Expected : Option Nat := some 0

-- Test case 3 (from prompt): odd in middle -> some 2
-- Most important example: validates minimality (earlier evens).
def test3_a : Array Int := #[2, 4, 5, 8]
def test3_Expected : Option Nat := some 2

-- Test case 4 (from prompt): singleton odd

def test4_a : Array Int := #[7]
def test4_Expected : Option Nat := some 0

-- Test case 5 (from prompt): singleton even

def test5_a : Array Int := #[2]
def test5_Expected : Option Nat := none

-- Test case 6 (from prompt): multiple odds, first at 0

def test6_a : Array Int := #[1, 2, 3]
def test6_Expected : Option Nat := some 0

-- Test case 7: first odd appears later among negatives and evens

def test7_a : Array Int := #[-2, -4, -5, 10]
def test7_Expected : Option Nat := some 2

-- Test case 8: includes zero and a negative odd later

def test8_a : Array Int := #[0, 2, 4, -3]
def test8_Expected : Option Nat := some 3

-- Test case 9: longer, multiple odds; first is not last

def test9_a : Array Int := #[6, 8, 10, 11, 13]
def test9_Expected : Option Nat := some 3

-- Recommend to validate: 1, 2, 3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findFirstOdd test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findFirstOdd test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findFirstOdd test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findFirstOdd test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findFirstOdd test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findFirstOdd test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findFirstOdd test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findFirstOdd test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((findFirstOdd test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 169, Column 0
-- Message: unsolved goals
-- a : Array ℤ
-- result : Option ℕ
-- ⊢ Decidable (postcondition a result)
-- Line: prove_postcondition_decidable_for findFirstOdd
-- [ERROR] Line 171, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for findFirstOdd
-- prove_precondition_decidable_for findFirstOdd
-- prove_postcondition_decidable_for findFirstOdd
-- derive_tester_for findFirstOdd
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
--     let res := findFirstOddTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct findFirstOdd by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_prefix_no_odd : found = false → ∀ j < i, ¬isOdd a[j]!)
    (a_1 : i < a.size)
    (a_2 : found = false)
    (if_pos : a[i]! % 2 = 1)
    : IsFirstOddIndex a i := by
    refine And.intro a_1 ?_
    refine And.intro ?_ ?_
    · -- show `isOdd (a[i]!)`
      unfold isOdd
      -- goal: a[i]! % 2 ≠ 0
      -- rewrite using `if_pos`
      simpa [if_pos] using (Int.zero_ne_one).ne'
    · -- show no earlier index is odd
      intro j hj
      have hprefix : ∀ j < i, ¬ isOdd (a[j]!) := invariant_inv_prefix_no_odd a_2
      exact hprefix j hj

theorem goal_1
    (a : Array ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_prefix_no_odd : found = false → ∀ j < i, ¬isOdd a[j]!)
    (if_neg : 2 ∣ a[i]!)
    : found = false → ∀ j < i + 1, ¬isOdd a[j]! := by
    intro hfound
    intro j hj
    have hj' : j < i ∨ j = i := by
      simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_iff_lt_or_eq.mp hj)
    cases hj' with
    | inl hjlt =>
        exact (invariant_inv_prefix_no_odd hfound) j hjlt
    | inr hjeq =>
        -- avoid `subst` (which can clear `i`); rewrite directly
        have hmod : a[i]! % 2 = 0 := by
          simpa using (Int.emod_eq_zero_of_dvd if_neg)
        -- goal is `¬ isOdd a[j]!`
        -- rewrite `j = i`, then use `hmod`
        simpa [isOdd, hjeq, hmod]

theorem goal_2
    (a : Array ℤ)
    (ans : Option ℕ)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_found_iff_ans : found = true ↔ ∃ k, ans = some k)
    (invariant_inv_prefix_no_odd : found = false → ∀ j < i, ¬isOdd a[j]!)
    (invariant_inv_found_correct : found = true → ∃ k, ans = some k ∧ IsFirstOddIndex a k)
    (i_1 : Option ℕ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (done_1 : a.size ≤ i ∨ found = true)
    (i_4 : ans = i_1 ∧ found = i_2 ∧ i = i_3)
    : postcondition a i_1 := by
    rcases i_4 with ⟨hans, hfound, hi⟩
    -- rewrite the output in terms of `ans`
    subst hans
    -- now prove `postcondition a ans`
    cases ans with
    | none =>
        -- need: ∀ t < a.size, ¬ isOdd a[t]!
        intro t ht
        have hnotExists : ¬ ∃ k, (none : Option Nat) = some k := by
          simp
        have hneTrue : found ≠ true := by
          intro hft
          have hex : ∃ k, (none : Option Nat) = some k :=
            (invariant_inv_found_iff_ans.mp hft)
          exact hnotExists hex
        have hfalse : found = false := by
          exact eq_false_of_ne_true hneTrue
        have hprefix : ∀ j < i, ¬ isOdd a[j]! := invariant_inv_prefix_no_odd hfalse
        have hsle : a.size ≤ i := by
          cases done_1 with
          | inl hsle => exact hsle
          | inr hft =>
              have hex : ∃ k, (none : Option Nat) = some k :=
                (invariant_inv_found_iff_ans.mp hft)
              exact (hnotExists hex).elim
        have hti : t < i := Nat.lt_of_lt_of_le ht hsle
        exact hprefix t hti
    | some k =>
        -- need: IsFirstOddIndex a k
        have hex : ∃ k', (some k : Option Nat) = some k' := by
          exact ⟨k, rfl⟩
        have hft : found = true := invariant_inv_found_iff_ans.mpr hex
        have hcorr : ∃ k', (some k : Option Nat) = some k' ∧ IsFirstOddIndex a k' :=
          invariant_inv_found_correct hft
        rcases hcorr with ⟨k', hk', hfirst⟩
        have hkEq : k' = k := by
          have : k = k' := Option.some.inj hk'
          exact this.symm
        simpa [hkEq] using hfirst


prove_correct findFirstOdd by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a found i invariant_inv_prefix_no_odd a_1 a_2 if_pos)
  exact (goal_1 a found i invariant_inv_prefix_no_odd if_neg)
  exact (goal_2 a ans found i invariant_inv_found_iff_ans invariant_inv_prefix_no_odd invariant_inv_found_correct i_1 i_2 i_3 done_1 i_4)
end Proof
